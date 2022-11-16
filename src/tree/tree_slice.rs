use std::ops::Range;
use std::sync::Arc;

use super::{Chops, Leaf, Leaves, Metric, Node, Summarize};

// TODO: consider making this either Sliced<slice> or Inode<inode>, there's no
// use in keeping whole leafs.
/// TODO: docs
#[derive(Debug, Copy)]
pub(super) enum NodeOrSlicedLeaf<'a, const N: usize, L: Leaf> {
    /// No slicing was needed so we can reuse a reference to the original node.
    Whole(&'a Node<N, L>),

    /// We had to slice a leaf, getting an owned value.
    Sliced(&'a L::Slice, L::Summary),
}

// FIXME: Why can't I derive this?
impl<'a, const N: usize, L: Leaf> Clone for NodeOrSlicedLeaf<'a, N, L> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Self::Whole(node) => Self::Whole(*node),

            Self::Sliced(slice, summary) => {
                Self::Sliced(*slice, summary.clone())
            },
        }
    }
}

impl<'a, const N: usize, L: Leaf> NodeOrSlicedLeaf<'a, N, L> {
    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        match self {
            Self::Whole(node) => node.summary(),
            Self::Sliced(_slice, summary) => &summary,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    slice: SliceType<'a, FANOUT, L>,
    summary: L::Summary,
}

#[derive(Debug)]
enum SliceType<'a, const FANOUT: usize, L: Leaf> {
    Empty,

    Single(&'a L::Slice),

    Multi {
        start: (&'a L::Slice, L::Summary),
        internals: Vec<Arc<Node<FANOUT, L>>>,
        // internals: Vec<&'a Inode<FANOUT, L>>,
        end: (&'a L::Slice, L::Summary),
    },
}

impl<'a, const FANOUT: usize, L: Leaf> Clone for SliceType<'a, FANOUT, L> {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> TreeSlice<'a, FANOUT, L> {
    /// TODO: docs
    #[inline]
    pub fn chops<M: Metric<L>>(&'a self) -> Chops<'a, FANOUT, L, M> {
        let mut chops = Chops::new();
        match &self.slice {
            SliceType::Empty => {},

            SliceType::Single(slice) => {
                chops.append(NodeOrSlicedLeaf::Sliced(
                    *slice,
                    self.summary.clone(),
                ));
            },

            SliceType::Multi { start, internals, end } => {
                let (start, start_summary) = start;
                chops.append(NodeOrSlicedLeaf::Sliced(
                    *start,
                    start_summary.clone(),
                ));

                chops.extend(
                    internals.iter().map(|n| NodeOrSlicedLeaf::Whole(n)),
                );

                let (end, end_summary) = end;
                chops.append(NodeOrSlicedLeaf::Sliced(
                    *end,
                    end_summary.clone(),
                ));
            },
        }
        chops
    }

    pub(super) fn empty() -> Self {
        Self { slice: SliceType::Empty, summary: L::Summary::default() }
    }

    pub(super) fn from_range_in_node<M>(
        node: &'a Node<FANOUT, L>,
        range: Range<M>,
    ) -> Self
    where
        M: Metric<L>,
    {
        match node {
            Node::Leaf(leaf) => {
                let slice = M::slice(leaf.value().borrow(), range);
                Self {
                    slice: SliceType::Single(slice),
                    summary: slice.summarize(),
                }
            },

            Node::Internal(inode) => {
                // println!("splicing node {inode:#?}");
                let mut slice = None;
                let mut summary = L::Summary::default();
                let mut v = Vec::new();
                sumzyng(
                    inode.children(),
                    range,
                    &mut M::zero(),
                    &mut slice,
                    &mut (v.as_mut_ptr(), v.len(), v.capacity()),
                    &mut None,
                    &mut summary,
                    &mut false,
                    &mut false,
                );
                Self { slice: slice.unwrap(), summary }
            },
        }
    }

    /// TODO: docs
    #[inline]
    pub fn leaves(&'a self) -> Leaves<'a, FANOUT, L> {
        let mut leaves = Leaves::new();
        match &self.slice {
            SliceType::Empty => {},

            SliceType::Single(slice) => {
                leaves.append(NodeOrSlicedLeaf::Sliced(
                    *slice,
                    self.summary.clone(),
                ));
            },

            SliceType::Multi { start, internals, end } => {
                let (start, start_summary) = start;
                leaves.append(NodeOrSlicedLeaf::Sliced(
                    *start,
                    start_summary.clone(),
                ));

                leaves.extend(
                    internals.iter().map(|n| NodeOrSlicedLeaf::Whole(n)),
                );

                let (end, end_summary) = end;
                leaves.append(NodeOrSlicedLeaf::Sliced(
                    *end,
                    end_summary.clone(),
                ));
            },
        }
        leaves
    }

    /// TODO: docs
    #[inline]
    pub fn slice<M>(&'a self, range: Range<M>) -> TreeSlice<'a, FANOUT, L>
    where
        M: Metric<L>,
    {
        assert!(M::zero() <= range.start);
        assert!(range.start <= range.end);
        assert!(range.end <= M::measure(self.summary()));

        if range.start == range.end {
            Self::empty()
        } else {
            match &self.slice {
                SliceType::Empty => panic!("TODO: explain why"),

                SliceType::Single(slice) => {
                    let sliced = M::slice(slice, range);

                    Self {
                        summary: sliced.summarize(),
                        slice: SliceType::Single(sliced),
                    }
                },

                SliceType::Multi {
                    start: (a, ref b),
                    ref internals,
                    end: (c, ref d),
                } => {
                    // println!("=======================");
                    // println!("slicing {self:#?}");
                    let (slice, summary) =
                        sumzung((*a, b), internals, (*c, d), range);

                    Self { slice, summary }
                },
            }
        }
    }

    /// TODO: docs
    pub fn summary(&self) -> &L::Summary {
        &self.summary
    }
}

fn sumzung<'a, const N: usize, L: Leaf, M: Metric<L>>(
    start: (&'a L::Slice, &L::Summary),
    internals: &'a [Arc<Node<N, L>>],
    end: (&'a L::Slice, &L::Summary),
    range: Range<M>,
) -> (SliceType<'a, N, L>, L::Summary) {
    let (mut start, mut measured, mut summary) = {
        let (slice, summary) = start;
        let size = M::measure(summary);
        if size > range.start {
            if size >= range.end {
                // The whole range is contained in the starting slice.
                let sliced = M::slice(slice, range);
                return (SliceType::Single(sliced), sliced.summarize());
            } else {
                // The starting slice contains the start of the range but
                // not the end.
                let (_, slice) = M::split_right(slice, range.start);
                let summary = slice.summarize();
                let size = M::measure(&summary);
                (Some((slice, summary.clone())), size, summary)
            }
        } else {
            // The starting slice is not contained in the range.
            (None, M::zero(), L::Summary::default())
        }
    };

    let mut slice = None;

    let mut found_start = start.is_some();

    let mut found_end = false;

    let mut new_internals = Vec::new();

    sumzyng(
        internals,
        Range { start: range.start, end: range.end },
        &mut measured,
        &mut slice,
        &mut (
            new_internals.as_mut_ptr(),
            new_internals.len(),
            new_internals.capacity(),
        ),
        &mut start,
        &mut summary,
        &mut found_start,
        &mut found_end,
    );

    if found_end {
        (slice.unwrap(), summary)
    } else {
        let (end, end_summary) = end;
        let (end, end_summary, _) =
            M::split_left(end, range.end - measured, end_summary);
        summary += &end_summary;
        (
            SliceType::Multi {
                start: start.take().unwrap(),
                internals: new_internals,
                end: (end, end_summary),
            },
            summary,
        )
    }
}

fn sumzyng<'a, const N: usize, L, M>(
    nodes: &'a [Arc<Node<N, L>>],
    range: Range<M>,
    measured: &mut M,
    ty: &mut Option<SliceType<'a, N, L>>,
    internals: &mut (*mut Arc<Node<N, L>>, usize, usize),
    start: &mut Option<(&'a L::Slice, L::Summary)>,
    summary: &mut L::Summary,
    found_start: &mut bool,
    found_end: &mut bool,
) where
    L: Leaf,
    M: Metric<L>,
{
    // eprintln!("====================");
    // eprintln!("calling sumzyng w/ start: {start:#?}");
    // eprintln!("calling sumzyng w/ internals: {internals:#?}");
    // eprintln!("calling sumzyng w/ measured: {measured:?}");
    // eprintln!("calling sumzyng w/ i: {i:#?}");

    for node in nodes.into_iter() {
        // Once we've found the end leaf there's nothing left to do.
        if *found_end {
            return;
        }

        match &**node {
            Node::Internal(inode) => {
                let size = M::measure(inode.summary());

                // We're still looking for the start leaf.
                if !*found_start {
                    if *measured + size > range.start {
                        sumzyng(
                            inode.children(),
                            Range { start: range.start, end: range.end },
                            measured,
                            ty,
                            internals,
                            start,
                            summary,
                            found_start,
                            found_end,
                        );
                    } else {
                        *measured += size;
                    }
                }
                // We've found the start but we haven't found the end leaf.
                else {
                    if *measured + size >= range.end {
                        sumzyng(
                            inode.children(),
                            Range { start: range.start, end: range.end },
                            measured,
                            ty,
                            internals,
                            start,
                            summary,
                            found_start,
                            found_end,
                        );
                    } else {
                        let (ptr, vec, cap) = internals;
                        let mut int =
                            unsafe { Vec::from_raw_parts(*ptr, *vec, *cap) };
                        *summary += inode.summary();
                        int.push(Arc::clone(node));
                        *internals =
                            (int.as_mut_ptr(), int.len(), int.capacity());
                        std::mem::forget(int);
                        *measured += size;
                    }
                }
            },

            Node::Leaf(leaf) => {
                // println!("arrived to leaf {leaf:#?} at iter {i}");

                let leaf_summary = leaf.summary();
                let leaf = leaf.value().borrow();
                let size = M::measure(leaf_summary);

                if *found_start {
                    // The start of the range is already set.
                    if *measured + size >= range.end {
                        // This is the end of the range.
                        let (end, end_summary, _) = M::split_left(
                            leaf,
                            range.end - *measured,
                            leaf_summary,
                        );
                        *summary += &end_summary;
                        let (ptr, vec, cap) = internals;
                        let int =
                            unsafe { Vec::from_raw_parts(*ptr, *vec, *cap) };
                        *ty = Some(SliceType::Multi {
                            start: start.take().unwrap(),
                            internals: int, // TODO: dont clone
                            end: (end, end_summary),
                        });
                        *found_end = true;
                        return;
                    } else {
                        *summary += leaf_summary;
                        let (ptr, vec, cap) = internals;
                        let mut int =
                            unsafe { Vec::from_raw_parts(*ptr, *vec, *cap) };
                        int.push(Arc::clone(node));
                        *internals =
                            (int.as_mut_ptr(), int.len(), int.capacity());
                        *measured += size;
                        std::mem::forget(int);
                        continue;
                    }
                }

                if *measured + size > range.start {
                    let start_m = range.start - *measured;
                    let end = range.end - *measured;
                    // The start is not set so this is the start.
                    if end <= size {
                        // If the end of the range also fits in this slice this
                        // is also the end and we have a single type.
                        let slice = M::slice(leaf, start_m..end);
                        let slice_summary = slice.summarize();
                        *ty = Some(SliceType::Single(slice));
                        *summary = slice_summary.clone();
                        *found_end = true;
                    } else {
                        // println!("HEYO??, {}, {:?}", *i, start_m);
                        // The end of the range does not fit in this slice.
                        let (_, star) = M::split_right(leaf, start_m);
                        let start_summary = star.summarize();
                        *measured += M::measure(&leaf_summary);
                        *start = Some((star, start_summary.clone()));
                        *summary = start_summary;
                        *found_start = true;
                    }
                } else {
                    *measured += size;
                }
            },
        }
    }
}
