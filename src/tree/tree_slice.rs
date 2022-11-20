use std::ops::Range;
use std::sync::Arc;

use super::{Inode, Leaf, Leaves, Metric, Node, Summarize, Units};

/// TODO: docs
#[derive(Debug, Clone)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    pub(super) span: SliceSpan<'a, FANOUT, L>,
    pub(super) summary: L::Summary,
}

#[derive(Debug)]
pub(super) enum SliceSpan<'a, const N: usize, L: Leaf> {
    /// The slice is fully contained within a single leaf of the tree.
    Single(&'a L::Slice),

    /// The slice spans multiple leaves. In this case we store:
    ///
    /// - `start`: the leaf slice where this span starts together with its
    /// summary;
    ///
    /// - `internals`: a vector of tree nodes that are fully contained in the
    /// span. These nodes can have different depths and their order reflects
    /// the logical order of the slice, i.e. the first internal is the node
    /// right after `start` and the last is the one before `end`. This vector
    /// can be empty if the slice spans two consecutive leaves with no other
    /// node between them;
    ///
    /// - `end`: the leaf slice where this span ends together with its summary.
    Multi {
        start: (&'a L::Slice, L::Summary),
        internals: Vec<Arc<Node<N, L>>>,
        end: (&'a L::Slice, L::Summary),
    },

    /// The slice is empty.
    Empty,
}

impl<'a, const N: usize, L: Leaf> Clone for SliceSpan<'a, N, L> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            SliceSpan::Single(slice) => SliceSpan::Single(*slice),

            SliceSpan::Multi { start, internals, end } => SliceSpan::Multi {
                start: (start.0, start.1.clone()),
                internals: internals.clone(),
                end: (end.0, end.1.clone()),
            },

            SliceSpan::Empty => SliceSpan::Empty,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> TreeSlice<'a, FANOUT, L> {
    pub(super) fn empty() -> Self {
        Self { span: SliceSpan::Empty, summary: L::Summary::default() }
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
                    span: SliceSpan::Single(slice),
                    summary: slice.summarize(),
                }
            },

            Node::Internal(inode) => {
                tree_slice_from_range_in_inode(inode, range)
            },
        }
    }

    /// TODO: docs
    #[inline]
    pub fn leaves(&'a self) -> Leaves<'a, FANOUT, L> {
        Leaves::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn slice<M>(&'a self, range: Range<M>) -> TreeSlice<'a, FANOUT, L>
    where
        M: Metric<L>,
    {
        assert!(M::zero() <= range.start);
        assert!(range.start <= range.end);

        // TODO: this doesn't work for the line metric, e.g. we should be able
        // to slice a string w/ no newlines in the 0..1 range but its measure
        // is 0.
        assert!(range.end <= M::measure(self.summary()));

        if range.start == range.end {
            Self::empty()
        } else {
            match &self.span {
                SliceSpan::Empty => panic!("TODO: explain why"),

                SliceSpan::Single(slice) => {
                    let sliced = M::slice(slice, range);

                    Self {
                        summary: sliced.summarize(),
                        span: SliceSpan::Single(sliced),
                    }
                },

                SliceSpan::Multi { start, internals, end } => {
                    let (start_slice, start_summary) = start;
                    let (end_slice, end_summary) = end;
                    tree_slice_from_range_in_multi_span(
                        *start_slice,
                        start_summary,
                        internals,
                        *end_slice,
                        end_summary,
                        range,
                    )
                },
            }
        }
    }

    /// TODO: docs
    #[inline]
    pub fn summary(&self) -> &L::Summary {
        &self.summary
    }

    /// TODO: docs
    #[inline]
    pub fn units<M>(&'a self) -> Units<'a, FANOUT, L, M>
    where
        M: Metric<L>,
    {
        Units::from(self)
    }
}

fn tree_slice_from_range_in_inode<'a, const N: usize, L, M>(
    inode: &'a Inode<N, L>,
    range: Range<M>,
) -> TreeSlice<'a, N, L>
where
    L: Leaf,
    M: Metric<L>,
{
    let mut summary = L::Summary::default();
    let mut span = None;
    some_name_for_this_rec(
        inode.children(),
        range,
        &mut M::zero(),
        &mut None,
        &mut StackVec::new(),
        &mut span,
        &mut summary,
        &mut false,
    );
    TreeSlice { span: span.unwrap(), summary }
}

fn tree_slice_from_range_in_multi_span<'a, const N: usize, L, M>(
    start_slice: &'a L::Slice,
    start_summary: &L::Summary,
    internals: &'a [Arc<Node<N, L>>],
    end_slice: &'a L::Slice,
    end_summary: &L::Summary,
    range: Range<M>,
) -> TreeSlice<'a, N, L>
where
    L: Leaf,
    M: Metric<L>,
{
    let mut start = {
        let start_size = M::measure(start_summary);
        if start_size > range.start {
            // The starting slice contains the start of the range.
            if start_size >= range.end {
                // The starting slice also contains the end of the range.
                let slice = M::slice(start_slice, range);
                let summary = slice.summarize();
                return TreeSlice { span: SliceSpan::Single(slice), summary };
            } else {
                let (_, start_slice, start_summary) =
                    M::split_right(start_slice, range.start, start_summary);
                Some((start_slice, start_summary))
            }
        } else {
            // The starting slice is not contained in the range.
            None
        }
    };

    let (mut measured, mut summary) = start
        .as_ref()
        .map(|(_, summary)| (M::measure(summary), summary.clone()))
        .unwrap_or((M::zero(), L::Summary::default()));

    let mut span = None;

    let mut new_internals = StackVec::new();

    some_name_for_this_rec(
        internals,
        Range { start: range.start, end: range.end },
        &mut measured,
        &mut start,
        &mut new_internals,
        &mut span,
        &mut summary,
        &mut false,
    );

    if let Some(span) = span {
        TreeSlice { span, summary }
    } else {
        let (start_slice, start_summary) = start.unwrap();

        let (end_slice, end_summary, _) =
            M::split_left(end_slice, range.end - measured, end_summary);

        summary += &end_summary;

        TreeSlice {
            span: SliceSpan::Multi {
                start: (start_slice, start_summary),
                internals: unsafe { new_internals.into_vec() },
                end: (end_slice, end_summary),
            },
            summary,
        }
    }
}

fn some_name_for_this_rec<'a, const N: usize, L, M>(
    nodes: &'a [Arc<Node<N, L>>],
    range: Range<M>,
    measured: &mut M,
    start_slice: &mut Option<(&'a L::Slice, L::Summary)>,
    internals: &mut StackVec<Arc<Node<N, L>>>,
    final_span: &mut Option<SliceSpan<'a, N, L>>,
    final_summary: &mut L::Summary,
    span_is_some: &mut bool,
) where
    L: Leaf,
    M: Metric<L>,
{
    for node in nodes {
        // If the end of the slice has been found and the final span has been
        // set there's nothing left to do.
        if *span_is_some {
            return;
        }

        match &**node {
            Node::Internal(inode) => {
                let measure = M::measure(inode.summary());

                if start_slice.is_none() {
                    // We're still looking for the leaf where the final span
                    // starts.
                    if *measured + measure > range.start {
                        // This inode contains the starting leaf somewhere in
                        // its subtree. Run this function again looping over
                        // the inode's children.
                        some_name_for_this_rec(
                            inode.children(),
                            Range { start: range.start, end: range.end },
                            measured,
                            start_slice,
                            internals,
                            final_span,
                            final_summary,
                            span_is_some,
                        );
                    } else {
                        // This inode comes before the starting leaf.
                        *measured += measure;
                    }
                } else {
                    // We've found the starting slice and now we're looking for
                    // the leaf containing the end of the range.
                    if *measured + measure >= range.end {
                        // This inode contains the ending leaf somewhere in its
                        // subtree. Run this function again looping over the
                        // inode's children.
                        some_name_for_this_rec(
                            inode.children(),
                            Range { start: range.start, end: range.end },
                            measured,
                            start_slice,
                            internals,
                            final_span,
                            final_summary,
                            span_is_some,
                        );
                    } else {
                        // This inode is fully contained in the final span. Add
                        // the inode to the internals and update the final
                        // summary.
                        unsafe { internals.push(Arc::clone(node)) };
                        *final_summary += inode.summary();
                        *measured += measure;
                    }
                }
            },

            Node::Leaf(leaf) => {
                let measure = M::measure(leaf.summary());

                if start_slice.is_none() {
                    if *measured + measure > range.start {
                        // This leaf is the starting one.
                        if measure >= range.end - *measured {
                            // The end of the range is also contained in this
                            // leaf so the final slice only spans this single
                            // leaf.
                            let slice = M::slice(
                                leaf.value().borrow(),
                                range.start - *measured..range.end - *measured,
                            );
                            let slice_summary = slice.summarize();
                            *final_span = Some(SliceSpan::Single(slice));
                            *final_summary = slice_summary;
                            *span_is_some = true;
                            return;
                        } else {
                            let (_, start, start_summary) = M::split_right(
                                leaf.value().borrow(),
                                range.start - *measured,
                                leaf.summary(),
                            );
                            *measured += M::measure(leaf.summary());
                            *final_summary = start_summary.clone();
                            *start_slice = Some((start, start_summary));
                        }
                    } else {
                        *measured += measure;
                    }
                } else {
                    if *measured + measure >= range.end {
                        // This leaf is the ending one.
                        let (end_slice, end_summary, _) = M::split_left(
                            leaf.value().borrow(),
                            range.end - *measured,
                            leaf.summary(),
                        );
                        *final_summary += &end_summary;
                        *final_span = Some(SliceSpan::Multi {
                            start: start_slice.take().unwrap(),
                            internals: unsafe { internals.into_vec() },
                            end: (end_slice, end_summary),
                        });
                        *span_is_some = true;
                        return;
                    } else {
                        unsafe { internals.push(Arc::clone(node)) };
                        *final_summary += leaf.summary();
                        *measured += measure;
                    }
                }
            },
        }
    }
}

struct StackVec<T> {
    ptr: *mut T,
    len: usize,
    capacity: usize,
}

impl<T> Clone for StackVec<T> {
    fn clone(&self) -> Self {
        Self { ptr: self.ptr, len: self.len, capacity: self.capacity }
    }
}

impl<T> Copy for StackVec<T> {}

impl<T> StackVec<T> {
    fn new() -> Self {
        let mut vec = Vec::new();
        let stack = Self {
            ptr: vec.as_mut_ptr(),
            len: vec.len(),
            capacity: vec.capacity(),
        };
        std::mem::forget(vec);
        stack
    }

    unsafe fn push(&mut self, value: T) {
        let mut vec = Vec::from_raw_parts(self.ptr, self.len, self.capacity);
        vec.push(value);
        self.ptr = vec.as_mut_ptr();
        self.len = vec.len();
        self.capacity = vec.capacity();
        std::mem::forget(vec);
    }

    unsafe fn into_vec(self) -> Vec<T> {
        Vec::from_raw_parts(self.ptr, self.len, self.capacity)
    }
}
