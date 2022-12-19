use std::ops::Range;
use std::sync::Arc;

use super::{Leaf, Leaves, Metric, Node, Units};

#[derive(Debug)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    /// TODO: docs
    pub(super) root: &'a Arc<Node<FANOUT, L>>,

    /// The summary between the left-most leaf of the root and the start of the
    /// slice.
    pub(super) before: L::Summary,

    /// The total summary of this slice.
    ///
    /// It's always true that `before + summary + after = root.summary()`.
    pub(super) summary: L::Summary,

    /// The summary between the right-most leaf of the root and the end of the
    /// slice.
    pub(super) after: L::Summary,

    /// TODO: docs
    pub(super) start_slice: &'a L::Slice,

    /// TODO: docs
    pub(super) start_summary: L::Summary,

    /// TODO: docs
    pub(super) end_slice: &'a L::Slice,

    /// TODO: docs
    pub(super) end_summary: L::Summary,

    /// The number of leaves included in this slice (including the start and
    /// end slices). Used by the [`Leaves`] iterator.
    pub(super) num_leaves: usize,
}

// #[derive(Debug)]
// pub struct TreeSlicer<'a, const FANOUT: usize, L: Leaf> {
//     span: SliceSpan<'a, FANOUT, L>,
//     summary: L::Summary,
// }

// #[derive(Debug)]
// enum SliceSpan<'a, const N: usize, L: Leaf> {
//     Single(&'a L::Slice),

//     Multi {
//         root: &'a Arc<Node<N, L>>,

//         start_slice: &'a L::Slice,
//         start_summary: L::Summary,
//         offset_of_start: L::Summary,

//         end_slice: &'a L::Slice,
//         end_summary: L::Summary,
//         offset_of_end: L::Summary,

//         num_leaves: usize,
//     },
// }

impl<'a, const FANOUT: usize, L: Leaf> Clone for TreeSlice<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        TreeSlice {
            before: self.before.clone(),
            summary: self.summary.clone(),
            after: self.after.clone(),
            start_summary: self.start_summary.clone(),
            end_summary: self.end_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Copy for TreeSlice<'a, FANOUT, L> where
    L::Summary: Copy
{
}

impl<'a, const FANOUT: usize, L: Leaf> TreeSlice<'a, FANOUT, L> {
    /// TODO: docs
    #[inline]
    pub fn leaves(&'a self) -> Leaves<'a, FANOUT, L> {
        Leaves::from(self)
    }

    /// Returns .
    #[inline]
    pub fn num_leaves(&'a self) -> usize {
        self.num_leaves
    }

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

impl<'a, const FANOUT: usize, L: Leaf> TreeSlice<'a, FANOUT, L>
where
    for<'d> &'d L::Slice: Default,
{
    /// Note: doesn't do bounds checks.
    #[inline]
    pub(super) fn from_range_in_root<M>(
        root: &'a Arc<Node<FANOUT, L>>,
        range: Range<M>,
    ) -> Self
    where
        M: Metric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        // debug_assert!(range.end <= M::measure(self.summary()));

        let (root, range) = deepest_node_containing_range(root, range);

        // TODO: consider using `MaybeUninit` instead of adding a `Default`
        // bound on L::Slice.
        let mut tree_slice = Self {
            root,
            before: L::Summary::default(),
            summary: L::Summary::default(),
            after: root.summary().clone(),
            start_slice: Default::default(),
            start_summary: L::Summary::default(),
            end_slice: Default::default(),
            end_summary: L::Summary::default(),
            num_leaves: 0,
        };

        tree_slice_from_range_in_root_rec(
            root,
            range,
            &mut M::zero(),
            &mut tree_slice,
            &mut false,
            &mut false,
        );

        tree_slice
    }

    /// Note: doesn't do bounds checks.
    #[inline]
    pub fn slice<M>(&'a self, mut range: Range<M>) -> TreeSlice<'a, FANOUT, L>
    where
        M: Metric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        // debug_assert!(range.end <= M::measure(self.summary()));

        let before = M::measure(&self.before);
        range.start += before;
        range.end += before;

        Self::from_range_in_root(self.root, range)
    }
}

#[inline]
fn deepest_node_containing_range<'a, const N: usize, L: Leaf, M: Metric<L>>(
    mut node: &'a Arc<Node<N, L>>,
    mut range: Range<M>,
) -> (&'a Arc<Node<N, L>>, Range<M>) {
    'outer: loop {
        match &**node {
            Node::Internal(inode) => {
                let mut measured = M::zero();

                for child in inode.children() {
                    let this = M::measure(child.summary());
                    if measured <= range.start && measured + this >= range.end
                    {
                        node = child;
                        range.start -= measured;
                        range.end -= measured;
                        continue 'outer;
                    }
                    measured += this;
                }

                // If no child of this internal node fully contains the range
                // then this node is the deepest one fully containing the
                // range.
                break (node, range);
            },

            Node::Leaf(_) => break (node, range),
        }
    }
}

#[inline]
fn tree_slice_from_range_in_root_rec<'a, const N: usize, L, M>(
    node: &'a Arc<Node<N, L>>,
    range: Range<M>,
    measured: &mut M,
    slice: &mut TreeSlice<'a, N, L>,
    found_start: &mut bool,
    done: &mut bool,
) where
    L: Leaf,
    M: Metric<L>,
{
    match &**node {
        Node::Internal(inode) => {
            for child in inode.children() {
                // If the slice has been completed there's nothing left to do,
                // simply unwind the call stack.
                if *done {
                    return;
                }

                let measure = M::measure(child.summary());

                if !*found_start {
                    if *measured + measure > range.start {
                        // This child contains the starting slice somewhere in
                        // its subtree. Run this function again with this child
                        // as the node.
                        tree_slice_from_range_in_root_rec(
                            child,
                            Range { start: range.start, end: range.end },
                            measured,
                            slice,
                            found_start,
                            done,
                        )
                    } else {
                        // This child comes before the starting leaf.
                        slice.before += child.summary();
                        slice.after -= child.summary();
                        *measured += measure;
                    }
                } else if *measured + measure >= range.end {
                    // This child contains the ending leaf somewhere in its
                    // subtree. Run this function again with this child as the
                    // node.
                    tree_slice_from_range_in_root_rec(
                        child,
                        Range { start: range.start, end: range.end },
                        measured,
                        slice,
                        found_start,
                        done,
                    )
                } else {
                    // This is a node fully contained between the starting and
                    // the ending slices.
                    slice.summary += child.summary();
                    slice.after -= child.summary();
                    slice.num_leaves += child.num_leaves();
                    *measured += measure;
                }
            }
        },

        Node::Leaf(leaf) => {
            let measure = M::measure(leaf.summary());

            if !*found_start {
                if *measured + measure > range.start {
                    if measure >= range.end - *measured {
                        // The end of the range is also contained in this leaf
                        // so the final slice only spans this single leaf.

                        let (_, left_summary, right_slice, right_summary) =
                            M::split(
                                leaf.as_slice(),
                                range.start - *measured,
                                leaf.summary(),
                            );

                        slice.before += &left_summary;
                        slice.after -= &left_summary;

                        let (start_slice, start_summary, _, _) = M::split(
                            right_slice,
                            range.end - *measured - M::measure(&left_summary),
                            &right_summary,
                        );

                        slice.summary = start_summary.clone();
                        slice.after -= &start_summary;
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.num_leaves = 1;
                        *done = true;
                    } else {
                        // This leaf contains the starting slice but not the
                        // ending one.
                        let (_, before_summary, start_slice, start_summary) =
                            M::split(
                                leaf.as_slice(),
                                range.start - *measured,
                                leaf.summary(),
                            );
                        *measured += measure;
                        slice.before += &before_summary;
                        slice.summary = start_summary.clone();
                        slice.after -= leaf.summary();
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.num_leaves = 1;
                        *found_start = true;
                    }
                } else {
                    // This leaf comes before the starting leaf.
                    slice.before += leaf.summary();
                    slice.after -= leaf.summary();
                    *measured += measure;
                }
            } else if *measured + measure >= range.end {
                // This leaf contains the ending slice.
                let (end_slice, end_summary, _, _) = M::split(
                    leaf.as_slice(),
                    range.end - *measured,
                    leaf.summary(),
                );
                slice.summary += &end_summary;
                slice.after -= &end_summary;
                slice.end_slice = end_slice;
                slice.end_summary = end_summary;
                slice.num_leaves += 1;
                *done = true;
            } else {
                // This is a leaf between the starting and the ending slices.
                slice.summary += leaf.summary();
                slice.num_leaves += 1;
                *measured += measure;
            }
        },
    }
}
