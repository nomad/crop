use std::ops::Range;
use std::sync::Arc;

use super::{Leaf, Leaves, Metric, Node, Units};

#[derive(Debug)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    /// TODO: docs
    pub(super) root: &'a Arc<Node<FANOUT, L>>,

    /// TODO: docs
    pub(super) offset: L::Summary,

    /// TODO: docs
    pub(super) after: L::Summary,

    /// TODO: docs
    pub(super) summary: L::Summary,

    /// TODO: docs
    pub(super) start_slice: &'a L::Slice,

    /// TODO: docs
    pub(super) start_summary: L::Summary,

    /// TODO: docs
    pub(super) end_slice: &'a L::Slice,

    /// TODO: docs
    pub(super) end_summary: L::Summary,

    /// The number of leaves included in this [`TreeSlice`] (including
    /// the start and end slices). Used by the [`Leaves`] iterator.
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
            offset: self.offset.clone(),
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

        // TODO: consider using `MaybeUninit` instead of adding a `Default`
        // bound on L::Slice.
        let mut tree_slice = Self {
            root,
            offset: L::Summary::default(),
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
    pub fn slice<M>(&'a self, range: Range<M>) -> TreeSlice<'a, FANOUT, L>
    where
        M: Metric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        // debug_assert!(range.end <= M::measure(self.summary()));

        // TODO: consider using `MaybeUninit` instead of adding a `Default`
        // bound on L::Slice.
        let mut tree_slice = Self {
            root: self.root,
            offset: L::Summary::default(),
            summary: L::Summary::default(),
            after: self.summary().clone(),
            start_slice: Default::default(),
            start_summary: L::Summary::default(),
            end_slice: Default::default(),
            end_summary: L::Summary::default(),
            num_leaves: 0,
        };

        tree_slice_from_range_in_root_rec(
            self.root,
            range,
            &mut M::measure(&self.offset),
            &mut tree_slice,
            &mut false,
            &mut false,
        );

        tree_slice
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
                        // its subtree.
                        if *measured + measure >= range.end {
                            // If the child also contains the end of the range
                            // then this is the new root.
                            slice.root = child;
                        }
                        // Run this function again with this child
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
                        slice.offset += child.summary();
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
                        let (start_slice, start_summary) = M::slice(
                            leaf.as_slice(),
                            range.start - *measured..range.end - *measured,
                            leaf.summary(),
                        );
                        slice.summary = start_summary.clone();
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.num_leaves = 1;
                        *done = true;
                    } else {
                        // This leaf contains the starting slice but not the
                        // ending one.
                        let (_, _, start_slice, start_summary) = M::split(
                            leaf.as_slice(),
                            range.start - *measured,
                            leaf.summary(),
                        );
                        *measured += measure;
                        slice.summary = start_summary.clone();
                        slice.after -= leaf.summary();
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.num_leaves = 1;
                        *found_start = true;
                    }
                } else {
                    // This leaf comes before the starting leaf.
                    slice.offset += leaf.summary();
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
                slice.after -= leaf.summary();
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
