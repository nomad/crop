use std::ops::Range;
use std::sync::Arc;

use super::{Leaf, Leaves, Metric, Node, Units};

#[derive(Debug)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    /// The deepest node that contains all the leaves between..
    pub(super) root: &'a Arc<Node<FANOUT, L>>,

    /// The summary between the left-most leaf of the root and the start of the
    /// slice.
    pub(super) offset: L::BaseMetric,

    /// The total summary of this slice.
    pub(super) summary: L::Summary,

    /// TODO: docs
    pub(super) start_slice: &'a L::Slice,

    /// TODO: docs
    pub(super) start_summary: L::Summary,

    /// TODO: docs
    pub(super) end_slice: &'a L::Slice,

    /// TODO: docs
    pub(super) end_summary: L::Summary,

    /// The number of leaves spanned by this slice, also counting the leaves
    /// containing the start and end slices.
    pub(super) leaf_count: usize,
}

impl<'a, const FANOUT: usize, L: Leaf> Clone for TreeSlice<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        TreeSlice {
            summary: self.summary.clone(),
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
    /// Returns the base measure of this slice's summary.
    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    #[inline]
    pub fn convert_measure<M1, M2>(&self, from: M1) -> M2
    where
        M1: Metric<L>,
        M2: Metric<L>,
    {
        // let before = M1::measure(&self.before);
        // let measure = self.root.convert_measure::<M1, M2>(from + before);
        // measure - M2::measure(&self.before)

        todo!();
    }

    /// Returns the `M`-measure of this slice's summary.
    #[inline]
    pub fn measure<M: Metric<L>>(&self) -> M {
        M::measure(self.summary())
    }

    #[inline]
    pub fn end_slice(&'a self) -> &'a L::Slice {
        self.end_slice
    }

    #[inline]
    pub fn end_summary(&'a self) -> &'a L::Summary {
        &self.end_summary
    }

    #[inline]
    pub fn leaf_at_measure<M>(&'a self, measure: M) -> (&'a L::Slice, M)
    where
        M: Metric<L>,
    {
        debug_assert!(
            measure < M::measure(self.summary()),
            "Trying to get the leaf at {:?}, but this tree is only {:?} long",
            measure,
            M::measure(self.summary()),
        );

        // let before = M::measure(&self.before);
        // let (slice, mut measure) = self.root.leaf_at_measure(measure + before);
        // measure -= before;
        // (slice, measure)

        todo!();
    }

    /// TODO: docs
    #[inline]
    pub fn leaves(&'a self) -> Leaves<'a, FANOUT, L> {
        Leaves::from(self)
    }

    /// Returns .
    #[inline]
    pub fn leaf_count(&'a self) -> usize {
        self.leaf_count
    }

    #[inline]
    pub(super) fn root(&self) -> &Arc<Node<FANOUT, L>> {
        &self.root
    }

    #[inline]
    pub fn start_slice(&'a self) -> &'a L::Slice {
        self.start_slice
    }

    #[inline]
    pub fn start_summary(&'a self) -> &'a L::Summary {
        &self.start_summary
    }

    #[inline]
    pub fn summary(&self) -> &L::Summary {
        &self.summary
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
            offset: L::BaseMetric::zero(),
            summary: L::Summary::default(),
            start_slice: Default::default(),
            start_summary: L::Summary::default(),
            end_slice: Default::default(),
            end_summary: L::Summary::default(),
            leaf_count: 0,
        };

        tree_slice_from_range_in_root_rec(
            root,
            range,
            &mut M::zero(),
            &mut tree_slice,
            &mut false,
            &mut false,
        );

        // There's a final edge case that can happen when the start and end of
        // the range coincide (so the slice has zero measure) and the start of
        // the range lies "between" the end of a chunk and the start of the
        // next one.
        //
        // In this case the root is the leaf *preceding* the start of the range
        // and all other metadata are set correctly, *except* the number of
        // leaves which never gets modified and is still set as zero.
        if tree_slice.leaf_count == 0 {
            tree_slice.leaf_count = 1;
        }

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

        todo!();

        // let before = M::measure(&self.before);
        // range.start += before;
        // range.end += before;

        // Self::from_range_in_root(self.root, range)
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

#[inline]
pub(super) fn deepest_node_containing_range<
    'a,
    const N: usize,
    L: Leaf,
    M: Metric<L>,
>(
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
                        slice.offset +=
                            L::BaseMetric::measure(child.summary());
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
                    slice.leaf_count += child.num_leaves();
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

                        slice.offset += L::BaseMetric::measure(&left_summary);

                        let (start_slice, start_summary, _, _) = M::split(
                            right_slice,
                            range.end - *measured - M::measure(&left_summary),
                            &right_summary,
                        );

                        slice.summary = start_summary.clone();

                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary.clone();

                        slice.end_slice = start_slice;
                        slice.end_summary = start_summary;

                        slice.leaf_count = 1;
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
                        slice.offset +=
                            L::BaseMetric::measure(&before_summary);
                        slice.summary = start_summary.clone();
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.leaf_count = 1;
                        *found_start = true;
                    }
                } else {
                    // This leaf comes before the starting leaf.
                    slice.offset += L::BaseMetric::measure(leaf.summary());
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
                slice.end_slice = end_slice;
                slice.end_summary = end_summary;
                slice.leaf_count += 1;
                *done = true;
            } else {
                // This is a leaf between the starting and the ending slices.
                slice.summary += leaf.summary();
                slice.leaf_count += 1;
                *measured += measure;
            }
        },
    }
}
