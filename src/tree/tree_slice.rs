use std::ops::Range;
use std::sync::Arc;

use super::{Leaf, Leaves, Metric, Node, SlicingMetric, Units};

#[derive(Debug)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    /// The deepest node that contains all the leaves between..
    pub(super) root: &'a Arc<Node<FANOUT, L>>,

    /// The summary between the left-most leaf of the root and the start of the
    /// slice.
    pub(super) offset: L::Summary,

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

impl<const FANOUT: usize, L: Leaf> Clone for TreeSlice<'_, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        TreeSlice {
            offset: self.offset.clone(),
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
        M1: SlicingMetric<L>,
        M2: Metric<L>,
    {
        debug_assert!(
            from <= self.measure::<M1>() + M1::one(),
            "Trying to convert {:?} into {}, but this TreeSlice is only {:?} \
             long",
            from,
            std::any::type_name::<M2>(),
            self.measure::<M1>(),
        );

        if from == M1::zero() {
            M2::zero()
        } else {
            self.root
                .convert_measure::<M1, M2>(M1::measure(&self.offset) + from)
                - M2::measure(&self.offset)
        }
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

        if measure <= M::measure(&self.start_summary) {
            (self.start_slice, M::zero())
        } else {
            let all_minus_last =
                M::measure(&self.summary) - M::measure(&self.end_summary);
            if measure <= all_minus_last {
                let (leaf, mut offset) = self
                    .root
                    .leaf_at_measure(M::measure(&self.offset) + measure);
                offset -= M::measure(&self.offset);
                (leaf, offset)
            } else {
                (self.end_slice, all_minus_last)
            }
        }
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
        self.root
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
    /// NOTE: doesn't do any bounds checks on `range`.
    #[inline]
    pub(super) fn from_range_in_root<M>(
        root: &'a Arc<Node<FANOUT, L>>,
        range: Range<M>,
    ) -> Self
    where
        M: SlicingMetric<L>,
        L::BaseMetric: SlicingMetric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= root.measure::<M>() + M::one());

        if range.end <= root.measure::<M>() {
            Self::slice_impl(root, range.start, range.end)
        } else if range.start <= root.measure::<M>() {
            Self::slice_impl(root, range.start, root.base_measure())
        } else {
            Self::slice_impl(root, root.base_measure(), root.base_measure())
        }
    }

    /// NOTE: doesn't do any bounds checks on `range`.
    #[inline]
    pub fn slice<M>(self, mut range: Range<M>) -> TreeSlice<'a, FANOUT, L>
    where
        M: SlicingMetric<L>,
        L::BaseMetric: SlicingMetric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= self.measure::<M>() + M::one());

        if range.start > M::zero() {
            range.start += M::measure(&self.offset);
            range.end += M::measure(&self.offset);
            Self::from_range_in_root(self.root, range)
        } else if range.end <= self.measure::<M>() {
            let start = L::BaseMetric::measure(&self.offset);
            if range.end > M::zero() {
                let end = M::measure(&self.offset) + range.end;
                Self::slice_impl(self.root, start, end)
            } else {
                Self::slice_impl(self.root, start, start)
            }
        } else {
            self
        }
    }

    /// TODO: docs
    #[inline]
    fn slice_impl<S, E>(
        root: &'a Arc<Node<FANOUT, L>>,
        start: S,
        end: E,
    ) -> TreeSlice<'a, FANOUT, L>
    where
        S: SlicingMetric<L>,
        E: SlicingMetric<L>,
    {
        debug_assert!(S::zero() <= start);
        debug_assert!(end <= root.measure::<E>());

        let (root, start, end) =
            deepest_node_containing_range(root, start, end);

        let mut slice = Self {
            root,
            offset: L::Summary::default(),
            summary: L::Summary::default(),
            start_slice: Default::default(),
            start_summary: L::Summary::default(),
            end_slice: Default::default(),
            end_summary: L::Summary::default(),
            leaf_count: 0,
        };

        let mut recompute_root = false;

        tree_slice_from_range_in_root(
            &mut slice,
            root,
            start,
            end,
            &mut false,
            &mut recompute_root,
            &mut false,
        );

        if recompute_root {
            let start = L::BaseMetric::measure(&slice.offset);

            let (root, offset) = deepest_node_containing_base_range_greedy(
                slice.root,
                start,
                start + L::BaseMetric::measure(&slice.summary),
            );

            slice.root = root;
            slice.offset -= &offset;
        }

        slice
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

/// TODO: docs
#[inline]
fn deepest_node_containing_range<const N: usize, L, S, E>(
    mut node: &Arc<Node<N, L>>,
    mut start: S,
    mut end: E,
) -> (&Arc<Node<N, L>>, S, E)
where
    L: Leaf,
    S: Metric<L>,
    E: Metric<L>,
{
    'outer: loop {
        match &**node {
            Node::Internal(inode) => {
                let mut measured = L::Summary::default();

                for child in inode.children() {
                    let child_summary = child.summary();

                    let contains_first_slice = S::measure(&measured)
                        + S::measure(child_summary)
                        >= start;

                    if contains_first_slice {
                        let contains_last_slice = E::measure(&measured)
                            + E::measure(child_summary)
                            >= end;

                        if contains_last_slice {
                            node = child;
                            start -= S::measure(&measured);
                            end -= E::measure(&measured);
                            continue 'outer;
                        } else {
                            return (node, start, end);
                        }
                    } else {
                        measured += child_summary;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => return (node, start, end),
        }
    }
}

/// TODO: docs
#[inline]
pub(super) fn deepest_node_containing_base_range_greedy<const N: usize, L>(
    mut node: &Arc<Node<N, L>>,
    mut start: L::BaseMetric,
    mut end: L::BaseMetric,
) -> (&Arc<Node<N, L>>, L::Summary)
where
    L: Leaf,
{
    let mut offset = L::Summary::default();

    'outer: loop {
        match &**node {
            Node::Internal(inode) => {
                let mut measured = L::Summary::default();

                for child in inode.children() {
                    let child_summary = child.summary();

                    let contains_first_slice =
                        L::BaseMetric::measure(&measured) <= start;

                    let contains_last_slice =
                        L::BaseMetric::measure(&measured)
                            + L::BaseMetric::measure(child_summary)
                            >= end;

                    if contains_first_slice && contains_last_slice {
                        node = child;
                        start -= L::BaseMetric::measure(&measured);
                        end -= L::BaseMetric::measure(&measured);
                        offset += &measured;
                        continue 'outer;
                    } else {
                        measured += child_summary;
                    }
                }

                return (node, offset);
            },

            Node::Leaf(_) => return (node, offset),
        }
    }
}

/// TODO: docs
#[inline]
fn tree_slice_from_range_in_root<'a, const N: usize, L, S, E>(
    slice: &mut TreeSlice<'a, N, L>,
    node: &'a Arc<Node<N, L>>,
    start: S,
    end: E,
    found_first_slice: &mut bool,
    recompute_root: &mut bool,
    done: &mut bool,
) where
    L: Leaf,
    S: SlicingMetric<L>,
    E: SlicingMetric<L>,
{
    match &**node {
        Node::Internal(inode) => {
            for child in inode.children() {
                // If the slice has been completed there's nothing left to do,
                // simply unwind the call stack.
                if *done {
                    return;
                }

                let child_summary = child.summary();

                if !*found_first_slice {
                    if S::measure(&slice.offset) + S::measure(child_summary)
                        >= start
                    {
                        // This child contains the starting slice somewhere in
                        // its subtree. Run this function again with this child
                        // as the node.
                        tree_slice_from_range_in_root(
                            slice,
                            child,
                            start,
                            end,
                            found_first_slice,
                            recompute_root,
                            done,
                        );
                    } else {
                        // This child comes before the starting leaf.
                        slice.offset += child_summary;
                    }
                } else if E::measure(&slice.offset)
                    + E::measure(&slice.summary)
                    + E::measure(child_summary)
                    >= end
                {
                    // This child contains the ending leaf somewhere in its
                    // subtree. Run this function again with this child as the
                    // node.
                    tree_slice_from_range_in_root(
                        slice,
                        child,
                        start,
                        end,
                        found_first_slice,
                        recompute_root,
                        done,
                    );
                } else {
                    // This is a node fully contained between the starting and
                    // the ending slices.
                    slice.summary += child_summary;
                    slice.leaf_count += child.num_leaves();
                }
            }
        },

        Node::Leaf(leaf) => {
            let leaf_summary = leaf.summary();

            if !*found_first_slice {
                let contains_first_slice = S::measure(&slice.offset)
                    + S::measure(leaf_summary)
                    >= start;

                if contains_first_slice {
                    let contains_last_slice = E::measure(&slice.offset)
                        + E::measure(leaf_summary)
                        >= end;

                    if contains_last_slice {
                        // The end of the range is also contained in this leaf
                        // so the final slice only spans this single leaf.
                        let start = start - S::measure(&slice.offset);

                        let (_, left_summary, right_slice, right_summary) =
                            S::split(leaf.as_slice(), start, leaf.summary());

                        let end = end
                            - E::measure(&slice.offset)
                            - E::measure(&left_summary);

                        let (start_slice, start_summary, _, _) =
                            E::split(right_slice, end, &right_summary);

                        slice.offset += &left_summary;
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary.clone();
                        slice.end_slice = start_slice;
                        slice.end_summary = start_summary.clone();
                        slice.summary = start_summary;
                        slice.leaf_count = 1;

                        *done = true;
                    } else {
                        // This leaf contains the starting slice but not the
                        // ending one.
                        let (_, right_summary, start_slice, start_summary) =
                            S::split(
                                leaf.as_slice(),
                                start - S::measure(&slice.offset),
                                leaf.summary(),
                            );

                        if L::BaseMetric::measure(&start_summary)
                            == L::BaseMetric::zero()
                        {
                            slice.offset += leaf.summary();
                            *recompute_root = true;
                            return;
                        }

                        slice.offset += &right_summary;
                        slice.summary += &start_summary;
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.leaf_count = 1;

                        *found_first_slice = true;
                    }
                } else {
                    // TODO: can we even get here?
                    // This leaf comes before the starting leaf.
                    slice.offset += leaf_summary;
                }
            } else {
                let measured =
                    E::measure(&slice.offset) + E::measure(&slice.summary);

                let contains_last_slice =
                    measured + E::measure(leaf_summary) >= end;

                if contains_last_slice {
                    // This leaf contains the ending slice.
                    let (end_slice, end_summary, _, _) = E::split(
                        leaf.as_slice(),
                        end - measured,
                        leaf.summary(),
                    );

                    debug_assert!(
                        L::BaseMetric::measure(&end_summary)
                            > L::BaseMetric::zero()
                    );

                    slice.summary += &end_summary;
                    slice.end_slice = end_slice;
                    slice.end_summary = end_summary;
                    slice.leaf_count += 1;

                    *done = true;
                }
                // This is a leaf between the starting and the ending slices.
                else {
                    // TODO: can we even get here?
                    slice.summary += leaf_summary;
                    slice.leaf_count += 1;
                }
            }
        },
    }
}
