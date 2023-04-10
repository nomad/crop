use core::ops::Range;

use super::*;

/// An immutable slice of a [`Tree`].
#[derive(Debug)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    /// The deepest node that contains all the leaves between (and including)
    /// [`start_slice`](Self::start_slice) and [`end_slice`](Self::end_slice).
    pub(super) root: &'a Arc<Node<FANOUT, L>>,

    /// The summary of the subtree under [`root`](Self::root) up to the start
    /// of the [`start_slice`](Self::start_slice).
    pub(super) offset: L::Summary,

    /// The total summary of this slice.
    pub(crate) summary: L::Summary,

    /// A right sub-slice of the leaf containing the start of the sliced range.
    pub(crate) start_slice: L::Slice<'a>,

    /// [`start_slice`](Self::start_slice)'s summary.
    pub(crate) start_summary: L::Summary,

    /// A left sub-slice of the leaf containing the end of the sliced range.
    pub(crate) end_slice: L::Slice<'a>,

    /// [`end_slice`](Self::end_slice)'s summary.
    pub(crate) end_summary: L::Summary,

    /// The number of leaves spanned by this slice, including the leaves
    /// containing the first and last slices.
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

impl<const FANOUT: usize, L: Leaf> Copy for TreeSlice<'_, FANOUT, L> where
    L::Summary: Copy
{
}

impl<'a, const FANOUT: usize, L: Leaf> TreeSlice<'a, FANOUT, L> {
    /*
      Public methods
    */

    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        match &**self.root {
            Node::Internal(_) => {
                assert!(self.leaf_count > 1);

                assert_eq!(self.start_slice.summarize(), self.start_summary);

                assert_eq!(self.end_slice.summarize(), self.end_summary);

                assert!(
                    L::BaseMetric::measure(&self.start_summary)
                        > L::BaseMetric::zero()
                );

                assert!(
                    L::BaseMetric::measure(&self.end_summary)
                        > L::BaseMetric::zero()
                );

                if self.leaf_count == 2 {
                    assert_eq!(
                        self.summary,
                        self.start_summary.clone() + &self.end_summary
                    );
                }

                // This last part checks that the first and last slices are
                // under different children of the root, making the latter the
                // deepest node that contains both.

                let (root, remove_offset) = {
                    let start = L::BaseMetric::measure(&self.offset);
                    deepest_node_containing_base_range(
                        self.root,
                        start,
                        start + L::BaseMetric::measure(&self.summary),
                    )
                };

                // These asserts should be equivalent but we use them all for
                // redundancy.

                assert!(Arc::ptr_eq(self.root, root));
                assert_eq!(self.root.depth(), root.depth());
                assert_eq!(
                    L::BaseMetric::measure(&remove_offset),
                    L::BaseMetric::zero()
                );
            },

            Node::Leaf(leaf) => {
                assert_eq!(1, self.leaf_count);
                assert_eq!(self.start_summary, self.summary);
                assert_eq!(self.summary, self.end_summary);
                assert!(leaf.base_measure() >= self.base_measure());
            },
        }
    }

    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    /// Returns the `M2`-measure of all the leaves before `up_to` plus the
    /// `M2`-measure of the left sub-slice of the leaf at `up_to`.
    #[inline]
    pub fn convert_measure<M1, M2>(&self, up_to: M1) -> M2
    where
        M1: SlicingMetric<L>,
        M2: Metric<L>,
    {
        debug_assert!(up_to <= self.measure::<M1>());

        if up_to == M1::zero() {
            M2::zero()
        } else {
            self.root
                .convert_measure::<M1, M2>(M1::measure(&self.offset) + up_to)
                - M2::measure(&self.offset)
        }
    }

    #[inline]
    pub fn end_slice(&self) -> L::Slice<'a> {
        self.end_slice
    }

    #[inline]
    pub fn end_summary(&self) -> &L::Summary {
        &self.end_summary
    }

    /// Returns the leaf containing the `measure`-th unit of the `M`-metric,
    /// plus the `M`-measure of all the leaves before it.
    #[inline]
    pub fn leaf_at_measure<M>(&self, measure: M) -> (L::Slice<'a>, M)
    where
        M: Metric<L>,
    {
        debug_assert!(measure <= self.measure::<M>() + M::one());

        if M::measure(&self.start_summary) >= measure {
            (self.start_slice, M::zero())
        } else {
            let all_minus_last =
                M::measure(&self.summary) - M::measure(&self.end_summary);

            if all_minus_last >= measure {
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

    #[inline]
    pub fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    #[inline]
    pub fn leaves(&self) -> Leaves<'a, FANOUT, L> {
        Leaves::from(self)
    }

    #[inline]
    pub fn measure<M: Metric<L>>(&self) -> M {
        M::measure(self.summary())
    }

    #[inline]
    pub(super) fn root(&self) -> &'a Arc<Node<FANOUT, L>> {
        self.root
    }

    #[inline]
    pub fn start_slice(&self) -> L::Slice<'a> {
        self.start_slice
    }

    #[inline]
    pub fn start_summary(&self) -> &L::Summary {
        &self.start_summary
    }

    #[inline]
    pub fn summary(&self) -> &L::Summary {
        &self.summary
    }
}

impl<'a, const FANOUT: usize, L: Leaf> TreeSlice<'a, FANOUT, L>
where
    for<'d> L::Slice<'d>: Default,
{
    #[track_caller]
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

    #[track_caller]
    #[inline]
    pub fn slice<M>(self, mut range: Range<M>) -> Self
    where
        M: SlicingMetric<L>,
        L::BaseMetric: SlicingMetric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= self.measure::<M>() + M::one());

        match (
            range.start > M::zero(),
            range.end < self.measure::<M>() + M::one(),
        ) {
            (true, true) => {
                range.start += M::measure(&self.offset);
                range.end += M::measure(&self.offset);
                Self::from_range_in_root(self.root, range)
            },

            (true, false) => {
                let start = M::measure(&self.offset) + range.start;
                let end =
                    L::BaseMetric::measure(&self.offset) + self.base_measure();
                Self::slice_impl(self.root, start, end)
            },

            (false, true) if range.end > M::zero() => {
                let start = L::BaseMetric::measure(&self.offset);
                let end = M::measure(&self.offset) + range.end;
                Self::slice_impl(self.root, start, end)
            },

            (false, true) => {
                let start = L::BaseMetric::measure(&self.offset);
                Self::slice_impl(self.root, start, start)
            },

            (false, false) => self,
        }
    }

    /// Returns the `TreeSlice` obtained by slicing `root` between `start` and
    /// `end`.
    ///
    /// Note that `start` and `end` are specified using different metrics so
    /// there's no way to tell if `start` actually precedes `end` without
    /// traversing the nodes (which this function doesn't do).
    ///
    /// It's the caller's responsibility to guarantee this, and this function
    /// can panic or return an incorrect or invalid `TreeSlice` if this
    /// condition is not met.
    #[track_caller]
    #[inline]
    fn slice_impl<S, E>(
        root: &'a Arc<Node<FANOUT, L>>,
        start: S,
        end: E,
    ) -> Self
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

        build_slice(
            &mut slice,
            root,
            start,
            end,
            &mut recompute_root,
            &mut false,
            &mut false,
        );

        if recompute_root {
            let start = L::BaseMetric::measure(&slice.offset);

            let (root, offset) = deepest_node_containing_base_range(
                slice.root,
                start,
                start + L::BaseMetric::measure(&slice.summary),
            );

            slice.root = root;
            slice.offset -= &offset;
        }

        slice
    }

    #[inline]
    pub fn units<M>(&self) -> Units<'a, FANOUT, L, M>
    where
        M: Metric<L>,
    {
        Units::from(self)
    }
}

/// Returns the deepest node under `nodes`'s subtree that fully contains the
/// range between `start` and `end`, together with the `S` and `E` offsets with
/// respect to that node.
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

                    let contains_start_slice = S::measure(&measured)
                        + S::measure(child_summary)
                        >= start;

                    if contains_start_slice {
                        let contains_end_slice = E::measure(&measured)
                            + E::measure(child_summary)
                            >= end;

                        if contains_end_slice {
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

/// Same as [`deepest_node_containing_range`] except it only accepts base
/// measures and thus can check whether a node contains `start` using `>`
/// instead of `>=` (because the remainder of a slice divided by the BaseMetric
/// should always be zero), resulting in a potentially deeper node than the one
/// returned by [`deepest_node_containing_range`].
///
/// Also returns the summary between the input `node` and the returned node.
#[inline]
pub(super) fn deepest_node_containing_base_range<const N: usize, L>(
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

                    let contains_start_slice =
                        L::BaseMetric::measure(&measured)
                            + L::BaseMetric::measure(child_summary)
                            > start;

                    if contains_start_slice {
                        let contains_end_slice =
                            L::BaseMetric::measure(&measured)
                                + L::BaseMetric::measure(child_summary)
                                >= end;

                        if contains_end_slice {
                            node = child;
                            start -= L::BaseMetric::measure(&measured);
                            end -= L::BaseMetric::measure(&measured);
                            offset += &measured;
                            continue 'outer;
                        } else {
                            return (node, offset);
                        }
                    } else {
                        measured += child_summary;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => return (node, offset),
        }
    }
}

/// Gradually builds the `TreeSlice` by recursively traversing all the nodes
/// between `start` and `end`.
///
/// The `found_start_slice` and `done` bits are used to track state while
/// traversing and should always start off as `false`.
///
/// # On `recompute_root`
///
/// The leaf node containing the start of the range could return an
/// empty right sub-slice when calling `S::split`. Since `TreeSlice`s are not
/// allowed to have an empty [`start_slice`](TreeSlice::start_slice) this
/// function will move to the following leaf to set that field. This
/// however means that the current root of the `slice` might not actually be
/// the deepest node containing the entire range.
///
/// When this happens the `recompute_root` bit will be set to `true` to
/// indicate that the slice's root (and its offset) needs to be recomputed. All
/// the other fields of the slice are valid.
#[track_caller]
#[inline]
fn build_slice<'a, const N: usize, L, S, E>(
    slice: &mut TreeSlice<'a, N, L>,
    node: &'a Arc<Node<N, L>>,
    start: S,
    end: E,
    recompute_root: &mut bool,
    found_start_slice: &mut bool,
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

                if !*found_start_slice {
                    if S::measure(&slice.offset) + S::measure(child_summary)
                        >= start
                    {
                        // This child contains the starting slice somewhere in
                        // its subtree. Run this function again with this child
                        // as the node.
                        build_slice(
                            slice,
                            child,
                            start,
                            end,
                            recompute_root,
                            found_start_slice,
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
                    build_slice(
                        slice,
                        child,
                        start,
                        end,
                        recompute_root,
                        found_start_slice,
                        done,
                    );
                } else {
                    // This is a node fully contained between the starting and
                    // the ending slices.
                    slice.summary += child_summary;
                    slice.leaf_count += child.leaf_count();
                }
            }
        },

        Node::Leaf(leaf) => {
            let leaf_summary = leaf.summary();

            // This leaf must contain either the first slice, the last slice or
            // both.

            let contains_end_slice = E::measure(&slice.offset)
                + E::measure(&slice.summary)
                + E::measure(leaf_summary)
                >= end;

            if !*found_start_slice {
                debug_assert_eq!(L::Summary::default(), slice.summary);

                debug_assert!({
                    // If we haven't yet found the first slice this leaf must
                    // contain it.
                    S::measure(&slice.offset) + S::measure(leaf_summary)
                        >= start
                });

                if contains_end_slice {
                    // The end of the range is also contained in this leaf
                    // so the final slice only spans this single leaf.
                    let start = start - S::measure(&slice.offset);

                    let (right_slice, right_summary) =
                        S::slice_from(leaf.as_slice(), start, leaf.summary());

                    let left_summary = leaf.summary().clone() - &right_summary;

                    let end = end
                        - E::measure(&slice.offset)
                        - E::measure(&left_summary);

                    let (start_slice, start_summary) =
                        E::slice_up_to(right_slice, end, &right_summary);

                    slice.offset += &left_summary;
                    slice.start_slice = start_slice;
                    slice.start_summary = start_summary.clone();
                    slice.end_slice = start_slice;
                    slice.end_summary = start_summary.clone();
                    slice.summary = start_summary;
                    slice.leaf_count = 1;

                    *done = true;
                } else {
                    // This leaf contains the first slice but not the last.
                    let (start_slice, start_summary) = S::slice_from(
                        leaf.as_slice(),
                        start - S::measure(&slice.offset),
                        leaf.summary(),
                    );

                    let right_summary =
                        leaf.summary().clone() - &start_summary;

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

                    *found_start_slice = true;
                }
            } else {
                debug_assert!(contains_end_slice);

                let end = end
                    - E::measure(&slice.offset)
                    - E::measure(&slice.summary);

                // This leaf contains the last slice.
                let (end_slice, end_summary) =
                    E::slice_up_to(leaf.as_slice(), end, leaf.summary());

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
        },
    }
}
