use core::cmp::Ordering;
use core::ops::Range;

use super::*;

/// An immutable slice of a [`Tree`].
pub struct TreeSlice<'a, const ARITY: usize, L: Leaf> {
    /// The deepest node that contains all the leaves between (and including)
    /// [`start_slice`](Self::start_slice) and [`end_slice`](Self::end_slice).
    pub(super) root: &'a Arc<Node<ARITY, L>>,

    /// The base length of the subtree under [`root`](Self::root) up to the
    /// start of the [`start_slice`](Self::start_slice).
    pub(super) offset: L::BaseMetric,

    /// The total summary of this slice.
    pub(crate) summary: L::Summary,

    /// A right sub-slice of the leaf containing the start of the sliced range.
    pub(crate) start_slice: L::Slice<'a>,

    /// A left sub-slice of the leaf containing the end of the sliced range.
    pub(crate) end_slice: L::Slice<'a>,
}

/// The number of leaves spanned by a [`TreeSlice`].
#[derive(Debug)]
pub enum SliceLeafCount {
    One,
    Two,
    ThreeOrMore,
}

impl<const ARITY: usize, L: Leaf> Clone for TreeSlice<'_, ARITY, L> {
    #[inline]
    fn clone(&self) -> Self {
        TreeSlice { summary: self.summary.clone(), ..*self }
    }
}

impl<const ARITY: usize, L: Leaf> Copy for TreeSlice<'_, ARITY, L> where
    L::Summary: Copy
{
}

impl<'a, const ARITY: usize, L: Leaf> TreeSlice<'a, ARITY, L> {
    #[inline]
    pub fn base_len(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    /// Returns the M-length of all the leaves before the given offset, plus
    /// the M-length of the left sub-slice of the leaf at the given offset.
    #[inline]
    pub fn convert_len_from_base<M>(&self, base_offset: L::BaseMetric) -> M
    where
        M: FromMetric<L::BaseMetric, L::Summary>,
    {
        debug_assert!(base_offset <= self.base_len());

        if base_offset.is_zero() {
            M::zero()
        } else {
            self.root.convert_len::<_, M>(self.offset + base_offset)
                - self.measure_offset::<M>()
        }
    }

    /// Returns the base length of all the leaves before the given offset,
    /// plus the base length of the left sub-slice of the leaf at the given
    /// offset.
    #[inline]
    pub fn convert_len_to_base<M>(&self, offset: M) -> L::BaseMetric
    where
        M: FromMetric<L::BaseMetric, L::Summary>,
        L::BaseMetric: FromMetric<M, L::Summary>,
    {
        debug_assert!(offset <= self.measure::<M>());

        if offset.is_zero() {
            L::BaseMetric::zero()
        } else {
            let m_offset = self.measure_offset::<M>();
            self.root.convert_len::<_, L::BaseMetric>(m_offset + offset)
                - self.offset
        }
    }

    #[inline]
    pub fn end_slice(&self) -> L::Slice<'a> {
        self.end_slice
    }

    /// Returns the leaf at the given M-offset, plus the M-length of all the
    /// leaves before it.
    #[inline]
    pub fn leaf_at_offset<M>(&self, offset: M) -> (L::Slice<'a>, M)
    where
        M: Metric<L::Summary> + FromMetric<L::BaseMetric, L::Summary>,
    {
        debug_assert!(offset <= self.measure::<M>());

        let len_start_slice = self.start_slice.measure::<M>();

        if offset <= len_start_slice {
            return (self.start_slice, M::zero());
        }

        let len_total_minus_end =
            self.measure::<M>() - self.end_slice.measure::<M>();

        if len_total_minus_end < offset {
            return (self.end_slice, len_total_minus_end);
        }

        let m_offset = self.measure_offset::<M>();
        let (leaf, leaf_offset) = self.root.leaf_at_offset(m_offset + offset);
        (leaf.as_slice(), leaf_offset - m_offset)
    }

    #[inline]
    pub fn leaf_count(&self) -> SliceLeafCount {
        if self.root.is_leaf() {
            SliceLeafCount::One
        } else if self.start_slice.base_len() + self.end_slice.base_len()
            == self.base_len()
        {
            SliceLeafCount::Two
        } else {
            SliceLeafCount::ThreeOrMore
        }
    }

    #[inline]
    pub fn leaves(&self) -> Leaves<'a, ARITY, L> {
        Leaves::from(self)
    }

    #[inline]
    pub fn measure<M>(&self) -> M
    where
        M: Metric<L::Summary>,
    {
        self.summary.measure::<M>()
    }

    #[inline]
    pub fn start_slice(&self) -> L::Slice<'a> {
        self.start_slice
    }

    #[inline]
    pub fn summary(&self) -> &L::Summary {
        &self.summary
    }

    #[inline]
    pub(super) fn root(&self) -> &'a Arc<Node<ARITY, L>> {
        self.root
    }

    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        match &**self.root {
            Node::Internal(_) => {
                assert!(self.leaf_count() > 1);
                assert!(!self.start_slice.is_empty());
                assert!(!self.end_slice.is_empty());

                if self.leaf_count() == 2 {
                    assert_eq!(
                        self.summary.base_len(),
                        self.start_slice.base_len()
                            + self.end_slice.base_len()
                    );
                }

                // This last part checks that the first and last slices are
                // under different children of the root, making the latter the
                // deepest node that contains both.

                let (root, remove_offset) = {
                    let start = self.offset;
                    deepest_node_containing_base_range(
                        self.root,
                        start,
                        start + self.summary.base_len(),
                    )
                };

                // These asserts should be equivalent but we use them all for
                // redundancy.

                assert!(Arc::ptr_eq(self.root, root));
                assert_eq!(self.root.depth(), root.depth());
                assert!(remove_offset.is_zero());
            },

            Node::Leaf(leaf) => {
                assert_eq!(self.leaf_count(), 1);
                assert!(leaf.base_len() >= self.base_len());
            },
        }
    }

    /// Returns the `M`-length of the subtree under [`root`](Self::root) up to
    /// the start of the [`start_slice`](Self::start_slice).
    ///
    /// Note that it's never necessary to call this with `L::BaseMetric`, as
    /// that's already known to be [`Self::offset`].
    #[inline]
    fn measure_offset<M>(&self) -> M
    where
        M: FromMetric<L::BaseMetric, L::Summary>,
    {
        self.root.convert_len(self.offset)
    }
}

impl<'a, const ARITY: usize, L: Leaf> TreeSlice<'a, ARITY, L>
where
    for<'d> L::Slice<'d>: Default,
{
    #[track_caller]
    #[inline]
    pub fn slice<M>(self, range: Range<M>) -> Self
    where
        M: SlicingMetric<L> + FromMetric<L::BaseMetric, L::Summary>,
        L::BaseMetric: SlicingMetric<L> + FromMetric<M, L::Summary>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= self.measure::<M>());

        let start = self.offset + self.convert_len_to_base(range.start);
        let end = self.measure_offset::<M>() + range.end;
        Self::slice_node(self.root, start, end)
    }

    #[track_caller]
    #[inline]
    pub fn slice_from<M>(self, start: M) -> Self
    where
        M: SlicingMetric<L> + FromMetric<L::BaseMetric, L::Summary>,
        L::BaseMetric: SlicingMetric<L> + FromMetric<M, L::Summary>,
    {
        debug_assert!(start <= self.measure::<M>());

        let start = self.offset + self.convert_len_to_base(start);
        let end = self.offset + self.base_len();
        Self::slice_node(self.root, start, end)
    }

    #[inline]
    pub fn units<M>(&self) -> Units<'a, ARITY, L, M>
    where
        M: Metric<L::Summary>,
    {
        Units::from(self)
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
    pub(super) fn slice_node<S, E>(
        root: &'a Arc<Node<ARITY, L>>,
        start: S,
        end: E,
    ) -> Self
    where
        S: SlicingMetric<L>,
        E: SlicingMetric<L>,
    {
        debug_assert!(S::zero() <= start);
        debug_assert!(end <= root.measure::<E>());

        println!("Slicing between {start:?} and {end:?} in\n{root:#?}");

        let (root, start, end) =
            deepest_node_containing_range(root, start, end);

        let mut slice = Self {
            root,
            offset: L::BaseMetric::zero(),
            summary: L::Summary::empty(),
            start_slice: Default::default(),
            end_slice: Default::default(),
        };

        let mut recompute_root = false;

        build_slice(
            &mut slice,
            root,
            start,
            end,
            &mut S::zero(),
            &mut E::zero(),
            &mut recompute_root,
            &mut false,
            &mut false,
        );

        println!("Need to recompute root: {recompute_root}");

        if recompute_root {
            let start = slice.offset;

            let (root, offset) = deepest_node_containing_base_range(
                slice.root,
                start,
                start + slice.summary.base_len(),
            );

            slice.root = root;
            slice.offset -= offset;
        }

        println!("Slice's root: {:?}", slice.root);
        println!("Slice's offset: {:?}", slice.offset);
        println!("Slice's summary: {:?}", slice.summary);
        println!("Slice's start_slice: {:?}", slice.start_slice);
        println!("Slice's end_slice: {:?}", slice.end_slice);

        slice
    }
}

impl PartialEq<usize> for SliceLeafCount {
    #[inline]
    fn eq(&self, other: &usize) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl PartialOrd<usize> for SliceLeafCount {
    #[inline]
    fn partial_cmp(&self, &other: &usize) -> Option<Ordering> {
        match self {
            SliceLeafCount::One => Some(1.cmp(&other)),
            SliceLeafCount::Two => Some(2.cmp(&other)),
            SliceLeafCount::ThreeOrMore => {
                (other < 3).then_some(Ordering::Greater)
            },
        }
    }

    #[inline]
    fn ge(&self, &other: &usize) -> bool {
        if other == 3 {
            matches!(self, Self::ThreeOrMore)
        } else {
            self.partial_cmp(&other).is_some_and(Ordering::is_ge)
        }
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
    S: Metric<L::Summary>,
    E: Metric<L::Summary>,
{
    'outer: loop {
        match &**node {
            Node::Internal(inode) => {
                let mut offset = L::Summary::empty();

                for child in inode.children() {
                    let child_summary = child.summary();

                    let contains_start_slice = offset.measure::<S>()
                        + child_summary.measure::<S>()
                        >= start;

                    if contains_start_slice {
                        let contains_end_slice = offset.measure::<E>()
                            + child_summary.measure::<E>()
                            >= end;

                        if contains_end_slice {
                            node = child;
                            start -= offset.measure::<S>();
                            end -= offset.measure::<E>();
                            continue 'outer;
                        } else {
                            return (node, start, end);
                        }
                    } else {
                        offset += child_summary;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => return (node, start, end),
        }
    }
}

/// Same as [`deepest_node_containing_range`] except it only accepts base
/// lengths and thus can check whether a node contains `start` using `>`
/// instead of `>=` (because the remainder of a slice divided by the BaseMetric
/// should always be zero), resulting in a potentially deeper node than the one
/// returned by [`deepest_node_containing_range`].
///
/// Also returns the base length between the input `node` and the returned node.
#[inline]
pub(super) fn deepest_node_containing_base_range<const N: usize, L>(
    mut node: &Arc<Node<N, L>>,
    mut start: L::BaseMetric,
    mut end: L::BaseMetric,
) -> (&Arc<Node<N, L>>, L::BaseMetric)
where
    L: Leaf,
{
    let mut offset = L::BaseMetric::zero();

    'outer: loop {
        match &**node {
            Node::Internal(inode) => {
                let mut measured = L::BaseMetric::zero();

                for child in inode.children() {
                    let child_len = child.base_len();

                    let contains_start_slice = measured + child_len > start;

                    if contains_start_slice {
                        let contains_end_slice = measured + child_len >= end;

                        if contains_end_slice {
                            node = child;
                            start -= measured;
                            end -= measured;
                            offset += measured;
                            continue 'outer;
                        } else {
                            return (node, offset);
                        }
                    } else {
                        measured += child_len;
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
#[allow(clippy::too_many_arguments)]
fn build_slice<'a, const N: usize, L, S, E>(
    slice: &mut TreeSlice<'a, N, L>,
    node: &'a Arc<Node<N, L>>,
    start: S,
    end: E,
    start_offset: &mut S,
    end_offset: &mut E,
    recompute_root: &mut bool,
    found_start_slice: &mut bool,
    done: &mut bool,
) where
    L: Leaf,
    S: SlicingMetric<L>,
    E: SlicingMetric<L>,
{
    println!("Node is leaf? {}", node.is_leaf());

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
                    if *start_offset + child_summary.measure::<S>() >= start {
                        // This child contains the starting slice somewhere in
                        // its subtree. Run this function again with this child
                        // as the node.
                        build_slice(
                            slice,
                            child,
                            start,
                            end,
                            start_offset,
                            end_offset,
                            recompute_root,
                            found_start_slice,
                            done,
                        );
                    } else {
                        // This child comes before the starting leaf.
                        slice.offset += child_summary.base_len();
                        *start_offset += child_summary.measure::<S>();
                        *end_offset += child_summary.measure::<E>();
                    }
                } else if *end_offset
                    + slice.summary.measure::<E>()
                    + child_summary.measure::<E>()
                    >= end
                {
                    // This child contains the ending slice somewhere in its
                    // subtree. Run this function again with this child as the
                    // node.
                    build_slice(
                        slice,
                        child,
                        start,
                        end,
                        start_offset,
                        end_offset,
                        recompute_root,
                        found_start_slice,
                        done,
                    );
                } else {
                    // This node is fully contained between the starting and
                    // the ending slices.
                    slice.summary += child_summary;
                }
            }
        },

        Node::Leaf(leaf) => {
            let leaf_summary = leaf.summarize();

            // This leaf must contain either the first slice, the last slice or
            // both.

            let contains_end_slice = *end_offset
                + slice.summary.measure::<E>()
                + leaf_summary.measure::<E>()
                >= end;

            if !*found_start_slice {
                debug_assert!(slice.summary.is_empty());

                debug_assert!({
                    // If we haven't yet found the first slice this leaf must
                    // contain it.
                    *start_offset + leaf_summary.measure::<S>() >= start
                });

                if contains_end_slice {
                    // The end of the range is also contained in this leaf
                    // so the final slice only spans this single leaf.
                    let start = start - *start_offset;

                    let right_slice = S::slice_from(leaf.as_slice(), start);

                    let left_slice_end_measure =
                        leaf.measure::<E>() - right_slice.measure::<E>();

                    let left_slice_base_measure =
                        leaf.base_len() - right_slice.base_len();

                    let end = end - *end_offset - left_slice_end_measure;

                    let start_slice = E::slice_up_to(right_slice, end);

                    slice.offset += left_slice_base_measure;
                    slice.summary = start_slice.summarize();
                    slice.start_slice = start_slice;
                    slice.end_slice = start_slice;

                    println!(
                        "Set both start and end slices to {start_slice:?}"
                    );

                    *done = true;
                } else {
                    // This leaf contains the first slice but not the last.
                    let start_slice =
                        S::slice_from(leaf.as_slice(), start - *start_offset);

                    if start_slice.is_empty() {
                        slice.offset += leaf.base_len();
                        *start_offset += leaf.measure::<S>();
                        *end_offset += leaf.measure::<E>();
                        *recompute_root = true;
                        return;
                    }

                    let start_summary = start_slice.summarize();

                    slice.offset += leaf.base_len() - start_summary.base_len();
                    *end_offset +=
                        leaf.measure::<E>() - start_summary.measure::<E>();

                    slice.summary += start_summary;
                    slice.start_slice = start_slice;
                    *found_start_slice = true;
                }
            } else {
                debug_assert!(contains_end_slice);

                let end = end - *end_offset - slice.summary.measure::<E>();

                // This leaf contains the last slice.
                let end_slice = E::slice_up_to(leaf.as_slice(), end);

                debug_assert!(!end_slice.is_empty());

                slice.summary += end_slice.summarize();
                slice.end_slice = end_slice;

                *done = true;
            }
        },
    }
}
