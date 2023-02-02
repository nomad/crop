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
        M: SlicingMetric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= root.measure::<M>() + M::one());

        let (root, range, _) = deepest_node_containing_range(root, range);

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

        tree_slice_from_range_in_root(
            &mut slice,
            root,
            range,
            L::BaseMetric::zero(),
            None,
            None,
            &mut L::Summary::default(),
            &mut false,
            &mut false,
        );

        // There's a final edge case that can happen when the start and end of
        // the range coincide (so the slice has zero measure) and the start of
        // the range lies "between" the end of a leaf and the start of the
        // next one.
        //
        // In this case the root is the leaf *preceding* the start of the range
        // and all other metadata are set correctly, *except* the number of
        // leaves which never gets modified and is still set as zero.
        if slice.leaf_count == 0 {
            slice.leaf_count = 1;
        }

        slice
    }

    /// NOTE: doesn't do bound checks on `range`.
    #[inline]
    pub fn slice<M>(&'a self, range: Range<M>) -> TreeSlice<'a, FANOUT, L>
    where
        M: SlicingMetric<L>,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= self.measure::<M>() + M::one());

        let mut slice = Self::from_range_in_root(
            self.root,
            Range {
                start: M::measure(&self.offset) + range.start,
                end: M::measure(&self.offset) + range.end,
            },
        );

        if range.start == M::zero() {
            // TODO: this is wrong if the root has changed.
            // TODO: this is wrong if num_leaves == 1

            // NOTE: If the slice starts at M::zero() we need to fix the
            // `offset`, the `start_slice` and the `start_summary` of the slice
            // we got back from `Self::from_range_in_root`.
            //
            // To understand why let's consider the slice "bb\ncc" taken from
            // the following Tree:
            //
            // Root
            // ├── "aaa\n"
            // ├── "bbb\n"
            // └── "cccc"
            //
            // Slicing that slice in the `RawLineMetric(0)..RawLineMetric(1)`
            // range should result in "bb\n", but the slice we get back from
            // `from_range_in_root` is taken by slicing the **root** in the
            // `RawLineMetric(1)..RawLineMetric(2)` range, which results in
            // "bbb\n".
            //
            // To fix this we simply override the `start_slice` and
            // `start_summary` fields with the ones of `self`, and also add the
            // difference between the old and new `start_summary` to the
            // slice's `offset`.

            debug_assert!(
                L::BaseMetric::measure(&slice.start_summary)
                    >= L::BaseMetric::measure(&self.start_summary)
            );

            slice.offset += &slice.start_summary;
            slice.offset -= &self.start_summary;
            slice.start_slice = self.start_slice;
            slice.start_summary = self.start_summary.clone();
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

#[inline]
fn deepest_node_containing_range<const N: usize, L: Leaf, M: Metric<L>>(
    mut node: &Arc<Node<N, L>>,
    mut range: Range<M>,
) -> (&Arc<Node<N, L>>, Range<M>, L::BaseMetric) {
    let mut base_distance_from_original = L::BaseMetric::zero();

    'outer: loop {
        match &**node {
            Node::Internal(inode) => {
                let mut base = L::BaseMetric::zero();
                let mut measured = M::zero();

                for child in inode.children() {
                    let child_summary = child.summary();

                    if measured <= range.start
                        && measured + M::measure(&child_summary) >= range.end
                    {
                        node = child;
                        range.start -= measured;
                        range.end -= measured;
                        base_distance_from_original += base;
                        continue 'outer;
                    }

                    measured += M::measure(&child_summary);
                    base += L::BaseMetric::measure(&child_summary);
                }

                // If no child of this internal node fully contains the range
                // then this node is the deepest one fully containing the
                // range.
                break (node, range, base_distance_from_original);
            },

            Node::Leaf(_) => break (node, range, base_distance_from_original),
        }
    }
}

// Can we modify `tree_slice_from_range_in_root` so that it also works
// with `TreeSlice`s?
//
// Things to worry about:
//
// - keep track of the base measured;
//
// - once you get to the start leaf, need to be able to tell if you
// should use the `start_slice` instead of the leaf;
//
// - once you get to the last leaf, need to be able to tell if you
// should use the `start_slice` instead of the leaf;
//
// - we should use >= instead of >. If we go to slice the leaf and the right
// summary is empty we need to get to the next leaf. That means the root might
// change. This is real hard to deal with tbh.
//
// - needs to work if the end of the range is = measure + 1, in that
// case you need to take until the end. If the two coincide you need to
// panic.

// TODO if first_slice is some the slice is smaller but the range.start is the
// same. doesn't that fuck shit up?
//
// What if instead of passing the first and last slices we just act as if we're
// slicing a Tree and then fix the start_slice, end_slice once we're done if
// necessary.
//
// TODO: how do you detect if it's necessary?
//
// TODO: how do you fix it?
//
// Tbh this would be a lot better since that complexity would remain in
// `TreeSlice::slice` (which is where it belongs) and this function would stay
// more like it was before.

#[inline]
fn tree_slice_from_range_in_root<
    'a,
    const N: usize,
    L: Leaf,
    M: SlicingMetric<L>,
>(
    slice: &mut TreeSlice<'a, N, L>,
    node: &'a Arc<Node<N, L>>,
    range: Range<M>,
    take_after_offset: L::BaseMetric,
    first_slice: Option<(&'a L::Slice, &'a L::Summary)>,
    last_slice: Option<(&'a L::Slice, &'a L::Summary)>,
    measured: &mut L::Summary, // cant we use slice.(offset + summary?)
    found_first_slice: &mut bool,
    done: &mut bool,
) {
    match &**node {
        Node::Internal(inode) => {
            for child in inode.children() {
                if *done {
                    return;
                }

                let child_summary = child.summary();

                if !*found_first_slice {
                    let a = M::measure(&slice.offset)
                        + M::measure(&child_summary)
                        // why > ?
                        // this doesn't work w/ the LineMetric
                        > range.start;

                    let b = L::BaseMetric::measure(&slice.offset)
                        + L::BaseMetric::measure(&child_summary)
                        > take_after_offset;

                    if a && b {
                        tree_slice_from_range_in_root(
                            slice,
                            child,
                            Range { ..*&range },
                            take_after_offset,
                            first_slice,
                            last_slice,
                            measured,
                            found_first_slice,
                            done,
                        );
                    } else {
                        slice.offset += child_summary;
                        *measured += child_summary;
                    }
                }
                // TODO: docs
                else if M::measure(&*measured) + M::measure(&child_summary)
                    >= range.end
                {
                    tree_slice_from_range_in_root(
                        slice,
                        child,
                        Range { ..*&range },
                        take_after_offset,
                        first_slice,
                        last_slice,
                        measured,
                        found_first_slice,
                        done,
                    );
                }
                // TODO: docs
                else {
                    slice.summary += child_summary;
                    slice.leaf_count += child.num_leaves();
                    *measured += child_summary;
                }
            }
        },

        Node::Leaf(leaf) => {
            let leaf_summary = leaf.summary();

            if !*found_first_slice {
                let a = M::measure(&slice.offset)
                        + M::measure(&leaf_summary)
                        // why > ?
                        // this doesn't work w/ the LineMetric
                        >= range.start;

                let b = L::BaseMetric::measure(&slice.offset)
                    + L::BaseMetric::measure(&leaf_summary)
                    > take_after_offset;

                if a && b {
                    let (to_slice, summary) = if let Some(first) = first_slice
                    {
                        first
                    } else {
                        (leaf.as_slice(), leaf.summary())
                    };

                    // TODO: docs
                    if M::measure(measured) + M::measure(leaf_summary)
                        >= range.end
                    {
                        let range = Range {
                            start: range.start - M::measure(measured),
                            end: range.end - M::measure(measured),
                        };

                        let (left_summary, start_slice, start_summary) =
                            M::take(to_slice, range, summary);

                        slice.offset += &left_summary;
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary.clone();
                        slice.end_slice = start_slice;
                        slice.end_summary = start_summary.clone();
                        slice.summary = start_summary;
                        slice.leaf_count = 1;

                        *done = true;
                    }
                    // TODO: docs
                    else {
                        let (_, right_summary, start_slice, start_summary) =
                            M::split(
                                to_slice,
                                range.start - M::measure(measured),
                                summary,
                            );

                        debug_assert!(
                            L::BaseMetric::measure(&start_summary)
                                > L::BaseMetric::zero()
                        );

                        slice.offset += &right_summary;
                        slice.summary += &start_summary;
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.leaf_count = 1;

                        *measured += leaf_summary;
                        *found_first_slice = true;
                    }
                }
                // TODO: docs
                else {
                    slice.offset += leaf_summary;
                    *measured += leaf_summary;
                }
            }
            // TODO: docs
            else if M::measure(&*measured) + M::measure(&leaf_summary)
                >= range.end
            {
                let (to_slice, summary) = if let Some(last) = last_slice {
                    last
                } else {
                    (leaf.as_slice(), leaf.summary())
                };

                let (end_slice, end_summary, _, _) = M::split(
                    to_slice,
                    range.end - M::measure(measured),
                    summary,
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
            // TODO: docs
            else {
                slice.summary += leaf_summary;
                slice.leaf_count += 1;
                *measured += leaf_summary;
            }
        },
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
    M: SlicingMetric<L>,
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
                        slice.offset += child.summary();
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

                        slice.offset += &left_summary;

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
                        slice.offset += &before_summary;
                        slice.summary = start_summary.clone();
                        slice.start_slice = start_slice;
                        slice.start_summary = start_summary;
                        slice.leaf_count = 1;
                        *found_start = true;
                    }
                } else {
                    // This leaf comes before the starting leaf.
                    slice.offset += leaf.summary();
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
