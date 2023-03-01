use std::fmt::Debug;
use std::ops::{Add, AddAssign, RangeBounds, Sub, SubAssign};

pub trait Summarize: Debug {
    type Summary: Debug
        + Default
        + Clone
        + for<'a> Add<&'a Self::Summary, Output = Self::Summary>
        + for<'a> Sub<&'a Self::Summary, Output = Self::Summary>
        + for<'a> AddAssign<&'a Self::Summary>
        + for<'a> SubAssign<&'a Self::Summary>
        + PartialEq<Self::Summary>;

    fn summarize(&self) -> Self::Summary;
}

pub trait BaseMeasured: Summarize {
    type BaseMetric: Metric<Self>;
}

pub trait AsSlice: Summarize + for<'a> From<Self::Slice<'a>> {
    type Slice<'a>: Copy + Summarize<Summary = Self::Summary>
    where
        Self: 'a;

    fn as_slice(&self) -> Self::Slice<'_>;
}

pub trait Leaf: Summarize + BaseMeasured + AsSlice {}

impl<T: Summarize + BaseMeasured + AsSlice> Leaf for T {}

pub trait BalancedLeaf: Leaf {
    /// Returns whether the leaf node is too small to be on its own and should
    /// be rebalanced with another leaf.
    fn is_underfilled(slice: Self::Slice<'_>, summary: &Self::Summary)
        -> bool;

    /// Balance two leaves.
    ///
    /// The `right` leaf can be left empty if the two leaves can be combined
    /// into a single one.
    fn balance_leaves(
        left: (&mut Self, &mut Self::Summary),
        right: (&mut Self, &mut Self::Summary),
    );

    /// Balances two leaf slices.
    ///
    /// The second element of the tuple can be omitted if the two slices can be
    /// combined into a single leaf.
    #[allow(clippy::type_complexity)]
    fn balance_slices(
        left: (Self::Slice<'_>, &Self::Summary),
        right: (Self::Slice<'_>, &Self::Summary),
    ) -> ((Self, Self::Summary), Option<(Self, Self::Summary)>);
}

pub trait ReplaceableLeaf<M: Metric<Self>>: BalancedLeaf {
    type ExtraLeaves: ExactSizeIterator<Item = Self>;

    /// Replace the contents of the leaf in the given range with `slice`. If
    /// that would cause the leaf to be too big the function can return an
    /// iterator over the leaves to insert right after this leaf. Note that in
    /// this case both this leaf and all the leaves yielded by the iterator are
    /// assumed to not be underfilled.
    fn replace<R>(
        &mut self,
        summary: &mut Self::Summary,
        range: R,
        slice: Self::Slice<'_>,
    ) -> Option<Self::ExtraLeaves>
    where
        R: RangeBounds<M>;

    /// Remove the contents of the leaf up to `up_to`. The leaf is allowed to
    /// be underfilled after calling this function.
    fn remove(&mut self, summary: &mut Self::Summary, up_to: M);
}

pub trait Metric<L: Summarize + ?Sized>:
    Debug
    + Copy
    + Ord
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + AddAssign<Self>
    + SubAssign<Self>
{
    /// The identity element of this metric with respect to addition.
    ///
    /// Given an implementor `M` of this trait, for all instances `m` of `M`
    /// it should hold `m == m + M::zero()`.
    fn zero() -> Self;

    /// The smallest value larger than [`zero`](Self::zero()) this metric can
    /// measure.
    fn one() -> Self;

    /// Returns the measure of the summary according to this metric.
    fn measure(summary: &L::Summary) -> Self;
}

/// Metrics that can be used to slice `Tree`s and `TreeSlice`s.
pub trait SlicingMetric<L: Leaf>: Metric<L> {
    /// Splits the given slice at `at`, returning a
    /// `(left_slice, left_summary, right_slice, right_summary)` tuple.
    ///
    /// The original slice must always be split without omitting any contents.
    /// In other words, it should always hold
    /// `left_summary + right_summary = summary`.
    #[allow(clippy::type_complexity)]
    fn split<'a>(
        slice: L::Slice<'a>,
        at: Self,
        summary: &L::Summary,
    ) -> (L::Slice<'a>, L::Summary, L::Slice<'a>, L::Summary);
}

/// Allows iterating forward over the units of this metric.
pub trait UnitMetric<L: Leaf>: Metric<L> {
    /// Returns a
    /// `(first_slice, first_summary, advance, rest_slice, rest_summary)`
    /// tuple, where `advance` is equal to `first_summary` **plus** the summary
    /// of any content between the end of `first_slice` and the start of
    /// `rest_slice` that's not included in neither of them.
    ///
    /// It follows that if `slice == first_slice ++ rest_slice` (where `++`
    /// denotes concatenation) the `first_summary` and the `advance` should be
    /// equal.
    ///
    /// In any case it must always hold `summary == advance + rest_summary`.
    #[allow(clippy::type_complexity)]
    fn first_unit<'a>(
        slice: L::Slice<'a>,
        summary: &L::Summary,
    ) -> (L::Slice<'a>, L::Summary, L::Summary, L::Slice<'a>, L::Summary);
}

/// Allows iterating backward over the units of this metric.
pub trait DoubleEndedUnitMetric<L: Leaf>: UnitMetric<L> {
    /// Returns a
    /// `(rest_slice, rest_summary, last_slice, last_summary, advance)`
    /// tuple, where `advance` is equal to `last_summary` **plus** the summary
    /// of any content between the end of `last_slice` and the end of the
    /// original `slice`.
    ///
    /// It follows that if `slice == rest_slice ++ last_slice` (where `++`
    /// denotes concatenation) the `last_summary` and the `advance` should be
    /// equal.
    ///
    /// In any case it must always hold `summary == rest_summary + advance`.
    #[allow(clippy::type_complexity)]
    fn last_unit<'a>(
        slice: L::Slice<'a>,
        summary: &L::Summary,
    ) -> (L::Slice<'a>, L::Summary, L::Slice<'a>, L::Summary, L::Summary);

    /// It's possible for a leaf slice to contain some content that extends
    /// past the end of its last `M`-unit. This is referred to as "the
    /// remainder of the leaf divided by `M`".
    ///
    /// Returns a `(rest_slice, rest_summary, remainder, remainder_summary)`
    /// tuple. Note that unlike [`last_unit`](Self::last_unit()), this function
    /// does not allow an `advance` to be returned. Instead `rest_slice` and
    /// `remainder` should always concatenate up the original `slice` and their
    /// summaries should sum up to the original `summary`.
    ///
    /// The remainder can be empty if the last `M`-unit coincides with the end
    /// of the leaf slice.
    #[allow(clippy::type_complexity)]
    fn remainder<'a>(
        slice: L::Slice<'a>,
        summary: &L::Summary,
    ) -> (L::Slice<'a>, L::Summary, L::Slice<'a>, L::Summary);
}
