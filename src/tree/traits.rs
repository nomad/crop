use core::fmt::Debug;
use core::ops::{Add, AddAssign, RangeBounds, Sub, SubAssign};

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
    type BaseMetric: Metric<Self::Summary>;

    #[inline]
    fn is_empty(&self) -> bool {
        Self::BaseMetric::measure(&self.summarize())
            == Self::BaseMetric::zero()
    }
}

pub trait AsSlice: Summarize {
    type Slice<'a>: Copy + Summarize<Summary = Self::Summary>
    where
        Self: 'a;

    fn as_slice(&self) -> Self::Slice<'_>;
}

pub trait Leaf: Summarize + BaseMeasured + AsSlice {}

impl<T: Summarize + BaseMeasured + AsSlice> Leaf for T {}

pub trait BalancedLeaf: Leaf + for<'a> From<Self::Slice<'a>> {
    /// Returns whether the leaf node is too small to be on its own and should
    /// be rebalanced with another leaf.
    fn is_underfilled(&self) -> bool;

    /// Balance two leaves.
    ///
    /// The `right` leaf can be left empty if the two leaves can be combined
    /// into a single one.
    fn balance_leaves(left: &mut Self, right: &mut Self);
}

pub trait ReplaceableLeaf<M: Metric<Self::Summary>>: BalancedLeaf {
    type Replacement<'a>;

    type ExtraLeaves: ExactSizeIterator<Item = Self>;

    /// Replace the contents of the leaf in the range with the given
    /// replacement.
    ///
    /// If that would cause the leaf to be too big the function can return an
    /// iterator over the leaves to insert right after this leaf. Note that in
    /// this case both this leaf and all the leaves yielded by the iterator are
    /// assumed to not be underfilled.
    fn replace<R>(
        &mut self,
        range: R,
        replace_with: Self::Replacement<'_>,
    ) -> Option<Self::ExtraLeaves>
    where
        R: RangeBounds<M>;

    fn remove_up_to(&mut self, up_to: M);
}

pub trait Metric<Summary: ?Sized>:
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
    fn measure(summary: &Summary) -> Self;
}

/// Metrics that can be used to slice `Tree`s and `TreeSlice`s.
pub trait SlicingMetric<L: Leaf>: Metric<L::Summary> {
    fn slice_up_to<'a>(slice: L::Slice<'a>, up_to: Self) -> L::Slice<'a>;

    fn slice_from<'a>(slice: L::Slice<'a>, from: Self) -> L::Slice<'a>;
}

/// Allows iterating forward over the units of this metric.
pub trait UnitMetric<L: Leaf>: Metric<L::Summary> {
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
