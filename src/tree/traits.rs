use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Sub, SubAssign};

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

pub trait Leaf: Summarize + Borrow<Self::Slice> + Sized {
    type BaseMetric: Metric<Self>;

    type Slice: ?Sized
        + Summarize<Summary = <Self as Summarize>::Summary>
        + ToOwned<Owned = Self>;

    /// Returns `true` if the leaf is big enough on its own, `false` if it
    /// should be balanced with another leaf slice to become valid.
    #[allow(unused_variables)]
    fn is_big_enough(&self, summary: &Self::Summary) -> bool {
        true
    }

    /// Balances two leaves.
    ///
    /// There are no guarantees on whether both `first` and `second` are big
    /// enough, all combinations should be checked.
    ///
    /// The first `(leaf, summary)` in the returned tuple is the left leaf
    /// together with its summary, the second tuple is optional and is only
    /// returned if the two leaves didn't get combined in a single leaf.
    #[allow(unused_variables)]
    #[allow(clippy::type_complexity)]
    fn balance_slices<'a>(
        first: (&'a Self::Slice, &'a Self::Summary),
        second: (&'a Self::Slice, &'a Self::Summary),
    ) -> ((Self, Self::Summary), Option<(Self, Self::Summary)>) {
        unimplemented!();
    }
}

pub trait ReplaceableLeaf<M: Metric<Self>>: Leaf {
    type ExtraLeaves: ExactSizeIterator<Item = Self>;

    fn replace(
        &mut self,
        summary: &mut Self::Summary,
        range: std::ops::Range<M>,
        slice: &Self::Slice,
    ) -> Option<Self::ExtraLeaves>;

    fn remove(&mut self, summary: &mut Self::Summary, up_to: M);
}

pub trait Metric<L: Leaf>:
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
    /// produce.
    fn one() -> Self;

    /// Returns the measure of the summary according to this metric.
    fn measure(summary: &L::Summary) -> Self;
}

/// Metrics that can be used to slice `Tree`s and `TreeSlice`s.
pub trait SlicingMetric<L: Leaf>: Metric<L> {
    /// Splits the given slice at `at`, returning a
    /// `(left_slice, left_summary, right_slice, right_summary)` tuple.
    ///
    /// NOTE: the original slice must always be split without omitting any
    /// contents. In other words, it should always hold
    /// `summary == left_summary + right_summary`.
    #[allow(clippy::type_complexity)]
    fn split<'a>(
        slice: &'a L::Slice,
        at: Self,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, &'a L::Slice, L::Summary);
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
        slice: &'a L::Slice,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, L::Summary, &'a L::Slice, L::Summary);
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
        slice: &'a L::Slice,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, &'a L::Slice, L::Summary, L::Summary);

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
        slice: &'a L::Slice,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, &'a L::Slice, L::Summary);
}
