use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Range, Sub, SubAssign};

/// TODO: docs
pub trait Summarize: Debug {
    type Summary: Debug
        + Default
        + Clone
        + for<'a> Add<&'a Self::Summary, Output = Self::Summary>
        + for<'a> Sub<&'a Self::Summary, Output = Self::Summary>
        + for<'a> AddAssign<&'a Self::Summary>
        + for<'a> SubAssign<&'a Self::Summary>;

    fn summarize(&self) -> Self::Summary;
}

/// TODO: docs
pub trait Leaf: Summarize + Borrow<Self::Slice> + Sized + Clone {
    type BaseMetric: Metric<Self>;

    type Slice: ?Sized
        + Summarize<Summary = <Self as Summarize>::Summary>
        + ToOwned<Owned = Self>;

    /// TODO: docs
    #[allow(unused_variables)]
    fn is_big_enough(&self, summary: &Self::Summary) -> bool {
        unimplemented!();
    }

    /// TODO: docs
    #[allow(unused_variables)]
    fn balance_slices<'a>(
        first: (&'a Self::Slice, &'a Self::Summary),
        second: (&'a Self::Slice, &'a Self::Summary),
    ) -> ((Self, Self::Summary), Option<(Self, Self::Summary)>) {
        unimplemented!();
    }
}

/// TODO: docs
pub trait Metric<L: Leaf>:
    Debug
    + Copy
    + Ord
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + AddAssign<Self>
    + SubAssign<Self>
{
    /// The identity element of this metric wrt to addition. It should always
    /// be such that `t + t::zero() = t` for all `t` in `T`.
    fn zero() -> Self;

    /// TODO: docs.
    fn one() -> Self;

    /// TODO: docs
    fn measure(summary: &L::Summary) -> Self;
}

/// TODO: docs
pub trait SlicingMetric<L: Leaf>: Metric<L> {
    /// TODO: docs
    #[allow(clippy::type_complexity)]
    fn split<'a>(
        slice: &'a L::Slice,
        at: Self,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, &'a L::Slice, L::Summary);

    /// TODO: docs
    #[allow(clippy::type_complexity)]
    fn take<'a>(
        slice: &'a L::Slice,
        range: Range<Self>,
        summary: &L::Summary,
    ) -> (L::Summary, &'a L::Slice, L::Summary) {
        let (_, left_summary, right_slice, right_summary) =
            Self::split(slice, range.start, summary);

        let (slice, summary, _, _) = Self::split(
            right_slice,
            range.end - Self::measure(&left_summary),
            &right_summary,
        );

        (left_summary, slice, summary)
    }
}

/// TODO: docs
pub trait UnitMetric<L: Leaf>: Metric<L> {
    /// TODO: docs
    #[allow(clippy::type_complexity)]
    fn first_unit<'a>(
        slice: &'a L::Slice,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, L::Summary, &'a L::Slice, L::Summary);
}

/// TODO: docs
pub trait DoubleEndedUnitMetric<L: Leaf>: UnitMetric<L> {
    /// TODO: docs
    #[allow(clippy::type_complexity)]
    fn last_unit<'a>(
        slice: &'a L::Slice,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, &'a L::Slice, L::Summary, L::Summary);

    /// TODO: docs
    #[allow(clippy::type_complexity)]
    fn remainder<'a>(
        slice: &'a L::Slice,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, &'a L::Slice, L::Summary);
}
