use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Range, Sub, SubAssign};

/// TODO: docs
pub trait Summarize: Debug {
    type Summary: Debug
        + Default
        + Clone
        + for<'a> AddAssign<&'a Self::Summary>
        + for<'a> SubAssign<&'a Self::Summary>;

    fn summarize(&self) -> Self::Summary;
}

/// TODO: docs
pub trait Leaf: Summarize + Borrow<Self::Slice> + Sized {
    type BaseMetric: Metric<Self>;

    type Slice: ?Sized
        + Summarize<Summary = <Self as Summarize>::Summary>
        + ToOwned<Owned = Self>;
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

    /// TODO: docs
    #[allow(unused_variables)]
    #[allow(clippy::type_complexity)]
    fn split_left<'a>(
        slice: &'a L::Slice,
        up_to: Self,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, Option<(&'a L::Slice, L::Summary)>) {
        unimplemented!(
            "Trying to split left {slice:?} at {up_to:?}, but {} cannot be \
             split by {}",
            std::any::type_name::<L>(),
            std::any::type_name::<Self>()
        )
    }

    /// TODO: docs
    #[allow(unused_variables)]
    #[allow(clippy::type_complexity)]
    fn split_right<'a>(
        slice: &'a L::Slice,
        from: Self,
        summary: &L::Summary,
    ) -> (Option<(&'a L::Slice, L::Summary)>, &'a L::Slice, L::Summary) {
        unimplemented!(
            "Trying to split right {slice:?} at {from:?}, but {} cannot be \
             split by {}",
            std::any::type_name::<L>(),
            std::any::type_name::<Self>()
        )
    }

    /// Slice the leaf in the given range. This method should be implemented
    /// only if it makes sense to take "part of a leaf".
    #[allow(unused_variables)]
    fn slice<'a>(
        leaf: &'a L::Slice,
        range: Range<Self>,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary) {
        unimplemented!(
            "Trying to slice {leaf:?} in the {range:?} range, but {} cannot \
             be sliced by {}",
            std::any::type_name::<L>(),
            std::any::type_name::<Self>()
        )
    }
}
