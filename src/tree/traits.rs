use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Sub, SubAssign};

/// TODO: docs
pub trait Summarize: Debug {
    type Summary: Debug
        + Default
        + Clone
        + for<'a> AddAssign<&'a Self::Summary>;

    fn summarize(&self) -> Self::Summary;
}

/// TODO: docs
pub trait Leaf: Summarize + Borrow<Self::Slice> + Sized + Clone {
    const MIN_LEAF_SIZE: Self::BaseMetric;

    type BaseMetric: Metric<Self>;

    type Slice: ?Sized
        + Summarize<Summary = <Self as Summarize>::Summary>
        + ToOwned<Owned = Self>;

    /// TODO: docs
    #[allow(unused_variables)]
    fn append_slice(&mut self, slice: &Self::Slice) {
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

    /// Split the leaf slice at the given measure. This method should be
    /// implemented only if it makes sense to take "part of a leaf".
    #[allow(unused_variables)]
    #[allow(clippy::type_complexity)]
    fn split<'a>(
        slice: &'a L::Slice,
        at: Self,
        summary: &L::Summary,
    ) -> (&'a L::Slice, L::Summary, &'a L::Slice, L::Summary) {
        unimplemented!(
            "Trying to split {slice:?} at {at:?}, but {} cannot be split by
            {}",
            std::any::type_name::<L>(),
            std::any::type_name::<Self>()
        )
    }
}
