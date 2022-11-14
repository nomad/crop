use std::fmt::Debug;
use std::ops::{Add, AddAssign, Range, Sub, SubAssign};

use super::Leaf;

/// TODO: docs
pub trait Metric<L: Leaf>:
    Debug
    + Copy
    + Ord
    + Sized
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
    fn split_right(
        slice: &L::Slice,
        from: Self,
    ) -> (Option<&L::Slice>, &L::Slice) {
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
    fn slice<'a>(leaf: &'a L::Slice, range: Range<Self>) -> &'a L::Slice {
        unimplemented!(
            "Trying to slice {leaf:?} in the {range:?} range, but {} cannot \
             be sliced by {}",
            std::any::type_name::<L>(),
            std::any::type_name::<Self>()
        )
    }
}
