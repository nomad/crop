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

    /// TODO: docs
    fn measure(summary: &L::Summary) -> Self;

    /// Slice the leaf in the given range. This method should be implemented
    /// only if it makes sense to take "part of a leaf".
    #[allow(unused_variables)]
    fn slice<'a>(leaf: &'a L::Slice, range: Range<Self>) -> &'a L::Slice {
        unimplemented!(
            "Trying to slice {leaf:?} in the {range:?} range, but {} isn't \
             sliceable by {}",
            std::any::type_name::<L>(),
            std::any::type_name::<Self>()
        )
    }
}
