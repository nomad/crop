use std::ops::{Add, AddAssign};

use super::Summarize;

pub trait Metric<T: Summarize>:
    Copy + Ord + Sized + Add<Self, Output = Self> + AddAssign<Self>
// + for<'a> Add<&'a Self, Output = Self>
// + for<'a> AddAssign<&'a Self>
{
    /// The identity element of this metric wrt to addition. It should always
    /// be such that `t + t::zero() = t` for all `t` in `T`.
    fn zero() -> Self;

    /// TODO: docs
    fn measure(summary: &T::Summary) -> Self;
}
