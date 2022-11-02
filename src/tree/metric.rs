use std::ops::{Add, AddAssign, Range, Sub};

use super::Summarize;

pub trait Metric<Leaf: Summarize>:
    Copy
    + Ord
    + Sized
    + Add<Self, Output = Self>
    + AddAssign<Self>
    + Sub<Self, Output = Self>
// + for<'a> Add<&'a Self, Output = Self>
// + for<'a> AddAssign<&'a Self>
{
    /// The identity element of this metric wrt to addition. It should always
    /// be such that `t + t::zero() = t` for all `t` in `T`.
    fn zero() -> Self;

    /// TODO: docs
    fn measure(summary: &Leaf::Summary) -> Self;

    // NOTE: it might be impossible for some leaf types to return a reference
    // after slicing, some leaves may need to return an owned value. Consider
    // returning a Cow<'a, Leaf>?
    /// Slice the leaf in the given range. This method should be implemented
    /// iff it makes sense to take "part of a leaf", in which case it's
    /// expected to return `Some`.
    #[allow(unused_variables)]
    fn slice<'a>(leaf: &'a Leaf, range: Range<&Self>) -> Option<&'a Leaf> {
        None
    }
}
