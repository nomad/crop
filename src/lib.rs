#![allow(clippy::explicit_auto_deref)]
#![allow(clippy::module_inception)]
#![deny(rustdoc::broken_intra_doc_links)]

mod rope;
mod tree;

pub mod iter {
    //! Iterators over [`Rope`](crate::Rope)s and
    //! [`RopeSlice`](crate::RopeSlice)s.

    pub use crate::rope::iterators::*;
}

pub use rope::{Rope, RopeBuilder, RopeSlice};

#[inline]
pub(crate) fn range_bounds_to_start_end<B>(
    range: B,
    lo: usize,
    hi: usize,
) -> (usize, usize)
where
    B: std::ops::RangeBounds<usize>,
{
    use std::ops::Bound;

    let start = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n + 1,
        Bound::Unbounded => lo,
    };

    let end = match range.end_bound() {
        Bound::Included(&n) => n + 1,
        Bound::Excluded(&n) => n,
        Bound::Unbounded => hi,
    };

    (start, end)
}
