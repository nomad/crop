use std::ops::{Bound, RangeBounds};

pub(super) fn range_bound_to_tuple<B>(
    range: B,
    hi: usize,
    lo: usize,
) -> (usize, usize)
where
    B: RangeBounds<usize>,
{
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
