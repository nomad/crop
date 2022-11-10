use std::ops::{Bound, RangeBounds};

use super::Chunks;

/// Note: assumes that `chunks` yields the same number of bytes as `s` and that
/// `chunks` is iterating forward.
pub(super) fn chunks_eq_str<'a>(chunks: Chunks<'a>, s: &str) -> bool {
    let mut checked = 0;
    for chunk in chunks {
        if chunk != &s[checked..(checked + chunk.len())] {
            return false;
        }
        checked += chunk.len();
    }
    true
}

pub(super) fn range_to_tuple<B>(
    range: B,
    lo: usize,
    hi: usize,
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
