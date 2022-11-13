use std::ops::{Bound, RangeBounds};

use super::iterators::Chunks;

/// Checks equality between the chunks yielded by iterating over a [`Chunks`]
/// and a string slice.
///
/// This is used in the `PartialEq` implementation between `Rope`/`RopeSlice`s
/// and strings. It's assumed that if we get this far `chunks` and `s` have the
/// same number of bytes.
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

/// Checks equality between the chunks yielded by iterating over two
/// [`Chunks`].
///
/// This is used in the `PartialEq` implementation between `Rope`s and
/// `RopeSlice`s. It's assumed that if we get this far both chunks yield the
/// same number of bytes.
pub(super) fn chunks_eq_chunks<'a, 'b>(
    mut lhs: Chunks<'a>,
    mut rhs: Chunks<'b>,
) -> bool {
    let mut left_chunk = lhs.next().unwrap_or("").as_bytes();
    let mut right_chunk = rhs.next().unwrap_or("").as_bytes();

    loop {
        if left_chunk.len() < right_chunk.len() {
            if left_chunk != &right_chunk[..left_chunk.len()] {
                return false;
            } else {
                left_chunk = &[];
                right_chunk = &right_chunk[..left_chunk.len()];
            }
        } else if &left_chunk[..right_chunk.len()] != right_chunk {
            return false;
        } else {
            left_chunk = &left_chunk[right_chunk.len()..];
            right_chunk = &[];
        }

        if left_chunk.is_empty() {
            match lhs.next() {
                Some(chunk) => left_chunk = chunk.as_bytes(),

                // This works because both chunks are assumed to yield the same
                // number of bytes, so if one iterator is done then so is the
                // other.
                _ => return true,
            }
        }

        if right_chunk.is_empty() {
            match rhs.next() {
                Some(chunk) => right_chunk = chunk.as_bytes(),

                // Same as above.
                _ => return true,
            }
        }
    }
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
