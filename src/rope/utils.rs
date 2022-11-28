use std::ops::{Bound, RangeBounds};

use super::iterators::Chunks;
use super::{TextSlice, TextSummary};

/// Checks equality between the chunks yielded by iterating over a [`Chunks`]
/// and a string slice.
///
/// This is used in the `PartialEq` implementation between `Rope`/`RopeSlice`s
/// and strings. It's assumed that if we get this far `chunks` and `s` have the
/// same number of bytes.
pub(super) fn chunks_eq_str(chunks: Chunks<'_>, s: &str) -> bool {
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
pub(super) fn chunks_eq_chunks(
    mut lhs: Chunks<'_>,
    mut rhs: Chunks<'_>,
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

/// TODO: docs
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

/// Splits a [TextSlice] at the `line_break`th line break (0-indexed),
/// returning the left and right slices together with their summary if they are
/// not empty. The line break itself, be it a `\n` or a `\r\n`, is not part of
/// any of the 2 returned slices.
#[allow(clippy::type_complexity)]
pub(super) fn split_slice_at_line_break<'a>(
    chunk: &'a TextSlice,
    line_break: usize,
    summary: &TextSummary,
) -> (Option<(&'a TextSlice, TextSummary)>, Option<(&'a TextSlice, TextSummary)>)
{
    // This is the index of the byte *after* the newline, or the byte length of
    // the chunk if the newline is the last byte.
    let lf_plus_one = str_indices::lines_lf::to_byte_idx(chunk, line_break);

    let left_bytes = lf_plus_one
        // We have to stop 1 byte earlier if the line break is a `\n`..
        - 1
        // ..and 2 if it's a `\r\n`.
        - ((chunk.as_bytes()[lf_plus_one.saturating_sub(2)] == b'\r') as
           usize);

    let left = if left_bytes == 0 {
        None
    } else {
        Some((
            chunk[..left_bytes].into(),
            TextSummary { bytes: left_bytes, line_breaks: line_break - 1 },
        ))
    };

    let right = if lf_plus_one == chunk.len() {
        None
    } else {
        Some((
            chunk[lf_plus_one..].into(),
            TextSummary {
                bytes: chunk.len() - lf_plus_one,
                line_breaks: summary.line_breaks - line_break,
            },
        ))
    };

    (left, right)
}

/// TODO: docs
pub(super) fn slice_between_line_breaks(
    chunk: &TextSlice,
    start: usize,
    end: usize,
) -> &'_ TextSlice {
    debug_assert!(start < end);

    let byte_start = str_indices::lines_lf::to_byte_idx(chunk, start);

    let mut byte_end = byte_start
        + str_indices::lines_lf::to_byte_idx(
            &chunk[byte_start..],
            end - start,
        );

    // Same logic as above in `left_bytes` of [split_slice_at_line_break].
    byte_end = byte_end
        - 1
        - ((chunk.as_bytes()[byte_end.saturating_sub(2)] == b'\r') as usize);

    chunk[byte_start..byte_end].into()
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use super::*;

    #[test]
    fn between_line_breaks_1() {
        let chunk = "this is\na line\r\nwith mixed\nline breaks\n".into();

        let s = slice_between_line_breaks(chunk, 0, 1);
        assert_eq!("this is", s.deref());

        let s = slice_between_line_breaks(chunk, 0, 2);
        assert_eq!("this is\na line", s.deref());

        let s = slice_between_line_breaks(chunk, 1, 4);
        assert_eq!("a line\r\nwith mixed\nline breaks", s.deref());

        let s = slice_between_line_breaks(chunk, 2, 3);
        assert_eq!("with mixed", s.deref());

        let s = slice_between_line_breaks(chunk, 0, 5);
        assert_eq!("this is\na line\r\nwith mixed\nline breaks", s.deref());
    }
}
