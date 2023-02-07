use std::fmt::Write;
use std::ops::{Bound, RangeBounds};

use super::iterators::Chunks;
use super::rope_chunk::{ChunkSlice, ChunkSummary, RopeChunk};
use crate::tree::Summarize;

#[inline]
pub(super) fn adjust_split_point<const WITH_RIGHT_BIAS: bool>(
    s: &str,
    mut candidate: usize,
) -> usize {
    if WITH_RIGHT_BIAS {
        while !s.is_char_boundary(candidate) {
            candidate += 1;
        }
        if is_splitting_crlf_pair(s, candidate) {
            candidate += 1;
        }
    } else {
        while !s.is_char_boundary(candidate) {
            candidate -= 1;
        }
        if is_splitting_crlf_pair(s, candidate) {
            candidate -= 1;
        }
    }
    candidate
}

/// Balances `left` with the contents of `right`, assuming that:
///
/// - `left` has less than `RopeChunk::min_bytes()` bytes;
/// - `right` has more than `RopeChunk::min_bytes()` bytes;
/// - `left` and `right` can't be combined in a single `RopeChunk`, i.e. `left`
/// and `right` combined have more than `RopeChunk::max_bytes()` bytes.
#[inline]
pub(super) fn balance_left_with_right(
    left: &ChunkSlice,
    left_summary: &ChunkSummary,
    right: &ChunkSlice,
    right_summary: &ChunkSummary,
) -> ((RopeChunk, ChunkSummary), (RopeChunk, ChunkSummary)) {
    debug_assert!(left.len() < RopeChunk::min_bytes());
    debug_assert!(right.len() > RopeChunk::min_bytes());
    debug_assert!(left.len() + right.len() > RopeChunk::max_bytes());

    let bytes_to_left = adjust_split_point::<false>(
        right,
        RopeChunk::min_bytes() - left.len(),
    );

    let add_to_left: &ChunkSlice = (&right[..bytes_to_left]).into();

    let add_to_left_summary = add_to_left.summarize();

    let mut left = left.to_owned();
    left.push_str(add_to_left);

    let mut left_summary = *left_summary;
    left_summary += &add_to_left_summary;

    let right: &ChunkSlice = (&right[bytes_to_left..]).into();

    let mut right_summary = *right_summary;
    right_summary -= &add_to_left_summary;

    ((left, left_summary), (right.to_owned(), right_summary))
}

/// Balances `right` with the contents of `left`, assuming that:
///
/// - `left` has more than `RopeChunk::min_bytes()` bytes;
/// - `right` has less than `RopeChunk::min_bytes()` bytes;
/// - `left` and `right` can't be combined in a single `RopeChunk`, i.e. `left`
/// and `right` combined have more than `RopeChunk::max_bytes()` bytes.
#[inline]
pub(super) fn balance_right_with_left(
    left: &ChunkSlice,
    left_summary: &ChunkSummary,
    right: &ChunkSlice,
    right_summary: &ChunkSummary,
) -> ((RopeChunk, ChunkSummary), (RopeChunk, ChunkSummary)) {
    debug_assert!(left.len() > RopeChunk::min_bytes());
    debug_assert!(right.len() < RopeChunk::min_bytes());
    debug_assert!(left.len() + right.len() > RopeChunk::max_bytes());

    let bytes_keep_left = adjust_split_point::<true>(
        left,
        left.len() - (RopeChunk::min_bytes() - right.len()),
    );

    let add_to_right: &ChunkSlice = (&left[bytes_keep_left..]).into();

    let add_to_right_summary = add_to_right.summarize();

    let left: &ChunkSlice = (&left[..bytes_keep_left]).into();

    let mut left_summary = *left_summary;
    left_summary -= &add_to_right_summary;

    let old_right = right;

    let mut right = add_to_right.to_owned();
    right.push_str(old_right);

    let mut right_summary = *right_summary;
    right_summary += &add_to_right_summary;

    ((left.to_owned(), left_summary), (right, right_summary))
}

/// Returns the number of bytes that `s`'s trailing line break takes up.
///
/// NOTE: this function assumes that `s` ends with a newline (`\n`), if `s`
/// doesn't it can return a wrong result.
#[inline]
pub(super) fn bytes_line_break(s: &str) -> usize {
    debug_assert!(!s.is_empty() && *s.as_bytes().last().unwrap() == b'\n');
    1 + (s.len() > 1 && s.as_bytes()[s.len() - 2] == b'\r') as usize
}

/// Checks equality between the chunks yielded by iterating over a [`Chunks`]
/// and a string slice.
///
/// This is used in the `PartialEq` implementation between `Rope`/`RopeSlice`s
/// and strings. It's assumed that if we get this far `chunks` and `s` have the
/// same number of bytes.
#[inline]
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
#[inline]
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
                right_chunk = &right_chunk[left_chunk.len()..];
                left_chunk = &[];
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

/// Iterates over the string slices yielded by [`Chunks`], writing the debug
/// output of each chunk to a formatter.
#[inline]
pub(super) fn debug_chunks(
    chunks: Chunks<'_>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    for chunk in chunks {
        // This is basically the Debug impl of a string slice except it doesn't
        // enclose the output in double quotes and also escapes single quotes.
        let mut from = 0;
        for (idx, char) in chunk.char_indices() {
            let esc = char.escape_debug();
            if esc.len() != 1 {
                f.write_str(&chunk[from..idx])?;
                for c in esc {
                    f.write_char(c)?;
                }
                from = idx + char.len_utf8();
            }
        }
        f.write_str(&chunk[from..])?;
    }

    Ok(())
}

/// Returns `true` if the last byte in the string slice is a carriage return.
///
/// # Panics
///
/// This function will panic if the string slice is empty.
pub(super) fn ends_in_cr(s: &str) -> bool {
    s.as_bytes()[s.len() - 1] == b'\r'
}

/// Returns whether `byte_offset` is a grapheme boundary in the string
/// constructed by concatenating the chunks yielded by `chunks`.
#[cfg(feature = "graphemes")]
#[inline]
pub(super) fn is_grapheme_boundary(
    mut chunks: Chunks<'_>,
    byte_len: usize,
    byte_offset: usize,
) -> bool {
    use unicode_segmentation::{GraphemeCursor, GraphemeIncomplete};

    debug_assert!(byte_offset <= byte_len);

    let mut cursor = GraphemeCursor::new(0, byte_len, true);
    cursor.set_cursor(byte_offset);

    let mut bytes_left = byte_len;

    // TODO: we need something like `Rope{Slice}::chunks_in_range` to make this
    // fast.
    //
    // Iterate from the back until we reach the chunk containing the given byte
    // index.
    let chunk = loop {
        let chunk = chunks.next_back().unwrap();
        bytes_left -= chunk.len();
        if bytes_left <= byte_offset {
            break chunk;
        }
    };

    if !chunk.is_char_boundary(byte_offset - bytes_left) {
        return false;
    }

    let chunk_start = bytes_left;

    loop {
        match cursor.is_boundary(chunk, chunk_start) {
            Ok(is_boundary) => return is_boundary,

            Err(GraphemeIncomplete::PreContext(offset)) => {
                debug_assert_eq!(offset, bytes_left);
                let prev = chunks.next_back().unwrap();
                bytes_left -= prev.len();
                cursor.provide_context(prev, bytes_left);
            },

            _ => unreachable!(),
        }
    }
}

/// Returns whether `byte_offset` would be splitting a CRLF pair inside `s`.
#[inline]
pub(super) fn is_splitting_crlf_pair(s: &str, byte_offset: usize) -> bool {
    byte_offset > 0
        && byte_offset < s.len()
        && ({
            let s = s.as_bytes();
            s[byte_offset - 1] == b'\r' && s[byte_offset] == b'\n'
        })
}

/// Returns `true` if the last byte of the string slice is a line feed (0x0A).
#[inline]
pub(super) fn last_byte_is_newline(s: &str) -> bool {
    !s.is_empty() && s.as_bytes()[s.len() - 1] == b'\n'
}

#[inline]
pub(super) fn range_bounds_to_start_end<B>(
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

/// Returns a tuple `(to_add, rest)`, where `to_add` is the largest left
/// sub-slice of `text` that can be added to `current` that still keeps the
/// latter under the byte limit of [`RopeChunk`]s. It follows that `rest` is
/// the right sub-slice of `text` not included in `to_add`.
#[inline]
pub(super) fn rope_chunk_append<'a>(
    current: &str,
    text: &'a str,
) -> (&'a str, &'a str) {
    if current.len() >= RopeChunk::max_bytes() {
        // If the current text is already longer than `RopeChunk::max_bytes()`
        // the only edge case to consider is not splitting CRLF pairs.
        if ends_in_cr(current) && starts_with_lf(text) {
            return (&text[0..1], &text[1..]);
        } else {
            return ("", text);
        }
    }

    let mut bytes_to_add = RopeChunk::max_bytes() - current.len();

    if text.len() <= bytes_to_add {
        return (text, "");
    }

    bytes_to_add = adjust_split_point::<true>(text, bytes_to_add);

    (&text[..bytes_to_add], &text[bytes_to_add..])
}

/// Returns `true` if the first byte in the string slice is a line feed.
pub(super) fn starts_with_lf(s: &str) -> bool {
    !s.is_empty() && s.as_bytes()[0] == b'\n'
}
