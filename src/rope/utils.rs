use std::fmt::Write;
use std::ops::{Bound, RangeBounds};

use super::iterators::Chunks;
use super::{ChunkSlice, ChunkSummary, Rope, RopeChunk};
use crate::tree::TreeSlice;

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

/// TODO: docs
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

/// Returns `true` if the last byte of the string slice is a line feed (0x0A).
///
/// # Panics
///
/// This function will panic if the string slice is empty.
#[inline]
pub(super) fn last_byte_is_newline(s: &str) -> bool {
    s.as_bytes()[s.len() - 1] == b'\n'
}

/// TODO: docs
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

/// TODO: docs
#[inline]
pub(super) fn rope_chunk_append<'a>(
    current: &str,
    mut text: &'a str,
) -> (&'a str, &'a str) {
    todo!()
}

/// TODO: docs
#[inline]
pub(super) fn rope_slice_remove_trailing_line_break(
    slice: &mut TreeSlice<'_, { Rope::fanout() }, RopeChunk>,
) {
    debug_assert!(matches!(slice.summary().line_breaks, 0 | 1));

    if slice.summary().line_breaks == 1 {
        todo!();
    }
}

/// Splits a chunk at the `line_break`-th line break (0-indexed), returning the
/// left and right slices and their respective summaries.
#[inline]
#[allow(clippy::type_complexity)]
pub(super) fn split_slice_at_line_break<'a>(
    chunk: &'a ChunkSlice,
    line_break: usize,
    summary: &ChunkSummary,
) -> (&'a ChunkSlice, ChunkSummary, &'a ChunkSlice, ChunkSummary) {
    // This is the index of the byte *after* the newline, or the byte length of
    // the chunk if the newline is the last byte.
    let left_bytes = str_indices::lines_lf::to_byte_idx(chunk, line_break);

    let left = chunk[..left_bytes].into();

    let left_summary =
        ChunkSummary { bytes: left_bytes, line_breaks: line_break };

    let right = chunk[left_bytes..].into();

    let right_summary = ChunkSummary {
        bytes: chunk.len() - left_bytes,
        line_breaks: summary.line_breaks - line_break,
    };

    (left, left_summary, right, right_summary)
}
