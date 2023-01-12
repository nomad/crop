use std::fmt::Write;
use std::ops::{Bound, RangeBounds};

use super::iterators::Chunks;
use super::{ChunkSlice, ChunkSummary, Rope, RopeChunk};
use crate::tree::{Summarize, TreeSlice};

#[allow(dead_code)]
pub(super) fn assert_valid_chunk(
    chunk: &str,
    next: Option<&str>,
    is_first: bool,
) {
    // TODO: explain the reason for the `-3`.
    let min_bytes = if RopeChunk::min_bytes() >= 4 {
        RopeChunk::min_bytes() - 3
    } else {
        1
    };

    // Only the first chunk of a single-chunk Rope is allowed to contain less
    // than the min number of bytes.
    if chunk.len() < min_bytes && !(is_first && next.is_none()) {
        panic!("AA: {chunk}");
    }

    // Chunks are only allowed to exceed the max number of bytes if the max
    // byte offset lies at a char boundary or between a CRLF pair.
    if chunk.len() > RopeChunk::max_bytes() {
        let excess = RopeChunk::max_bytes() - chunk.len();

        if !chunk.is_char_boundary(RopeChunk::max_bytes()) {
            let mut i = 1;
            while !chunk.is_char_boundary(RopeChunk::max_bytes() + i) {
                i += 1;
            }
            if i != excess {
                panic!("");
            }
        } else if !(excess == 1 && &chunk[chunk.len() - 2..] == "\r\n") {
            panic!("");
        }
    }

    // CRLF pairs should never be split across chunks.
    if let Some(&b'\r') = chunk.as_bytes().last() {
        if let Some(next) = next {
            if *next.as_bytes().first().unwrap() == b'\n' {
                panic!("");
            }
        }
    }
}

#[inline]
fn is_splitting_crlf_pair(s: &str, byte_offset: usize) -> bool {
    byte_offset > 0
        && byte_offset < s.len()
        && ({
            let s = s.as_bytes();
            s[byte_offset - 1] == b'\r' && s[byte_offset] == b'\n'
        })
}

/// TODO: docs
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

    let mut bytes_to_left = RopeChunk::min_bytes() - left.len();

    // If we're splitting a code point we take less bytes from the right slice.
    // This will result in the final left chunk having less than
    // `RopeChunk::min_bytes()` bytes.
    if !right.is_char_boundary(bytes_to_left) {
        bytes_to_left -= 1;
        while !right.is_char_boundary(bytes_to_left) {
            bytes_to_left -= 1;
        }
    }
    // Similarly, if we're splitting a CRLF pair we take 1 less byte.
    else if is_splitting_crlf_pair(right, bytes_to_left) {
        bytes_to_left -= 1;
    }

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

/// TODO: docs
#[inline]
pub(super) fn balance_right_with_left(
    left: &ChunkSlice,
    left_summary: &ChunkSummary,
    old_right: &ChunkSlice,
    right_summary: &ChunkSummary,
) -> ((RopeChunk, ChunkSummary), (RopeChunk, ChunkSummary)) {
    debug_assert!(left.len() > RopeChunk::min_bytes());
    debug_assert!(old_right.len() < RopeChunk::min_bytes());
    debug_assert!(left.len() + old_right.len() > RopeChunk::max_bytes());

    let mut bytes_keep_left =
        left.len() - (RopeChunk::min_bytes() - old_right.len());

    // If we're splitting a code point we take less bytes from the left slice.
    // This will result in the final right chunk having less than
    // `RopeChunk::min_bytes()` bytes.
    if !left.is_char_boundary(bytes_keep_left) {
        bytes_keep_left += 1;
        while !left.is_char_boundary(bytes_keep_left) {
            bytes_keep_left += 1;
        }
    }
    // Similarly, if we're splitting a CRLF pair we take 1 less byte.
    else if is_splitting_crlf_pair(left, bytes_keep_left) {
        bytes_keep_left += 1;
    }

    let add_to_right: &ChunkSlice = (&left[bytes_keep_left..]).into();

    let add_to_right_summary = add_to_right.summarize();

    let left: &ChunkSlice = (&left[..bytes_keep_left]).into();

    let mut left_summary = *left_summary;
    left_summary -= &add_to_right_summary;

    let mut right = add_to_right.to_owned();
    right.push_str(old_right);

    let mut right_summary = *right_summary;
    right_summary += &add_to_right_summary;

    ((left.to_owned(), left_summary), (right, right_summary))
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
fn ends_in_cr(s: &str) -> bool {
    s.as_bytes()[s.len() - 1] == b'\r'
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
#[inline]
pub(super) fn last_byte_is_newline(s: &str) -> bool {
    !s.is_empty() && s.as_bytes()[s.len() - 1] == b'\n'
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
    text: &'a str,
) -> (&'a str, &'a str) {
    if current.len() >= RopeChunk::max_bytes() {
        // If the current text is already longer than `RopeChunk::max_bytes()`
        // the only edge case to consider is not splitting CRLF pairs.
        if ends_in_cr(current) && !text.is_empty() && starts_with_lf(text) {
            return (&text[0..1], &text[1..]);
        } else {
            return ("", text);
        }
    }

    let mut bytes_to_add = RopeChunk::max_bytes() - current.len();

    if text.len() <= bytes_to_add {
        return (text, "");
    }

    while !text.is_char_boundary(bytes_to_add) {
        bytes_to_add += 1;
    }

    // Add one more byte if we're splitting a CRLF pair.
    if ends_in_cr(&text[..bytes_to_add])
        && !text[bytes_to_add..].is_empty()
        && starts_with_lf(&text[bytes_to_add..])
    {
        bytes_to_add += 1;
    }

    (&text[..bytes_to_add], &text[bytes_to_add..])
}

/// TODO: docs
#[inline]
pub(super) fn tree_slice_remove_trailing_line_break(
    slice: &mut TreeSlice<'_, { Rope::fanout() }, RopeChunk>,
) {
    debug_assert!(matches!(slice.summary().line_breaks, 0 | 1));

    if slice.summary().line_breaks == 0 {
        return;
    }

    use std::ops::Deref;

    match slice.end_slice().deref() {
        "\r\n" => {
            *slice = todo!();
        },

        "\n" => {
            *slice = todo!();
        },

        _ => {
            todo!();
        },
    }

    debug_assert_eq!(slice.summary().line_breaks, 0);
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

/// Returns `true` if the first byte in the string slice is a line feed.
///
/// # Panics
///
/// This function will panic if the string slice is empty.
fn starts_with_lf(s: &str) -> bool {
    s.as_bytes()[0] == b'\n'
}
