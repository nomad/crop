//! This module contains utility functions on strings and code to be shared
//! between `Rope`s and `RopeSlice`s, `RopeChunk`s and `ChunkSlice`s.

use std::fmt::Write;

use super::iterators::Chunks;

/// Adjusts the candidate byte offset to make sure it's a valid split point for
/// `s`, i.e. it makes sure that it lies on a char boundary and that it doesn't
/// split a CRLF pair. Offsets past the end of the string will be clipped to
/// the length of the string.
///
/// If the initial candidate is not a valid split position we can either go
/// left or right until is it. The direction is chosen based on the value of
/// `WITH_RIGHT_BIAS`: true -> go right, false -> go left.
///
/// In every case the adjusted split point will be within ± 3 bytes from the
/// input candidate.
#[inline]
pub(super) fn adjust_split_point<const WITH_RIGHT_BIAS: bool>(
    s: &str,
    mut candidate: usize,
) -> usize {
    if candidate >= s.len() {
        return s.len();
    }

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

#[inline]
pub(super) fn count_line_breaks(s: &str) -> usize {
    str_indices::lines_lf::count_breaks(s)
}

#[inline]
pub(super) fn byte_of_line(s: &str, line: usize) -> usize {
    str_indices::lines_lf::to_byte_idx(s, line)
}

#[inline]
pub(super) fn split_adjusted<const WITH_RIGHT_BIAS: bool>(
    s: &str,
    candidate: usize,
) -> (&str, &str) {
    let split_point = adjust_split_point::<WITH_RIGHT_BIAS>(s, candidate);
    (&s[..split_point], &s[split_point..])
}

/// Returns the number of bytes that `s`'s trailing line break takes up.
///
/// NOTE: this function assumes that `s` ends with a newline, if it doesn't
/// it will return a wrong result.
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

/// Writes the `Debug` output of the given string to the formatter without
/// enclosing it in double quotes.
pub(super) fn debug_no_quotes(
    s: &str,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let mut written = 0;

    for (idx, char) in s.char_indices() {
        let escape = char.escape_debug();
        if escape.len() != 1 {
            f.write_str(&s[written..idx])?;
            for c in escape {
                f.write_char(c)?;
            }
            written = idx + char.len_utf8();
        }
    }

    f.write_str(&s[written..])
}

/// Iterates over the string slices yielded by [`Chunks`], writing the debug
/// output of each chunk to a formatter.
#[inline]
pub(super) fn debug_chunks(
    chunks: Chunks<'_>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    for chunk in chunks {
        debug_no_quotes(chunk, f)?;
    }

    Ok(())
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

/// Returns whether `byte_offset` sits between a CRLF pair in `s`.
#[inline]
pub(super) fn is_splitting_crlf_pair(s: &str, byte_offset: usize) -> bool {
    byte_offset > 0
        && byte_offset < s.len()
        && ({
            let s = s.as_bytes();
            s[byte_offset - 1] == b'\r' && s[byte_offset] == b'\n'
        })
}

/// Returns whether the last byte of the string is a newline (0x0A).
#[inline]
pub(super) fn last_byte_is_newline(s: &str) -> bool {
    !s.is_empty() && s.as_bytes()[s.len() - 1] == b'\n'
}

pub(super) use panic_messages::*;

mod panic_messages {
    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn byte_offset_not_char_boundary(
        s: &str,
        byte_offset: usize,
    ) -> ! {
        debug_assert!(byte_offset <= s.len());
        debug_assert!(!s.is_char_boundary(byte_offset));

        // TODO: use `floor_char_boundary()` and `ceil_char_boundary()`
        // once they get stabilized.

        let mut start_char = byte_offset;
        while !s.is_char_boundary(start_char) {
            start_char -= 1;
        }

        let mut end_char = byte_offset;
        while !s.is_char_boundary(end_char) {
            end_char += 1;
        }

        let splitting_char = s[start_char..end_char].chars().next().unwrap();

        panic!(
            "byte offset {byte_offset} is not a char boundary: it is inside \
             {splitting_char:?} (bytes {start_char}..{end_char}) of {s:?}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn byte_index_out_of_bounds(
        byte_index: usize,
        byte_len: usize,
    ) -> ! {
        debug_assert!(byte_index >= byte_len);

        panic!(
            "Byte index out of bounds: the index is {byte_index} but the \
             length is {byte_len}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn byte_offset_out_of_bounds(
        byte_offset: usize,
        byte_len: usize,
    ) -> ! {
        debug_assert!(byte_offset > byte_len);

        panic!(
            "Byte offset out of bounds: the offset is {byte_offset} but the \
             length is {byte_len}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn byte_start_after_end(
        byte_start: usize,
        byte_end: usize,
    ) -> ! {
        debug_assert!(byte_start > byte_end);

        panic!(
            "Byte start after end: the start is {byte_start} but the end is \
             {byte_end}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn line_index_out_of_bounds(
        line_index: usize,
        line_len: usize,
    ) -> ! {
        debug_assert!(line_index >= line_len);

        panic!(
            "Line index out of bounds: the index is {line_index} but the \
             length is {line_len}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn line_offset_out_of_bounds(
        line_offset: usize,
        line_len: usize,
    ) -> ! {
        debug_assert!(line_offset > line_len);

        panic!(
            "Line offset out of bounds: the offset is {line_offset} but the \
             length is {line_len}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn line_start_after_end(
        line_start: usize,
        line_end: usize,
    ) -> ! {
        debug_assert!(line_start > line_end);

        panic!(
            "Line start after end: the start is {line_start} but the end is \
             {line_end}"
        );
    }
}
