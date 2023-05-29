//! This module contains utility functions on strings and code to be shared
//! between `Rope`s and `RopeSlice`s, `RopeChunk`s and `ChunkSlice`s.

use super::iterators::Chunks;

/// Adjusts the candidate byte offset to make sure it's a char boundary for
/// `s`. Offsets past the end of the string will be clipped to the length of
/// the string.
///
/// If the initial candidate is not on a char boundary we can either go left or
/// right until it is. The direction is chosen based on the value of
/// `WITH_RIGHT_BIAS`: true => go right, false => go left.
///
/// In every case the adjusted split point will be within ± 3 bytes from the
/// initial candidate.
#[inline]
pub(super) fn adjust_split_point<const WITH_RIGHT_BIAS: bool>(
    s: &str,
    candidate: usize,
) -> usize {
    if candidate >= s.len() {
        return s.len();
    }

    let mut offset = candidate;

    if WITH_RIGHT_BIAS {
        while !s.is_char_boundary(offset) {
            offset += 1;
        }
    } else {
        while !s.is_char_boundary(offset) {
            offset -= 1;
        }
    }

    offset
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

/// Checks equality between the chunks yielded by iterating over a [`Chunks`]
/// and a string slice.
///
/// This is used in the `PartialEq` implementation between `Rope`/`RopeSlice`s
/// and strings. It's assumed that if we get this far `chunks` and `s` have the
/// same number of bytes.
#[inline]
pub(super) fn chunks_eq_str(chunks: Chunks<'_>, s: &str) -> bool {
    let s = s.as_bytes();
    let mut checked = 0;
    for chunk in chunks {
        if chunk.as_bytes() != &s[checked..(checked + chunk.len())] {
            return false;
        }
        checked += chunk.len();
    }
    true
}

/// Iterates over the string slices yielded by [`Chunks`], writing the debug
/// output of each chunk to a formatter.
#[inline]
pub(super) fn debug_chunks(
    chunks: Chunks<'_>,
    f: &mut core::fmt::Formatter<'_>,
) -> core::fmt::Result {
    for chunk in chunks {
        debug_no_quotes(chunk, f)?;
    }

    Ok(())
}

/// Writes the `Debug` output of the given string to the formatter without
/// enclosing it in double quotes.
pub(super) fn debug_no_quotes(
    s: &str,
    f: &mut core::fmt::Formatter<'_>,
) -> core::fmt::Result {
    use core::fmt::Write;

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

    // Iterate from the back until we reach the chunk containing the given byte
    // index.
    //
    // TODO: we need something like `Rope{Slice}::chunks_{from,up_to}_byte()`
    // if we want to make this fast.
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

#[inline]
pub(super) fn split_adjusted<const WITH_RIGHT_BIAS: bool>(
    s: &str,
    candidate: usize,
) -> (&str, &str) {
    let split_point = adjust_split_point::<WITH_RIGHT_BIAS>(s, candidate);
    (&s[..split_point], &s[split_point..])
}

pub mod panic_messages {
    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn byte_index_out_of_bounds(
        byte_index: usize,
        byte_len: usize,
    ) -> ! {
        debug_assert!(byte_index >= byte_len);

        panic!(
            "byte index out of bounds: the index is {byte_index} but the \
             length is {byte_len}"
        );
    }

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

        let mut start = byte_offset;
        while !s.is_char_boundary(start) {
            start -= 1;
        }

        let mut end = byte_offset;
        while !s.is_char_boundary(end) {
            end += 1;
        }

        let splitting_char = s[start..end].chars().next().unwrap();

        panic!(
            "byte offset {byte_offset} is not a char boundary: it is inside \
             {splitting_char:?} (bytes {start}..{end}) of {s:?}"
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
            "byte offset out of bounds: the offset is {byte_offset} but the \
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
            "byte start after end: the start is {byte_start} but the end is \
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
            "line index out of bounds: the index is {line_index} but the \
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
            "line offset out of bounds: the offset is {line_offset} but the \
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
            "line start after end: the start is {line_start} but the end is \
             {line_end}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn utf16_offset_out_of_bounds(
        utf16_offset: usize,
        utf16_len: usize,
    ) -> ! {
        debug_assert!(utf16_offset > utf16_len);

        panic!(
            "UTF-16 offset out of bounds: the offset is {utf16_offset} but \
             the length is {utf16_len}"
        );
    }

    #[track_caller]
    #[cold]
    #[inline(never)]
    pub(crate) fn utf16_start_after_end(
        utf16_start: usize,
        utf16_end: usize,
    ) -> ! {
        debug_assert!(utf16_start > utf16_end);

        panic!(
            "UTF-16 offset start after end: the start is {utf16_start} but \
             the end is {utf16_end}"
        );
    }
}
