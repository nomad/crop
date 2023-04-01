use super::gap_buffer::ChunkSummary;
use super::utils::*;
use crate::tree::Summarize;

/// A slice of a [`GapBuffer`](super::gap_buffer::GapBuffer).
#[derive(Copy, Clone, Default)]
pub struct GapSlice<'a> {
    pub(super) bytes: &'a [u8],
    pub(super) len_left: u16,
    pub(super) line_breaks_left: u16,
    pub(super) len_right: u16,
}

impl core::fmt::Debug for GapSlice<'_> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_str("\"")?;
        debug_no_quotes(self.left_chunk(), f)?;
        write!(f, "{:~^1$}", "", self.len_gap())?;
        debug_no_quotes(self.right_chunk(), f)?;
        f.write_str("\"")
    }
}

// We only need this to compare `GapSlice`s with `&str`s in (doc)tests.
impl PartialEq<GapSlice<'_>> for &str {
    fn eq(&self, rhs: &GapSlice<'_>) -> bool {
        self.len() == rhs.len()
            && rhs.left_chunk() == &self[..rhs.len_left()]
            && rhs.right_chunk() == &self[rhs.len_left()..]
    }
}

impl<'a> GapSlice<'a> {
    /// Panics with a nicely formatted error message if the given byte offset
    /// is not a character boundary.
    #[track_caller]
    #[inline]
    pub(super) fn assert_char_boundary(&self, byte_offset: usize) {
        debug_assert!(byte_offset <= self.len());

        if !self.is_char_boundary(byte_offset) {
            if byte_offset < self.len_left() {
                byte_offset_not_char_boundary(self.left_chunk(), byte_offset)
            } else {
                byte_offset_not_char_boundary(
                    self.right_chunk(),
                    byte_offset - self.len_left(),
                )
            }
        }
    }

    pub(super) fn assert_invariants(&self) {
        assert_eq!(
            self.line_breaks_left,
            count_line_breaks(self.left_chunk()) as u16
        );

        if self.len_right() == 0 {
            assert_eq!(self.len_left(), self.bytes.len());
        } else if self.len_left() == 0 {
            assert_eq!(self.len_right(), self.bytes.len());
        }
    }

    /// Returns the byte at the given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds, i.e. greater than or equal to
    /// [`len()`](Self::len()).
    #[inline]
    pub(super) fn byte(&self, byte_index: usize) -> u8 {
        debug_assert!(byte_index < self.len());

        if byte_index < self.len_left() {
            self.left_chunk().as_bytes()[byte_index]
        } else {
            self.right_chunk().as_bytes()[byte_index - self.len_left()]
        }
    }

    /// Removes the trailing line break (if it has one), returning the number
    /// of bytes that were removed: 0 if there was no trailing line break, 1
    /// if it was a LF, or 2 if it was a CRLF.
    #[inline]
    pub(super) fn truncate_trailing_line_break(&mut self) -> usize {
        if !self.has_trailing_newline() {
            0
        } else if self.len_right() > 0 {
            let bytes_line_break = bytes_line_break(self.right_chunk());

            // Check if the right chunk only contained a trailing line break.
            // This only checks for LF and CRLF.
            if self.len_right == bytes_line_break as u16 {
                self.len_right = 0;

                // Check if the right chunk only contained a '\n' and the left
                // chunk contains a trailing CR.
                if bytes_line_break == 1
                    && self.len_left() > 0
                    && self.left_chunk().as_bytes()[self.len_left() - 1]
                        == b'\r'
                {
                    self.bytes = &self.bytes[..self.len_left() - 1];
                    self.len_left -= 1;
                    2
                } else {
                    self.bytes = &self.bytes[..self.len_left()];
                    bytes_line_break
                }
            } else {
                self.len_right -= bytes_line_break as u16;
                self.bytes =
                    &self.bytes[..self.bytes.len() - bytes_line_break];
                bytes_line_break
            }
        } else {
            let bytes_line_break = bytes_line_break(self.left_chunk());
            self.len_left -= bytes_line_break as u16;
            self.bytes = &self.bytes[..self.bytes.len() - bytes_line_break];
            self.line_breaks_left -= 1;
            bytes_line_break
        }
    }

    #[inline]
    pub(super) fn empty() -> Self {
        Self::default()
    }

    /// Returns `true` if it ends with a newline (either LF or CRLF).
    #[inline]
    pub(super) fn has_trailing_newline(&self) -> bool {
        last_byte_is_newline(self.last_chunk())
    }

    #[inline]
    pub(super) fn is_char_boundary(&self, byte_offset: usize) -> bool {
        debug_assert!(byte_offset <= self.len());

        if byte_offset <= self.len_left() {
            self.left_chunk().is_char_boundary(byte_offset)
        } else {
            self.right_chunk().is_char_boundary(byte_offset - self.len_left())
        }
    }

    /// The second segment if it's not empty, or the first one otherwise.
    #[inline]
    pub(super) fn last_chunk(&self) -> &'a str {
        if !self.right_chunk().is_empty() {
            self.right_chunk()
        } else {
            self.left_chunk()
        }
    }

    #[inline]
    pub(super) fn left_chunk(&self) -> &'a str {
        // SAFETY: the first `len_left` bytes are valid UTF-8.
        unsafe {
            core::str::from_utf8_unchecked(&self.bytes[..self.len_left()])
        }
    }

    #[inline]
    pub(super) fn len(&self) -> usize {
        self.len_left() + self.len_right()
    }

    #[inline]
    pub(super) fn len_gap(&self) -> usize {
        self.bytes.len() - self.len()
    }

    #[inline]
    pub(super) fn len_left(&self) -> usize {
        self.len_left as _
    }

    #[inline]
    pub(super) fn len_right(&self) -> usize {
        self.len_right as _
    }

    #[inline]
    pub(super) fn right_chunk(&self) -> &'a str {
        // SAFETY: the last `len_right` bytes are valid UTF-8.
        unsafe {
            core::str::from_utf8_unchecked(
                &self.bytes[self.bytes.len() - self.len_right()..],
            )
        }
    }

    /// Splits the slice at the given line offset, returning the left and right
    /// slices.
    ///
    /// # Panics
    ///
    /// Panics if the line offset is greater than the number of line breaks in
    /// the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// # use crop::tree::AsSlice;
    /// let gap_buffer = GapBuffer::<20>::from("foo\nbar\r\nbaz");
    ///
    /// let (left, right) = gap_buffer.as_slice().split_at_line(1);
    /// assert_eq!("foo\n", left);
    /// assert_eq!("bar\r\nbaz", right);
    /// ```
    #[inline]
    pub fn split_at_line(&self, line_offset: usize) -> (Self, Self) {
        debug_assert!(line_offset <= self.summarize().line_breaks);

        if line_offset <= self.line_breaks_left as usize {
            let byte_offset = byte_of_line(self.left_chunk(), line_offset);

            let (bytes_left, bytes_right) = if byte_offset != self.len_left() {
                (&self.bytes[..byte_offset], &self.bytes[byte_offset..])
            } else {
                (
                    (&self.bytes[..self.len_left()]),
                    (&self.bytes[self.bytes.len() - self.len_right()..]),
                )
            };

            let left = Self {
                bytes: bytes_left,
                len_left: byte_offset as u16,
                line_breaks_left: line_offset as u16,
                len_right: 0,
            };

            let right = Self {
                bytes: bytes_right,
                len_left: self.len_left - left.len_left,
                line_breaks_left: self.line_breaks_left - line_offset as u16,
                len_right: self.len_right,
            };

            (left, right)
        } else {
            let byte_offset = byte_of_line(
                self.right_chunk(),
                line_offset - self.line_breaks_left as usize,
            );

            let split_point =
                self.bytes.len() - self.len_right() + byte_offset;

            let left = Self {
                bytes: &self.bytes[..split_point],
                len_left: self.len_left,
                line_breaks_left: self.line_breaks_left,
                len_right: byte_offset as u16,
            };

            let right = Self {
                bytes: &self.bytes[split_point..],
                len_left: 0,
                line_breaks_left: 0,
                len_right: self.len_right - left.len_right,
            };

            (left, right)
        }
    }
}

impl Summarize for GapSlice<'_> {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        let line_breaks = self.line_breaks_left as usize
            + count_line_breaks(self.right_chunk());

        ChunkSummary { bytes: self.len(), line_breaks }
    }
}

#[cfg(test)]
mod tests {
    use crate::rope::gap_buffer::GapBuffer;
    use crate::tree::AsSlice;

    #[test]
    fn debug_slice() {
        let buffer = GapBuffer::<10>::from("Hello");
        assert_eq!("\"He~~~~~llo\"", format!("{:?}", buffer.as_slice()));
    }
}
