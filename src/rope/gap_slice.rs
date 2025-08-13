use super::gap_buffer::GapBuffer;
use super::metrics::{ChunkSummary, SummaryUpTo, ToByteOffset};
use super::utils::{debug_no_quotes, panic_messages as panic};
use crate::tree::{LeafSlice, Metric};

/// A slice of a [`GapBuffer`](super::gap_buffer::GapBuffer).
#[derive(Copy, Clone, Default)]
pub struct GapSlice<'a> {
    pub(super) bytes: &'a [u8],
    pub(super) left_summary: ChunkSummary,
    pub(super) right_summary: ChunkSummary,
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
                panic::byte_offset_not_char_boundary(
                    self.left_chunk(),
                    byte_offset,
                )
            } else {
                panic::byte_offset_not_char_boundary(
                    self.right_chunk(),
                    byte_offset - self.len_left(),
                )
            }
        }
    }

    pub(super) fn assert_invariants(&self) {
        assert_eq!(self.left_summary, ChunkSummary::from(self.left_chunk()));

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

    #[inline]
    fn left_measure<M>(&self) -> M
    where
        M: Metric<ChunkSummary>,
    {
        M::measure(&self.left_summary)
    }

    #[inline]
    pub(super) fn truncate_last_char(&mut self) -> ChunkSummary {
        debug_assert!(self.len() > 0);

        use core::cmp::Ordering;

        let last_char = self
            .last_chunk()
            .chars()
            .next_back()
            .expect("this slice isn't empty");

        let removed_summary = ChunkSummary::from(last_char);

        let len_utf8 = removed_summary.bytes();

        match self.len_right().cmp(&len_utf8) {
            // The slice doesn't have a right chunk, so we shorten the left
            // chunk.
            Ordering::Less => {
                self.left_summary -= removed_summary;
                self.bytes = &self.bytes[..self.len_left()];
            },

            // The right chunk has 2 or more characters, so we shorten the right
            // chunk.
            Ordering::Greater => {
                self.right_summary -= removed_summary;
                self.bytes = &self.bytes[..self.bytes.len() - len_utf8];
            },

            // The right chunk has exactly 1 character, so we can keep just the
            // left chunk.
            Ordering::Equal => {
                self.right_summary = ChunkSummary::new();
                self.bytes = &self.bytes[..self.len_left()];
            },
        }

        removed_summary
    }

    /// Removes the trailing line break (if it has one), returning the summary
    /// of what was removed.
    #[inline]
    pub(super) fn truncate_trailing_line_break(&mut self) -> ChunkSummary {
        if !self.has_trailing_newline() {
            return ChunkSummary::new();
        }

        let mut removed_summary = self.truncate_last_char();

        if self.last_chunk().ends_with('\r') {
            removed_summary += self.truncate_last_char()
        }

        removed_summary
    }

    #[inline]
    pub(super) fn empty() -> Self {
        Self::default()
    }

    /// Returns `true` if it ends with a newline.
    #[inline]
    pub(super) fn has_trailing_newline(&self) -> bool {
        self.last_chunk().ends_with('\n')
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
        if self.len_right() == 0 {
            self.left_chunk()
        } else {
            self.right_chunk()
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
        self.left_summary.bytes()
    }

    #[inline]
    pub(super) fn len_right(&self) -> usize {
        self.right_summary.bytes()
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

    /// Splits the slice at the given offset, returning the left and right
    /// slices.
    ///
    /// # Panics
    ///
    /// Panics if the offset is greater than the M-measure of the slice.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let gap_buffer = GapBuffer::<20>::from("foo\nbar\r\nbaz");
    ///
    /// let (left, right) =
    ///     gap_buffer.as_slice().split_at_offset(RawLineMetric(1));
    ///
    /// assert_eq!("foo\n", left);
    ///
    /// assert_eq!("bar\r\nbaz", right);
    /// ```
    #[track_caller]
    #[inline]
    pub fn split_at_offset<M>(&self, mut offset: M) -> (Self, Self)
    where
        M: Metric<ChunkSummary> + ToByteOffset + SummaryUpTo,
    {
        debug_assert!(offset <= self.measure::<M>());

        if offset <= self.left_measure::<M>() {
            let byte_offset: usize = offset.to_byte_offset(self.left_chunk());

            let (bytes_left, bytes_right) = self.split_bytes(byte_offset);

            let left_left_summary = M::up_to(
                self.left_chunk(),
                self.left_summary,
                offset,
                byte_offset,
            );

            let left = Self {
                bytes: bytes_left,
                left_summary: left_left_summary,
                right_summary: ChunkSummary::new(),
            };

            let right = Self {
                bytes: bytes_right,
                left_summary: self.left_summary - left_left_summary,
                right_summary: self.right_summary,
            };

            (left, right)
        } else {
            offset -= self.left_measure::<M>();

            let byte_offset = offset.to_byte_offset(self.right_chunk());

            let (bytes_left, bytes_right) =
                self.split_bytes(self.len_left() + byte_offset);

            let right_left_summary = M::up_to(
                self.right_chunk(),
                self.right_summary,
                offset,
                byte_offset,
            );

            let left = Self {
                bytes: bytes_left,
                left_summary: self.left_summary,
                right_summary: right_left_summary,
            };

            let right = Self {
                bytes: bytes_right,
                left_summary: self.right_summary - right_left_summary,
                right_summary: ChunkSummary::new(),
            };

            (left, right)
        }
    }

    #[inline]
    fn split_bytes(&self, byte_offset: usize) -> (&'a [u8], &'a [u8]) {
        debug_assert!(byte_offset <= self.len());

        use core::cmp::Ordering;

        let offset = match byte_offset.cmp(&self.len_left()) {
            Ordering::Less => byte_offset,

            Ordering::Greater => byte_offset + self.len_gap(),

            Ordering::Equal => {
                return (
                    self.left_chunk().as_bytes(),
                    self.right_chunk().as_bytes(),
                );
            },
        };

        self.bytes.split_at(offset)
    }
}

impl<'a> LeafSlice<'a> for GapSlice<'a> {
    type Leaf = GapBuffer;

    #[inline]
    fn summarize(&self) -> ChunkSummary {
        self.right_summary + self.left_summary
    }
}

#[cfg(all(test, feature = "small_chunks"))]
mod tests {
    use crate::rope::gap_buffer::GapBuffer;
    use crate::tree::Leaf;

    #[test]
    fn debug_slice() {
        let buffer = GapBuffer::from("Hi");
        assert_eq!("\"H~~i\"", format!("{:?}", buffer.as_slice()));
    }

    #[test]
    fn truncate_trailing_crlf() {
        let buffer = GapBuffer::from("ba\r\n");
        let mut slice = buffer.as_slice();
        slice.truncate_trailing_line_break();
        assert_eq!("aa", slice);
    }

    #[test]
    fn truncate_trailing_lf() {
        let buffer = GapBuffer::from("bar\n");
        let mut slice = buffer.as_slice();
        slice.truncate_trailing_line_break();
        assert_eq!("bar", slice);
    }
}
