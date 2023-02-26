use std::ops::RangeBounds;

use super::iterators::{Bytes, Chars, Chunks, Lines, RawLines};
use super::metrics::{ByteMetric, RawLineMetric};
use super::rope_chunk::RopeChunk;
use super::utils::*;
use super::Rope;
use crate::range_bounds_to_start_end;
use crate::tree::TreeSlice;

/// An immutable slice of a [`Rope`](crate::Rope).
#[derive(Copy, Clone)]
pub struct RopeSlice<'a> {
    pub(super) tree_slice: TreeSlice<'a, { Rope::fanout() }, RopeChunk>,
    pub(super) has_trailing_newline: bool,
}

impl<'a> RopeSlice<'a> {
    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        self.tree_slice.assert_invariants();

        let last = self.tree_slice.end_slice();

        assert_eq!(self.has_trailing_newline, last_byte_is_newline(last))
    }

    /// Returns the byte at `byte_index`.
    ///
    /// # Panics
    ///
    /// Panics if the byte index is out of bounds (i.e. greater than or equal
    /// to [`byte_len()`](Self::byte_len())).
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("bar");
    /// let s = r.byte_slice(..);
    ///
    /// assert_eq!(s.byte(0), b'b');
    /// assert_eq!(s.byte(1), b'a');
    /// assert_eq!(s.byte(2), b'r');
    /// ```
    #[inline]
    pub fn byte(&self, byte_index: usize) -> u8 {
        if byte_index >= self.byte_len() {
            byte_index_out_of_bounds(byte_index, self.byte_len());
        }

        let (chunk, ByteMetric(chunk_byte_offset)) =
            self.tree_slice.leaf_at_measure(ByteMetric(byte_index + 1));

        chunk.as_bytes()[byte_index - chunk_byte_offset]
    }

    /// Returns the length of the `RopeSlice` in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("ƒoo");
    ///
    /// let s = r.byte_slice(2..2);
    /// assert_eq!(s.byte_len(), 0);
    ///
    /// let s = r.byte_slice(..);
    /// assert_eq!(s.byte_len(), 4);
    /// ```
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.tree_slice.summary().bytes
    }

    /// Returns the byte offset of the start of the given line from the start
    /// of the `Rope`.
    ///
    /// # Panics
    ///
    /// Panics if the line index is out of bounds (i.e. greater than or equal
    /// to [`line_len()`](Self::line_len())).
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("ƒoo\nbär\r\nbaz");
    ///
    /// let s = r.byte_slice(..);
    /// assert_eq!(s.byte_of_line(0), 0);
    /// assert_eq!(s.byte_of_line(1), "ƒoo\n".len());
    ///
    /// let s = r.byte_slice("ƒoo\n".len()..);
    /// assert_eq!(s.byte_of_line(1), "bär\r\n".len());
    /// ```
    #[inline]
    pub fn byte_of_line(&self, line_index: usize) -> usize {
        if line_index >= self.line_len() {
            line_index_out_of_bounds(line_index, self.line_len());
        }

        let ByteMetric(byte_index) =
            self.tree_slice.convert_measure(RawLineMetric(line_index));

        byte_index
    }

    /// Returns a sub-slice of this `RopeSlice` in the specified byte range,
    /// where the start and end of the range are interpreted as offsets.
    ///
    /// # Panics
    ///
    /// Panics if the start or the end of the byte range don't lie on a code
    /// point boundary, if the start is greater than the end or if the end is
    /// out of bounds (i.e. greater than [`byte_len()`](Self::byte_len())).
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("🗻∈🌏");
    /// let s = r.byte_slice(4..);
    ///
    /// assert_eq!(s.byte_slice(..3), "∈");
    /// assert_eq!(s.byte_slice(3..), "🌏");
    /// ```
    #[inline]
    pub fn byte_slice<R>(self, byte_range: R) -> RopeSlice<'a>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) =
            range_bounds_to_start_end(byte_range, 0, self.byte_len());

        if start > end {
            byte_start_after_end(start, end);
        }

        if end > self.byte_len() {
            byte_offset_out_of_bounds(end, self.byte_len());
        }

        self.tree_slice.slice(ByteMetric(start)..ByteMetric(end)).into()
    }

    /// Returns an iterator over the bytes of this `RopeSlice`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("foobar");
    /// let s = r.byte_slice(1..5);
    ///
    /// let mut bytes = s.bytes();
    ///
    /// assert_eq!(Some(b'o'), bytes.next());
    /// assert_eq!(Some(b'o'), bytes.next());
    /// assert_eq!(Some(b'b'), bytes.next());
    /// assert_eq!(Some(b'a'), bytes.next());
    /// assert_eq!(None, bytes.next());
    /// ```
    #[inline]
    pub fn bytes(&'a self) -> Bytes<'a> {
        Bytes::from(self)
    }

    /// Returns an iterator over the [`char`]s of this `RopeSlice`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("🐻‍❄️");
    /// let s = r.byte_slice(4..);
    ///
    /// let mut chars = s.chars();
    ///
    /// assert_eq!(Some('\u{200d}'), chars.next());
    /// assert_eq!(Some('❄'), chars.next());
    /// assert_eq!(Some('\u{fe0f}'), chars.next());
    /// assert_eq!(None, chars.next());
    /// ```
    #[inline]
    pub fn chars(&'a self) -> Chars<'a> {
        Chars::from(self)
    }

    /// Returns an iterator over the chunks of this `RopeSlice`.
    #[inline]
    pub fn chunks(&'a self) -> Chunks<'a> {
        Chunks::from(self)
    }

    /// Returns an iterator over the extended grapheme clusters of this
    /// [`RopeSlice`].
    #[cfg(feature = "graphemes")]
    #[inline]
    pub fn graphemes(&'a self) -> crate::iter::Graphemes<'a> {
        crate::iter::Graphemes::from(self)
    }

    /// Returns `true` if the given byte offset lies on a [`char`] boundary.
    ///
    /// # Panics
    ///
    /// Panics if the byte offset is out of bounds (i.e. greater than
    /// [`byte_len()`](Self::byte_len())).
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("Löwe 老虎 Léopard");
    /// let s = r.byte_slice(3..);
    ///
    /// assert!(s.is_char_boundary(0));
    /// assert!(s.is_char_boundary(s.byte_len()));
    /// assert!(s.is_char_boundary(6)); // between '老' and '虎'
    /// assert!(!s.is_char_boundary(12)); // between the 1st and 2nd byte of 'é'
    /// ```
    #[inline]
    pub fn is_char_boundary(&self, byte_offset: usize) -> bool {
        if byte_offset > self.byte_len() {
            byte_offset_out_of_bounds(byte_offset, self.byte_len());
        }

        let (chunk, ByteMetric(chunk_byte_offset)) =
            self.tree_slice.leaf_at_measure(ByteMetric(byte_offset));

        chunk.is_char_boundary(byte_offset - chunk_byte_offset)
    }

    /// Returns `true` if the `RopeSlice`'s byte length is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("");
    /// assert!(r.byte_slice(..).is_empty());
    ///
    /// let r = Rope::from("foo");
    /// assert!(!r.line_slice(..).is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.byte_len() == 0
    }

    /// TODO: docs
    #[cfg(feature = "graphemes")]
    #[inline]
    pub fn is_grapheme_boundary(&self, byte_offset: usize) -> bool {
        if byte_offset > self.byte_len() {
            byte_offset_out_of_bounds(byte_offset, self.byte_len());
        }

        is_grapheme_boundary(self.chunks(), self.byte_len(), byte_offset)
    }

    /// TODO: docs
    #[inline]
    pub fn line(self, line_index: usize) -> RopeSlice<'a> {
        if line_index >= self.line_len() {
            line_index_out_of_bounds(line_index, self.line_len());
        }

        let mut tree_slice = self
            .tree_slice
            .slice(RawLineMetric(line_index)..RawLineMetric(line_index + 1));

        if tree_slice.summary().line_breaks == 1 {
            let byte_end = tree_slice.summary().bytes
                - bytes_line_break(tree_slice.end_slice());

            tree_slice = tree_slice.slice(ByteMetric(0)..ByteMetric(byte_end));
        }

        debug_assert_eq!(0, tree_slice.summary().line_breaks);

        Self { tree_slice, has_trailing_newline: false }
    }

    /// TODO: docs
    #[inline]
    pub fn line_len(&self) -> usize {
        self.tree_slice.summary().line_breaks + 1
            - (self.has_trailing_newline as usize)
            - (self.is_empty() as usize)
    }

    /// TODO: docs
    #[inline]
    pub fn line_of_byte(&self, byte_index: usize) -> usize {
        if byte_index >= self.byte_len() {
            byte_index_out_of_bounds(byte_index, self.byte_len());
        }

        let RawLineMetric(line_index) =
            self.tree_slice.convert_measure(ByteMetric(byte_index));

        line_index
    }

    /// TODO: docs
    #[inline]
    pub fn line_slice<R>(self, line_range: R) -> RopeSlice<'a>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) =
            range_bounds_to_start_end(line_range, 0, self.line_len());

        if start > end {
            line_start_after_end(start, end);
        }

        if end > self.line_len() {
            line_offset_out_of_bounds(end, self.line_len());
        }

        self.tree_slice.slice(RawLineMetric(start)..RawLineMetric(end)).into()
    }

    /// Returns an iterator over the lines of this [`RopeSlice`].
    #[inline]
    pub fn lines(&'a self) -> Lines<'a> {
        Lines::from(self)
    }

    /// TODO: docs.
    #[inline]
    pub fn raw_lines(&self) -> RawLines<'_> {
        RawLines::from(self)
    }
}

impl<'a> From<TreeSlice<'a, { Rope::fanout() }, RopeChunk>> for RopeSlice<'a> {
    #[inline]
    fn from(tree_slice: TreeSlice<'a, { Rope::fanout() }, RopeChunk>) -> Self {
        Self {
            has_trailing_newline: last_byte_is_newline(tree_slice.end_slice()),
            tree_slice,
        }
    }
}

impl std::fmt::Debug for RopeSlice<'_> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("RopeSlice(\"")?;
        debug_chunks(self.chunks(), f)?;
        f.write_str("\")")
    }
}

impl std::fmt::Display for RopeSlice<'_> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for chunk in self.chunks() {
            f.write_str(chunk)?;
        }
        Ok(())
    }
}

impl<'a, 'b> std::cmp::PartialEq<RopeSlice<'b>> for RopeSlice<'a> {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'b>) -> bool {
        (self.byte_len() == rhs.byte_len())
            && (self.line_len() == rhs.line_len())
            && chunks_eq_chunks(self.chunks(), rhs.chunks())
    }
}

impl std::cmp::PartialEq<Rope> for RopeSlice<'_> {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        rhs == self
    }
}

impl std::cmp::PartialEq<str> for RopeSlice<'_> {
    #[inline]
    fn eq(&self, rhs: &str) -> bool {
        (self.byte_len() == rhs.len()) && chunks_eq_str(self.chunks(), rhs)
    }
}

impl std::cmp::PartialEq<RopeSlice<'_>> for str {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'_>) -> bool {
        rhs == self
    }
}

impl<'a, 'b> std::cmp::PartialEq<&'b str> for RopeSlice<'a> {
    #[inline]
    fn eq(&self, rhs: &&'b str) -> bool {
        self == *rhs
    }
}

impl<'a, 'b> std::cmp::PartialEq<RopeSlice<'a>> for &'b str {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'a>) -> bool {
        rhs == self
    }
}

impl std::cmp::PartialEq<String> for RopeSlice<'_> {
    #[inline]
    fn eq(&self, rhs: &String) -> bool {
        self == &**rhs
    }
}

impl std::cmp::PartialEq<RopeSlice<'_>> for String {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'_>) -> bool {
        rhs == self
    }
}

impl<'a, 'b> std::cmp::PartialEq<std::borrow::Cow<'b, str>> for RopeSlice<'a> {
    #[inline]
    fn eq(&self, rhs: &std::borrow::Cow<'b, str>) -> bool {
        self == &**rhs
    }
}

impl<'a, 'b> std::cmp::PartialEq<RopeSlice<'a>> for std::borrow::Cow<'b, str> {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'a>) -> bool {
        rhs == self
    }
}

impl std::cmp::Eq for RopeSlice<'_> {}
