use std::ops::RangeBounds;

use super::chunk_slice::{ChunkSegmenter, ChunkSlice};
use super::iterators::{Bytes, Chars, Chunks, Lines, RawLines};
use super::metrics::{ByteMetric, RawLineMetric};
use super::rope_chunk::RopeChunk;
use super::utils::*;
use super::RopeSlice;
use crate::range_bounds_to_start_end;
use crate::tree::Tree;

#[cfg(all(any(test, feature = "fanout_4"), not(feature = "fanout_24")))]
const ROPE_FANOUT: usize = 4;

#[cfg(not(any(test, feature = "fanout_4", feature = "fanout_24")))]
const ROPE_FANOUT: usize = 8;

#[cfg(feature = "fanout_24")]
const ROPE_FANOUT: usize = 24;

/// A UTF-8 text rope.
#[derive(Clone, Default)]
pub struct Rope {
    pub(super) tree: Tree<{ Self::fanout() }, RopeChunk>,
    pub(super) has_trailing_newline: bool,
}

impl Rope {
    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        self.tree.assert_invariants();

        if let Some(last) = self.chunks().next_back() {
            assert_eq!(self.has_trailing_newline, last_byte_is_newline(last));
        }

        let mut chunks = self.chunks().peekable();

        if chunks.len() == 0 {
            return;
        } else if chunks.len() == 1 {
            let chunk = chunks.next().unwrap();
            assert!(chunk.len() <= RopeChunk::chunk_max());
            return;
        }

        while let Some(chunk) = chunks.next() {
            assert!(chunk.len() >= RopeChunk::chunk_min());
            assert!(chunk.len() <= RopeChunk::chunk_max());

            if ends_in_cr(chunk) {
                if let Some(next) = chunks.peek().copied() {
                    assert!(!starts_with_lf(next));
                }
            }
        }
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
    ///
    /// assert_eq!(r.byte(0), b'b');
    /// assert_eq!(r.byte(1), b'a');
    /// assert_eq!(r.byte(2), b'r');
    /// ```
    #[inline]
    pub fn byte(&self, byte_index: usize) -> u8 {
        if byte_index >= self.byte_len() {
            byte_index_out_of_bounds(byte_index, self.byte_len());
        }

        let (chunk, ByteMetric(chunk_byte_offset)) =
            self.tree.leaf_at_measure(ByteMetric(byte_index + 1));

        chunk.as_bytes()[byte_index - chunk_byte_offset]
    }

    /// Returns the length of the `Rope` in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("ƒoo");
    ///
    /// assert_eq!(r.byte_len(), 4);
    /// ```
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.tree.summary().bytes
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
    /// assert_eq!(r.byte_of_line(0), 0);
    /// assert_eq!(r.byte_of_line(1), "ƒoo\n".len());
    /// assert_eq!(r.byte_of_line(2), "ƒoo\nbär\r\n".len());
    /// ```
    #[inline]
    pub fn byte_of_line(&self, line_index: usize) -> usize {
        if line_index >= self.line_len() {
            line_index_out_of_bounds(line_index, self.line_len());
        }

        let ByteMetric(byte_index) =
            self.tree.convert_measure(RawLineMetric(line_index));

        byte_index
    }

    /// Returns an immutable slice of the `Rope` in the specified byte range,
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
    ///
    /// assert_eq!(r.byte_slice(..4), "🗻");
    /// assert_eq!(r.byte_slice(4..7), "∈");
    /// assert_eq!(r.byte_slice(7..), "🌏");
    /// ```
    #[inline]
    pub fn byte_slice<R>(&self, byte_range: R) -> RopeSlice<'_>
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

        self.tree.slice(ByteMetric(start)..ByteMetric(end)).into()
    }

    /// Returns an iterator over the bytes of this `Rope`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("foo");
    ///
    /// let mut bytes = r.bytes();
    ///
    /// assert_eq!(Some(b'f'), bytes.next());
    /// assert_eq!(Some(b'o'), bytes.next());
    /// assert_eq!(Some(b'o'), bytes.next());
    /// assert_eq!(None, bytes.next());
    /// ```
    #[inline]
    pub fn bytes(&self) -> Bytes<'_> {
        Bytes::from(self)
    }

    /// Returns an iterator over the [`char`]s of this `Rope`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let r = Rope::from("🐻‍❄️");
    ///
    /// let mut chars = r.chars();
    ///
    /// assert_eq!(Some('🐻'), chars.next());
    /// assert_eq!(Some('\u{200d}'), chars.next());
    /// assert_eq!(Some('❄'), chars.next());
    /// assert_eq!(Some('\u{fe0f}'), chars.next());
    /// assert_eq!(None, chars.next());
    /// ```
    #[inline]
    pub fn chars(&self) -> Chars<'_> {
        Chars::from(self)
    }

    /// Returns an iterator over the chunks of this [`Rope`].
    #[inline]
    pub fn chunks(&self) -> Chunks<'_> {
        Chunks::from(self)
    }

    /// Deletes the contents of the `Rope` within the specified byte range,
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
    /// let mut r = Rope::from("Hello Earth 🌎!");
    ///
    /// r.delete(5..16);
    /// assert_eq!(r, "Hello!");
    /// ```
    #[inline]
    pub fn delete<R>(&mut self, byte_range: R)
    where
        R: RangeBounds<usize>,
    {
        self.replace(byte_range, "");
    }

    pub(super) const fn fanout() -> usize {
        ROPE_FANOUT
    }

    /// Returns an iterator over the extended grapheme clusters of this
    /// [`Rope`].
    #[cfg(feature = "graphemes")]
    #[inline]
    pub fn graphemes(&self) -> crate::iter::Graphemes<'_> {
        crate::iter::Graphemes::from(self)
    }

    /// Inserts `text` in the `Rope` at the given byte offset.
    ///
    /// # Panics
    ///
    /// Panics if the byte offset doesn't lie on a code point boundary or if
    /// it's out of bounds (i.e. greater than
    /// [`byte_len()`](Self::byte_len())).
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let mut r = Rope::from("Hello Earth!");
    ///
    /// r.insert(11, " 🌎");
    /// assert_eq!(r, "Hello Earth 🌎!");
    /// ```
    #[inline]
    pub fn insert<T>(&mut self, byte_offset: usize, text: T)
    where
        T: AsRef<str>,
    {
        self.replace(byte_offset..byte_offset, text)
    }

    /// TODO: docs
    #[inline]
    pub fn is_char_boundary(&self, byte_offset: usize) -> bool {
        if byte_offset > self.byte_len() {
            byte_offset_out_of_bounds(byte_offset, self.byte_len());
        }

        let (chunk, ByteMetric(chunk_byte_offset)) =
            self.tree.leaf_at_measure(ByteMetric(byte_offset));

        chunk.is_char_boundary(byte_offset - chunk_byte_offset)
    }

    /// Returns `true` if the `Rope`'s byte length is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::Rope;
    /// #
    /// let mut r = Rope::new();
    /// assert!(r.is_empty());
    ///
    /// r.insert(0, "hey");
    /// assert!(!r.is_empty());
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
    pub fn line(&self, line_index: usize) -> RopeSlice<'_> {
        if line_index >= self.line_len() {
            line_index_out_of_bounds(line_index, self.line_len());
        }

        let mut tree_slice = self
            .tree
            .slice(RawLineMetric(line_index)..RawLineMetric(line_index + 1));

        if tree_slice.summary().line_breaks == 1 {
            let byte_end = tree_slice.summary().bytes
                - bytes_line_break(tree_slice.end_slice());

            tree_slice = tree_slice.slice(ByteMetric(0)..ByteMetric(byte_end));
        }

        debug_assert_eq!(0, tree_slice.summary().line_breaks);

        RopeSlice { tree_slice, has_trailing_newline: false }
    }

    /// TODO: docs
    #[inline]
    pub fn line_len(&self) -> usize {
        self.tree.summary().line_breaks + 1
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
            self.tree.convert_measure(ByteMetric(byte_index));

        line_index
    }

    /// TODO: docs
    #[inline]
    pub fn line_slice<R>(&self, line_range: R) -> RopeSlice<'_>
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

        self.tree.slice(RawLineMetric(start)..RawLineMetric(end)).into()
    }

    /// Returns an iterator over the lines of this [`Rope`].
    #[inline]
    pub fn lines(&self) -> Lines<'_> {
        Lines::from(self)
    }

    /// TODO: docs.
    #[inline]
    pub fn raw_lines(&self) -> RawLines<'_> {
        RawLines::from(self)
    }

    /// Returns a new empty [`Rope`].
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Replaces the contents of the `Rope` within the specified byte range
    /// with the given string, where the start and end of the range are
    /// interpreted as byte offsets.
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
    /// let mut r = Rope::from("Hello Earth 🌎!");
    ///
    /// r.replace(6..16, "Saturn 🪐");
    /// assert_eq!(r, "Hello Saturn 🪐!");
    /// ```
    #[inline]
    pub fn replace<R, T>(&mut self, byte_range: R, text: T)
    where
        R: RangeBounds<usize>,
        T: AsRef<str>,
    {
        let (start, end) =
            range_bounds_to_start_end(byte_range, 0, self.byte_len());

        if start > end {
            byte_start_after_end(start, end);
        }

        if end > self.byte_len() {
            byte_offset_out_of_bounds(end, self.line_len());
        }

        let text = text.as_ref();

        let mut update_trailing = false;

        if end == self.byte_len() {
            if !text.is_empty() {
                self.has_trailing_newline = last_byte_is_newline(text);
            } else if start == 0 {
                self.has_trailing_newline = false;
            } else {
                update_trailing = true;
            }
        }

        self.tree.replace(ByteMetric(start)..ByteMetric(end), text.into());

        if update_trailing {
            self.has_trailing_newline =
                last_byte_is_newline(self.chunks().next_back().unwrap());
        }

        #[cfg(debug_assertions)]
        self.assert_invariants();
    }
}

impl From<RopeSlice<'_>> for Rope {
    #[inline]
    fn from(rope_slice: RopeSlice<'_>) -> Rope {
        let rope = Self {
            has_trailing_newline: rope_slice.has_trailing_newline,
            tree: Tree::from(rope_slice.tree_slice),
        };

        #[cfg(debug_assertions)]
        rope.assert_invariants();

        rope
    }
}

impl std::fmt::Debug for Rope {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("Rope(\"")?;
        debug_chunks(self.chunks(), f)?;
        f.write_str("\")")
    }
}

impl std::fmt::Display for Rope {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for chunk in self.chunks() {
            f.write_str(chunk)?;
        }
        Ok(())
    }
}

impl From<&str> for Rope {
    #[inline]
    fn from(s: &str) -> Self {
        Rope {
            has_trailing_newline: last_byte_is_newline(s),

            tree: Tree::from_leaves(
                ChunkSegmenter::new(s).map(std::borrow::ToOwned::to_owned),
            ),
        }
    }
}

impl From<String> for Rope {
    #[inline]
    fn from(mut s: String) -> Self {
        // If the strings fits in a single chunk we can try to avoid a new
        // allocation.
        if s.len() <= RopeChunk::max_bytes()
            || <&ChunkSlice>::from(&*s)
                .split_adjusted::<true>(RopeChunk::max_bytes())
                .1
                .is_empty()
        {
            debug_assert!(s.len() <= RopeChunk::chunk_max());

            s.reserve_exact(RopeChunk::chunk_max() - s.len());

            Rope {
                has_trailing_newline: last_byte_is_newline(&s),
                tree: Tree::from_leaves([RopeChunk { text: s }]),
            }
        } else {
            Rope::from(&*s)
        }
    }
}

impl From<std::borrow::Cow<'_, str>> for Rope {
    #[inline]
    fn from(moo: std::borrow::Cow<'_, str>) -> Self {
        match moo {
            std::borrow::Cow::Owned(s) => Rope::from(s),
            std::borrow::Cow::Borrowed(s) => Rope::from(s),
        }
    }
}

impl std::str::FromStr for Rope {
    type Err = std::convert::Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s))
    }
}

impl std::cmp::PartialEq<Rope> for Rope {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        (self.byte_len() == rhs.byte_len())
            && (self.line_len() == rhs.line_len())
            && chunks_eq_chunks(self.chunks(), rhs.chunks())
    }
}

impl std::cmp::PartialEq<RopeSlice<'_>> for Rope {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'_>) -> bool {
        (self.byte_len() == rhs.byte_len())
            && (self.line_len() == rhs.line_len())
            && chunks_eq_chunks(self.chunks(), rhs.chunks())
    }
}

impl std::cmp::PartialEq<str> for Rope {
    #[inline]
    fn eq(&self, rhs: &str) -> bool {
        (self.byte_len() == rhs.len()) && chunks_eq_str(self.chunks(), rhs)
    }
}

impl std::cmp::PartialEq<Rope> for str {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        rhs == self
    }
}

impl std::cmp::PartialEq<&str> for Rope {
    #[inline]
    fn eq(&self, rhs: &&str) -> bool {
        self == *rhs
    }
}

impl std::cmp::PartialEq<Rope> for &str {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        rhs == self
    }
}

impl std::cmp::PartialEq<String> for Rope {
    #[inline]
    fn eq(&self, rhs: &String) -> bool {
        self == &**rhs
    }
}

impl std::cmp::PartialEq<Rope> for String {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        rhs == self
    }
}

impl std::cmp::PartialEq<std::borrow::Cow<'_, str>> for Rope {
    #[inline]
    fn eq(&self, rhs: &std::borrow::Cow<'_, str>) -> bool {
        self == &**rhs
    }
}

impl std::cmp::PartialEq<Rope> for std::borrow::Cow<'_, str> {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        rhs == self
    }
}

impl std::cmp::Eq for Rope {}
