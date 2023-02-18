use std::ops::RangeBounds;

use super::iterators::{Bytes, Chars, Chunks, Lines, RawLines};
use super::metrics::{ByteMetric, RawLineMetric};
use super::rope_chunk::{RopeChunk, RopeChunkIter};
use super::utils::*;
use crate::tree::Tree;
use crate::RopeSlice;

#[cfg(not(any(test, feature = "integration_tests")))]
const ROPE_FANOUT: usize = 8;

#[cfg(any(test, feature = "integration_tests"))]
const ROPE_FANOUT: usize = 4;

/// A UTF-8 text rope.
///
/// TODO: docs
#[derive(Clone, Default)]
pub struct Rope {
    pub(super) tree: Tree<{ Self::fanout() }, RopeChunk>,
    pub(super) last_byte_is_newline: bool,
}

impl Rope {
    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        self.tree.assert_invariants();

        let mut chunks = self.chunks().peekable();

        if chunks.len() == 0 {
            return;
        } else if chunks.len() == 1 {
            let chunk = chunks.next().unwrap();
            assert!(chunk.len() <= RopeChunk::chunk_max());
            return;
        }

        while let Some(chunk) = chunks.next() {
            // assert!(chunk.len() >= RopeChunk::chunk_min());
            assert!(chunk.len() <= RopeChunk::chunk_max());

            // if ends_in_cr(chunk) {
            if let Some(_next) = chunks.peek().copied() {
                // assert!(!starts_with_lf(next));
            }
            // }
        }
    }

    /// TODO: docs.
    #[inline]
    pub fn byte(&self, byte_index: usize) -> u8 {
        if byte_index >= self.byte_len() {
            panic!(
                "Trying to index past the end of the Rope: the byte length \
                 is {} but the byte index is {}",
                self.byte_len(),
                byte_index
            );
        }

        let (mut chunk, ByteMetric(mut chunk_byte_offset)) =
            self.tree.leaf_at_measure(ByteMetric(byte_index));

        if chunk.len() == byte_index - chunk_byte_offset {
            (chunk, ByteMetric(chunk_byte_offset)) =
                self.tree.leaf_at_measure(ByteMetric(byte_index + 1));
        }

        chunk.as_bytes()[byte_index - chunk_byte_offset]
    }

    /// TODO: docs
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.tree.summary().bytes
    }

    /// TODO: docs
    #[inline]
    pub fn byte_of_line(&self, line_index: usize) -> usize {
        if line_index >= self.line_len() {
            panic!(
                "Trying to index past the end of the Rope: the line length \
                 is {} but the line index is {}",
                self.line_len(),
                line_index
            );
        }

        let ByteMetric(byte_index) =
            self.tree.convert_measure(RawLineMetric(line_index));

        byte_index
    }

    /// TODO: docs
    #[inline]
    pub fn byte_slice<R>(&self, byte_range: R) -> RopeSlice<'_>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) =
            range_bounds_to_start_end(byte_range, 0, self.byte_len());

        if end > self.byte_len() {
            panic!(
                "Trying to slice past the end of the Rope: the byte length \
                 is {} but the end of the byte range is {}",
                self.byte_len(),
                end
            );
        }

        self.tree.slice(ByteMetric(start)..ByteMetric(end)).into()
    }

    /// Returns an iterator over the bytes of this [`Rope`].
    #[inline]
    pub fn bytes(&self) -> Bytes<'_> {
        Bytes::from(self)
    }

    /// Returns an iterator over the [`char`]s of this [`Rope`].
    #[inline]
    pub fn chars(&self) -> Chars<'_> {
        Chars::from(self)
    }

    /// Returns an iterator over the chunks of this [`Rope`].
    #[inline]
    pub fn chunks(&self) -> Chunks<'_> {
        Chunks::from(self)
    }

    /// TODO: docs
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

    /// TODO: docs
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
            panic!(
                "The given offset is past the end of the Rope: the byte \
                 length is {} but the byte offset is {}",
                self.byte_len(),
                byte_offset
            );
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
    /// use crop::Rope;
    ///
    /// let r = Rope::from("");
    /// assert!(r.is_empty());
    ///
    /// let r = Rope::from("foo");
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
            panic!(
                "The given offset is past the end of the Rope: the byte \
                 length is {} but the byte offset is {}",
                self.byte_len(),
                byte_offset
            );
        }

        is_grapheme_boundary(self.chunks(), self.byte_len(), byte_offset)
    }

    /// TODO: docs
    #[inline]
    pub fn line(&self, line_index: usize) -> RopeSlice<'_> {
        if line_index >= self.line_len() {
            panic!(
                "Trying to index past the end of the Rope: the line length \
                 is {} but the line index is {}",
                self.line_len(),
                line_index
            );
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

        RopeSlice { tree_slice, last_byte_is_newline: false }
    }

    /// TODO: docs
    #[inline]
    pub fn line_len(&self) -> usize {
        self.tree.summary().line_breaks + 1
            - (self.last_byte_is_newline as usize)
            - (self.is_empty() as usize)
    }

    /// TODO: docs
    #[inline]
    pub fn line_of_byte(&self, byte_index: usize) -> usize {
        if byte_index >= self.byte_len() {
            panic!(
                "Trying to index past the end of the Rope: the byte length \
                 is {} but the byte index is {}",
                self.byte_len(),
                byte_index
            );
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

        if end > self.line_len() {
            panic!(
                "Trying to slice past the end of the Rope: the line length \
                 is {} but the end of the line range is {}",
                self.line_len(),
                end
            );
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

    /// TODO: docs
    #[inline]
    pub fn replace<R, T>(&mut self, byte_range: R, text: T)
    where
        R: RangeBounds<usize>,
        T: AsRef<str>,
    {
        let (start, end) =
            range_bounds_to_start_end(byte_range, 0, self.byte_len());

        if start > end {
            panic!("TODO");
        }

        if end > self.byte_len() {
            panic!(
                "Trying to edit past the end of the Rope: the byte length is \
                 {} but the end of the byte range is {}",
                self.byte_len(),
                end
            );
        }

        self.tree
            .replace(ByteMetric(start)..ByteMetric(end), text.as_ref().into());

        #[cfg(debug_assertions)]
        self.assert_invariants();
    }
}

impl From<RopeSlice<'_>> for Rope {
    #[inline]
    fn from(rope_slice: RopeSlice<'_>) -> Rope {
        let rope = Self {
            last_byte_is_newline: rope_slice.last_byte_is_newline,
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
            tree: Tree::from_leaves(
                RopeChunkIter::new(s)
                    .map(|chunk| RopeChunk { text: chunk.to_owned() }),
            ),
            last_byte_is_newline: last_byte_is_newline(s),
        }
    }
}

impl From<String> for Rope {
    #[inline]
    fn from(s: String) -> Self {
        if s.is_empty() {
            Rope::new()
        } else if rope_chunk_append("", &s).1.is_empty() {
            // If the string fits in one chunk we can avoid a new allocation.
            Rope {
                last_byte_is_newline: last_byte_is_newline(&s),
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
