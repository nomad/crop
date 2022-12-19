use std::ops::RangeBounds;

use super::iterators::{Bytes, Chars, Chunks, Lines};
use super::metrics::{ByteMetric, LineMetric};
use super::utils::*;
use super::{RopeChunk, RopeChunkIter};
use crate::tree::Tree;
use crate::RopeSlice;

#[cfg(not(any(test, feature = "integration_tests")))]
const ROPE_FANOUT: usize = 8;

#[cfg(any(test, feature = "integration_tests"))]
const ROPE_FANOUT: usize = 2;

/// TODO: docs
#[derive(Clone, Default)]
pub struct Rope {
    root: Tree<ROPE_FANOUT, RopeChunk>,
    last_byte_is_newline: bool,
}

impl Rope {
    /// TODO: docs.
    #[inline]
    pub fn byte(&self, byte_idx: usize) -> u8 {
        if byte_idx >= self.byte_len() {
            panic!(
                "Trying to index past the end of the Rope: the byte length \
                 is {} but the byte index is {}",
                self.byte_len(),
                byte_idx
            );
        }

        let (chunk, ByteMetric(chunk_idx)) =
            self.root.leaf_at_measure(ByteMetric(byte_idx));

        chunk.as_bytes()[byte_idx - chunk_idx]
    }

    /// TODO: docs
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.root.summary().bytes
    }

    /// TODO: docs
    #[inline]
    pub fn byte_of_line(&self, line_idx: usize) -> usize {
        if line_idx >= self.line_len() {
            panic!(
                "Trying to index past the end of the Rope: the line length \
                 is {} but the line index is {}",
                self.line_len(),
                line_idx
            );
        }

        todo!()
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

        RopeSlice::from(self.root.slice(ByteMetric(start)..ByteMetric(end)))
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
        todo!()
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
    pub fn insert<T>(&mut self, byte_idx: usize, text: T)
    where
        T: AsRef<str>,
    {
        if byte_idx > self.byte_len() {
            panic!(
                "Trying to insert past the end of the Rope: the byte length \
                 is {} but the byte index is {}",
                self.byte_len(),
                byte_idx
            );
        }

        let text = text.as_ref();

        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn is_char_boundary(&self, byte_idx: usize) -> bool {
        todo!()
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
    pub fn is_grapheme_boundary(&self, byte_idx: usize) -> bool {
        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn line(&self, line_idx: usize) -> RopeSlice<'_> {
        if line_idx >= self.line_len() {
            panic!(
                "Trying to index past the end of the Rope: the line length \
                 is {} but the line index is {}",
                self.line_len(),
                line_idx
            );
        }

        RopeSlice::from(
            self.root.slice(LineMetric(line_idx)..LineMetric(line_idx + 1)),
        )
    }

    /// TODO: docs
    #[inline]
    pub fn line_len(&self) -> usize {
        self.root.summary().line_breaks + 1
            - (self.last_byte_is_newline as usize)
            - (self.is_empty() as usize)
    }

    /// TODO: docs
    #[inline]
    pub fn line_of_byte(&self, byte_idx: usize) -> usize {
        if byte_idx >= self.byte_len() {
            panic!(
                "Trying to index past the end of the Rope: the byte length \
                 is {} but the byte index is {}",
                self.byte_len(),
                byte_idx
            );
        }

        todo!()
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

        RopeSlice::from(self.root.slice(LineMetric(start)..LineMetric(end)))
    }

    /// Returns an iterator over the lines of this [`Rope`].
    #[inline]
    pub fn lines(&self) -> Lines<'_> {
        Lines::from(self)
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
        todo!()
    }

    #[inline]
    pub(super) fn root(&self) -> &Tree<ROPE_FANOUT, RopeChunk> {
        &self.root
    }
}

impl From<RopeSlice<'_>> for Rope {
    #[inline]
    fn from(rope_slice: RopeSlice<'_>) -> Rope {
        Rope {
            root: Tree::from(rope_slice.tree_slice),
            last_byte_is_newline: rope_slice.last_byte_is_newline,
        }
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
        if s.is_empty() {
            // Building a rope from empty string has to be special-cased
            // because `RopeChunkIter` would yield 0 items.
            Rope::new()
        } else {
            Rope {
                root: Tree::from_leaves(RopeChunkIter::new(s)),
                last_byte_is_newline: matches!(
                    s.as_bytes().last(),
                    Some(b'\n')
                ),
            }
        }
    }
}

impl From<String> for Rope {
    #[inline]
    fn from(s: String) -> Self {
        if s.len() <= RopeChunk::max_bytes() {
            // If the string fits in one chunk we can avoid the allocation.
            Rope {
                last_byte_is_newline: matches!(
                    s.as_bytes().last(),
                    Some(b'\n')
                ),
                root: Tree::from_leaves([RopeChunk::from(s)]),
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

impl std::cmp::PartialEq<Rope> for Rope {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        if self.byte_len() != rhs.byte_len() {
            false
        } else {
            chunks_eq_chunks(self.chunks(), rhs.chunks())
        }
    }
}

impl std::cmp::PartialEq<RopeSlice<'_>> for Rope {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'_>) -> bool {
        if self.byte_len() != rhs.byte_len() {
            false
        } else {
            chunks_eq_chunks(self.chunks(), rhs.chunks())
        }
    }
}

impl std::cmp::PartialEq<str> for Rope {
    #[inline]
    fn eq(&self, rhs: &str) -> bool {
        if self.byte_len() != rhs.len() {
            false
        } else {
            chunks_eq_str(self.chunks(), rhs)
        }
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
