use std::ops::RangeBounds;

use super::iterators::{Bytes, Chars, Chunks, Lines};
use super::metrics::{ByteMetric, LineMetric};
use super::utils::*;
use super::{TextChunk, TextChunkIter};
use crate::tree::Tree;
use crate::RopeSlice;

#[cfg(not(test))]
const ROPE_FANOUT: usize = 8;

#[cfg(test)]
const ROPE_FANOUT: usize = 2;

/// TODO: docs
#[derive(Clone, Default)]
pub struct Rope {
    root: Tree<ROPE_FANOUT, TextChunk>,
    last_byte_is_newline: bool,
}

impl Rope {
    /// TODO: docs
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.root.summary().bytes
    }

    /// TODO: docs
    #[inline]
    pub fn byte_slice<R>(&self, byte_range: R) -> RopeSlice<'_>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = range_to_tuple(byte_range, 0, self.byte_len());
        RopeSlice::new(self.root.slice(ByteMetric(start)..ByteMetric(end)))
    }

    /// TODO: docs
    #[inline]
    pub fn bytes(&self) -> Bytes<'_> {
        Bytes::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn chars(&self) -> Chars<'_> {
        Chars::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn chunks(&self) -> Chunks<'_> {
        Chunks::from(self)
    }

    pub(super) const fn fanout() -> usize {
        ROPE_FANOUT
    }

    /// TODO: docs
    #[doc(hidden)]
    #[cfg(feature = "graphemes")]
    #[inline]
    pub fn graphemes(&self) -> crate::iter::Graphemes<'_> {
        crate::iter::Graphemes::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn insert(&mut self, after_byte: usize, _text: &str) {
        assert!(after_byte <= self.byte_len());
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
    #[inline]
    pub fn line_len(&self) -> usize {
        self.root.summary().line_breaks + 1
            - (self.last_byte_is_newline as usize)
    }

    /// TODO: docs
    #[inline]
    pub fn line_slice<R>(&self, line_range: R) -> RopeSlice<'_>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = range_to_tuple(line_range, 0, self.line_len());
        RopeSlice::new(self.root.slice(LineMetric(start)..LineMetric(end)))
    }

    /// TODO: docs
    #[inline]
    pub fn lines(&self) -> Lines<'_> {
        Lines::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    pub(super) fn root(&self) -> &Tree<ROPE_FANOUT, TextChunk> {
        &self.root
    }
}

impl std::fmt::Debug for Rope {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // TODO: escape \r, \n, etc.
        f.write_str("Rope(\"")?;
        std::fmt::Display::fmt(self, f)?;
        f.write_str("\")")
    }
}

impl std::fmt::Display for Rope {
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
            // because `TextChunkIter` would yield 0 items.
            Rope::new()
        } else {
            Rope {
                root: Tree::from_leaves(TextChunkIter::new(s)),
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
        if s.len() <= TextChunk::max_bytes() {
            // If the string fits in one chunk we can avoid the allocation.
            let last_byte_is_newline =
                s.as_bytes().last().map(|b| *b == b'\n').unwrap_or_default();
            Rope {
                root: Tree::from_leaves([TextChunk::from(s)]),
                last_byte_is_newline,
            }
        } else {
            Rope::from(&*s)
        }
    }
}

impl<'a> From<std::borrow::Cow<'a, str>> for Rope {
    #[inline]
    fn from(moo: std::borrow::Cow<'a, str>) -> Self {
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

impl<'a> std::cmp::PartialEq<RopeSlice<'a>> for Rope {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'a>) -> bool {
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

impl<'a> std::cmp::PartialEq<&'a str> for Rope {
    #[inline]
    fn eq(&self, rhs: &&'a str) -> bool {
        self == *rhs
    }
}

impl<'a> std::cmp::PartialEq<Rope> for &'a str {
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

impl<'a> std::cmp::PartialEq<std::borrow::Cow<'a, str>> for Rope {
    #[inline]
    fn eq(&self, rhs: &std::borrow::Cow<'a, str>) -> bool {
        self == &**rhs
    }
}

impl<'a> std::cmp::PartialEq<Rope> for std::borrow::Cow<'a, str> {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        rhs == self
    }
}

impl std::cmp::Eq for Rope {}
