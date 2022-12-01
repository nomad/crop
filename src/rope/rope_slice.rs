use std::ops::RangeBounds;

use super::iterators::{Bytes, Chars, Chunks, Lines};
use super::metrics::{ByteMetric, LineMetric};
use super::utils::*;
use super::{Rope, TextChunk};
use crate::tree::TreeSlice;

/// TODO: docs
#[derive(Clone)]
pub struct RopeSlice<'a> {
    pub(super) tree_slice: TreeSlice<'a, { Rope::fanout() }, TextChunk>,
}

impl<'a> RopeSlice<'a> {
    /// TODO: docs
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.tree_slice.summary().bytes
    }

    /// TODO: docs
    #[inline]
    pub fn byte_slice<R>(&'a self, byte_range: R) -> RopeSlice<'a>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = range_to_tuple(byte_range, 0, self.byte_len());
        Self::new(self.tree_slice.slice(ByteMetric(start)..ByteMetric(end)))
    }

    /// TODO: docs
    #[inline]
    pub fn bytes(&'a self) -> Bytes<'a> {
        Bytes::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn chars(&'a self) -> Chars<'a> {
        Chars::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn chunks(&'a self) -> Chunks<'a> {
        Chunks::from(self)
    }

    /// TODO: docs
    #[doc(hidden)]
    #[cfg(feature = "graphemes")]
    #[inline]
    pub fn graphemes(&'a self) -> crate::iter::Graphemes<'a> {
        crate::iter::Graphemes::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn line_len(&self) -> usize {
        todo!()
        // self.tree_slice.summary().line_breaks + 1
        //     - (self.last_byte_is_newline as usize)
    }

    /// TODO: docs
    #[inline]
    pub fn line_slice<R>(&'a self, line_range: R) -> RopeSlice<'a>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = range_to_tuple(line_range, 0, self.line_len());
        RopeSlice::new(
            self.tree_slice.slice(LineMetric(start)..LineMetric(end)),
        )
    }

    /// TODO: docs
    #[inline]
    pub fn lines(&'a self) -> Lines<'a> {
        Lines::from(self)
    }

    /// Returns `true` if the `RopeSlice`'s byte length is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use crop::Rope;
    ///
    /// let r = Rope::from("");
    /// assert!(r.byte_slice(..).is_empty());
    ///
    /// let r = Rope::from("foo");
    /// assert!(!r.line_slice(0..1).is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.byte_len() == 0
    }

    #[inline]
    pub(super) fn new(
        tree_slice: TreeSlice<'a, { Rope::fanout() }, TextChunk>,
    ) -> Self {
        Self { tree_slice }
    }

    #[inline]
    pub(super) fn tree_slice(
        &'a self,
    ) -> &'a TreeSlice<'a, { Rope::fanout() }, TextChunk> {
        &self.tree_slice
    }
}

impl<'a> std::fmt::Debug for RopeSlice<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // TODO: escape \r, \n, etc.
        f.write_str("RopeSlice(\"")?;
        debug_chunks(self.chunks(), f)?;
        f.write_str("\")")
    }
}

impl<'a> std::fmt::Display for RopeSlice<'a> {
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
        if self.byte_len() != rhs.byte_len() {
            false
        } else {
            chunks_eq_chunks(self.chunks(), rhs.chunks())
        }
    }
}

impl<'a> std::cmp::PartialEq<Rope> for RopeSlice<'a> {
    #[inline]
    fn eq(&self, rhs: &Rope) -> bool {
        rhs == self
    }
}

impl<'a> std::cmp::PartialEq<str> for RopeSlice<'a> {
    #[inline]
    fn eq(&self, rhs: &str) -> bool {
        if self.byte_len() != rhs.len() {
            false
        } else {
            chunks_eq_str(self.chunks(), rhs)
        }
    }
}

impl<'a> std::cmp::PartialEq<RopeSlice<'a>> for str {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'a>) -> bool {
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

impl<'a> std::cmp::PartialEq<String> for RopeSlice<'a> {
    #[inline]
    fn eq(&self, rhs: &String) -> bool {
        self == &**rhs
    }
}

impl<'a> std::cmp::PartialEq<RopeSlice<'a>> for String {
    #[inline]
    fn eq(&self, rhs: &RopeSlice<'a>) -> bool {
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

impl<'a> std::cmp::Eq for RopeSlice<'a> {}
