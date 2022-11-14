use std::ops::RangeBounds;

use super::iterators::{Bytes, Chars, Chunks, Lines};
use super::metrics::ByteMetric;
use super::utils::*;
use super::{Rope, TextChunk};
use crate::tree::TreeSlice;

/// TODO: docs
pub struct RopeSlice<'a> {
    tree_slice: TreeSlice<'a, { Rope::fanout() }, TextChunk>,
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
    pub fn bytes(&self) -> Bytes<'_> {
        Bytes::from(self)
    }

    /// TODO: docs
    #[inline]
    pub fn chars(&self) -> Chars<'_> {
        Chars::from(self)
    }

    /// TODO: docs
    pub(super) fn chunks(&self) -> Chunks<'_> {
        Chunks { chunks: self.tree_slice.leaves() }
    }

    /// TODO: docs
    #[inline]
    pub fn lines(&self) -> Lines<'_> {
        Lines::from(self)
    }

    #[inline]
    pub(super) fn new(
        tree_slice: TreeSlice<'a, { Rope::fanout() }, TextChunk>,
    ) -> Self {
        Self { tree_slice }
    }

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
        std::fmt::Display::fmt(self, f)?;
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
