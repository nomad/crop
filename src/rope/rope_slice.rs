use std::ops::RangeBounds;

use super::iterators::{Bytes, Chars, Chunks, Lines};
use super::metrics::{ByteMetric, LineMetric};
use super::utils::*;
use super::{Rope, RopeChunk};
use crate::tree::TreeSlice;

/// TODO: docs
#[derive(Copy, Clone)]
pub struct RopeSlice<'a> {
    pub(super) tree_slice: TreeSlice<'a, { Rope::fanout() }, RopeChunk>,
}

impl<'a> RopeSlice<'a> {
    /// TODO: docs
    #[inline]
    pub fn byte(&self, byte_idx: usize) -> u8 {
        if byte_idx >= self.byte_len() {
            panic!(
                "Trying to index past the end of the RopeSlice: the byte \
                 length is {} but the byte index is {}",
                self.byte_len(),
                byte_idx
            );
        }

        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn byte_len(&self) -> usize {
        self.tree_slice.summary().bytes
    }

    /// TODO: docs
    #[inline]
    pub fn byte_of_line(&self, line_idx: usize) -> usize {
        if line_idx >= self.line_len() {
            panic!(
                "Trying to index past the end of the RopeSlice: the line \
                 length is {} but the line index is {}",
                self.line_len(),
                line_idx
            );
        }

        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn byte_slice<R>(&'a self, byte_range: R) -> RopeSlice<'a>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) =
            range_bounds_to_start_end(byte_range, 0, self.byte_len());

        if end > self.byte_len() {
            panic!(
                "Trying to slice past the end of the RopeSlice: the byte \
                 length is {} but the end of the byte range is {}",
                self.byte_len(),
                end
            );
        }

        Self::new(self.tree_slice.slice(ByteMetric(start)..ByteMetric(end)))
    }

    /// Returns an iterator over the bytes of this [`RopeSlice`].
    #[inline]
    pub fn bytes(&'a self) -> Bytes<'a> {
        Bytes::from(self)
    }

    /// Returns an iterator over the [`char`]s of this [`RopeSlice`].
    #[inline]
    pub fn chars(&'a self) -> Chars<'a> {
        Chars::from(self)
    }

    /// Returns an iterator over the chunks of this [`RopeSlice`].
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

    /// TODO: docs
    #[inline]
    pub fn is_char_boundary(&self, byte_idx: usize) -> bool {
        todo!()
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

    /// TODO: docs
    #[cfg(feature = "graphemes")]
    #[inline]
    pub fn is_grapheme_boundary(&self, byte_idx: usize) -> bool {
        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn line(&'a self, line_idx: usize) -> RopeSlice<'a> {
        if line_idx >= self.line_len() {
            panic!(
                "Trying to index past the end of the RopeSlice: the line \
                 length is {} but the line index is {}",
                self.line_len(),
                line_idx
            );
        }

        Self::new(
            self.tree_slice
                .slice(LineMetric(line_idx)..LineMetric(line_idx + 1)),
        )
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
    pub fn line_of_byte(&self, byte_idx: usize) -> usize {
        if byte_idx >= self.byte_len() {
            panic!(
                "Trying to index past the end of the RopeSlice: the byte \
                 length is {} but the byte index is {}",
                self.byte_len(),
                byte_idx
            );
        }

        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn line_slice<R>(&'a self, line_range: R) -> RopeSlice<'a>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) =
            range_bounds_to_start_end(line_range, 0, self.line_len());

        if end > self.line_len() {
            panic!(
                "Trying to slice past the end of the RopeSlice: the line \
                 length is {} but the end of the line range is {}",
                self.line_len(),
                end
            );
        }

        Self::new(self.tree_slice.slice(LineMetric(start)..LineMetric(end)))
    }

    /// Returns an iterator over the lines of this [`RopeSlice`].
    #[inline]
    pub fn lines(&'a self) -> Lines<'a> {
        Lines::from(self)
    }

    #[inline]
    pub(super) fn new(
        tree_slice: TreeSlice<'a, { Rope::fanout() }, RopeChunk>,
    ) -> Self {
        Self { tree_slice }
    }

    #[inline]
    pub(super) fn tree_slice(
        &'a self,
    ) -> &'a TreeSlice<'a, { Rope::fanout() }, RopeChunk> {
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
