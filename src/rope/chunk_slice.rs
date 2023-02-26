use super::rope_chunk::{ChunkSummary, RopeChunk};
use super::utils::*;
use crate::tree::Summarize;

#[derive(Debug, PartialEq)]
#[repr(transparent)]
pub(super) struct ChunkSlice {
    text: str,
}

impl Default for &ChunkSlice {
    #[inline]
    fn default() -> Self {
        "".into()
    }
}

impl<'a> From<&'a str> for &'a ChunkSlice {
    #[inline]
    fn from(text: &str) -> Self {
        // SAFETY: both the lifetime and the layout match.
        unsafe { &*(text as *const str as *const ChunkSlice) }
    }
}

impl PartialEq<str> for ChunkSlice {
    #[inline]
    fn eq(&self, rhs: &str) -> bool {
        &self.text == rhs
    }
}

impl PartialEq<ChunkSlice> for str {
    #[inline]
    fn eq(&self, rhs: &ChunkSlice) -> bool {
        rhs == self
    }
}

impl Summarize for ChunkSlice {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        ChunkSummary {
            bytes: self.text.len(),
            line_breaks: str_indices::lines_lf::count_breaks(&self.text),
        }
    }
}

impl std::ops::Deref for ChunkSlice {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.text
    }
}

impl ToOwned for ChunkSlice {
    type Owned = RopeChunk;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        // This ensures that the `RopeChunk` has the right capacity.
        let mut chunk = RopeChunk::default();
        chunk.push_str(self);
        chunk
    }
}

impl<'a> ChunkSlice {
    /// Balances `left` using `right`.
    ///
    /// # Panics
    ///
    /// Panics if `left` is not underfilled, in `right` is underfilled and if
    /// `left` and `right` can be combined in a single chunk.
    #[inline]
    pub(super) fn balance_left_with_right(
        left: &Self,
        left_summary: ChunkSummary,
        right: &Self,
        right_summary: ChunkSummary,
    ) -> ((RopeChunk, ChunkSummary), (RopeChunk, ChunkSummary)) {
        debug_assert!(left.len() < RopeChunk::min_bytes());
        debug_assert!(right.len() > RopeChunk::min_bytes());
        debug_assert!(left.len() + right.len() > RopeChunk::max_bytes());

        let missing = RopeChunk::min_bytes() - left.len();

        let (mut to_left, mut new_right) =
            right.split_adjusted::<false>(missing);

        if left.len() + to_left.len() < RopeChunk::chunk_min() {
            (to_left, new_right) = right.split_adjusted::<true>(missing);
        }

        let left = {
            let mut l = left.to_owned();
            l.push_str(to_left);
            l
        };

        let to_left_summary = to_left.summarize();

        let left_summary = left_summary + to_left_summary;

        let right = new_right.to_owned();

        let right_summary = right_summary - to_left_summary;

        debug_assert!(left.is_within_chunk_bounds());
        debug_assert!(right.is_within_chunk_bounds());

        ((left, left_summary), (right, right_summary))
    }

    /// Balances `right` using `left`.
    ///
    /// # Panics
    ///
    /// Panics if `right` is not underfilled, in `left` is underfilled and if
    /// `left` and `right` can be combined in a single chunk.
    #[inline]
    pub(super) fn balance_right_with_left(
        left: &Self,
        left_summary: ChunkSummary,
        right: &Self,
        right_summary: ChunkSummary,
    ) -> ((RopeChunk, ChunkSummary), (RopeChunk, ChunkSummary)) {
        debug_assert!(left.len() > RopeChunk::min_bytes());
        debug_assert!(right.len() < RopeChunk::min_bytes());
        debug_assert!(left.len() + right.len() > RopeChunk::max_bytes());

        let missing = RopeChunk::min_bytes() - right.len();

        let (mut new_left, mut to_right) =
            left.split_adjusted::<true>(left.len() - missing);

        if to_right.len() + right.len() < RopeChunk::chunk_min() {
            (new_left, to_right) =
                left.split_adjusted::<false>(left.len() - missing);
        }

        let right = {
            let mut r = to_right.to_owned();
            r.push_str(right);
            r
        };

        let to_right_summary = to_right.summarize();

        let right_summary = right_summary + to_right_summary;

        let left = new_left.to_owned();

        let left_summary = left_summary - to_right_summary;

        debug_assert!(left.is_within_chunk_bounds());
        debug_assert!(right.is_within_chunk_bounds());

        ((left, left_summary), (right, right_summary))
    }

    /// Returns whether the length of this slice is within
    /// [`RopeChunk::chunk_min()`] and [`RopeChunk::chunk_max()`].
    #[allow(dead_code)]
    #[inline]
    pub(super) fn is_within_chunk_bounds(&self) -> bool {
        self.len() >= RopeChunk::chunk_min()
            && self.len() <= RopeChunk::chunk_max()
    }

    /// Splits the slice at `byte_offset`, returning the left and right sides
    /// of the split.
    ///
    /// Note that the split point will be adjusted to make sure it's within the
    /// bounds of this slice, it lies on a char boundary and it doesn't split
    /// CRLF pair. Offsets past the end of the slice are valid and will be
    /// clipped to the length of the slice.
    #[inline]
    pub(super) fn split_adjusted<const WITH_RIGHT_BIAS: bool>(
        &'a self,
        byte_offset: usize,
    ) -> (&'a ChunkSlice, &'a ChunkSlice) {
        let split_at =
            adjust_split_point::<WITH_RIGHT_BIAS>(self, byte_offset);
        // SAFETY: we've adjusted the split point so now it's guaranteed to be
        // valid.
        unsafe { self.split_unchecked(split_at) }
    }

    /// Splits the slice at `byte_offset`, returning the left and right sides
    /// of the split.
    ///
    /// # Safety
    ///
    /// Unlike [`Self::split_adjusted()`] this function doesn't adjust the
    /// split point to make sure it's within bounds and it lies on a char
    /// boundary, leaving that up to the caller.
    #[inline]
    pub(super) unsafe fn split_unchecked(
        &'a self,
        byte_offset: usize,
    ) -> (&'a ChunkSlice, &'a ChunkSlice) {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));
        (
            self.get_unchecked(..byte_offset).into(),
            self.get_unchecked(byte_offset..).into(),
        )
    }
}

/// An iterator over the valid split points of a `ChunkSlice`.
///
/// All the `ChunkSlice`s yielded by this iterator are guaranteed to never
/// split char boundaries and CRLF pairs and to be within the chunk bounds of
/// [`RopeChunk`]s.
///
/// The only exception is if the slice fed to [`Self::new()`] is shorter than
/// [`RopeChunk::chunk_min()`], in which case this will only yield that slice.
pub(super) struct ChunkSegmenter<'a> {
    text: &'a ChunkSlice,
    yielded: usize,
}

impl<'a> ChunkSegmenter<'a> {
    #[inline]
    pub(super) fn new<T>(text: T) -> Self
    where
        T: Into<&'a ChunkSlice>,
    {
        Self { text: text.into(), yielded: 0 }
    }
}

impl<'a> Iterator for ChunkSegmenter<'a> {
    type Item = &'a ChunkSlice;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut remaining = self.text.len() - self.yielded;

        let chunk = if remaining == 0 {
            return None;
        } else if remaining > RopeChunk::max_bytes() {
            let mut chunk_len = RopeChunk::max_bytes();

            remaining -= chunk_len;

            if remaining < RopeChunk::min_bytes() {
                chunk_len -= RopeChunk::min_bytes() - remaining;
            }

            chunk_len = adjust_split_point::<true>(
                &self.text[self.yielded..],
                chunk_len,
            );

            &self.text[self.yielded..(self.yielded + chunk_len)]
        } else {
            debug_assert!(
                self.yielded == 0 || remaining >= RopeChunk::chunk_min()
            );

            &self.text[self.text.len() - remaining..]
        };

        self.yielded += chunk.len();

        Some(chunk.into())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let lo = (self.text.len() - self.yielded) / RopeChunk::max_bytes();
        (lo, Some(lo + 1))
    }
}

impl std::iter::FusedIterator for ChunkSegmenter<'_> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn balance_left_with_right_0() {
        let left = <&ChunkSlice>::from("");
        let right = <&ChunkSlice>::from("ちは");

        let ((left, _), (right, _)) = ChunkSlice::balance_left_with_right(
            left,
            left.summarize(),
            right,
            right.summarize(),
        );

        assert_eq!("ち", &*left);
        assert_eq!("は", &*right);
    }

    #[test]
    fn balance_right_with_left_0() {
        let left = <&ChunkSlice>::from("ちは");
        let right = <&ChunkSlice>::from("");

        let ((left, _), (right, _)) = ChunkSlice::balance_right_with_left(
            left,
            left.summarize(),
            right,
            right.summarize(),
        );

        assert_eq!("ち", &*left);
        assert_eq!("は", &*right);
    }

    #[test]
    fn chunk_segmenter_0() {
        let mut segments = ChunkSegmenter::new("");
        assert_eq!(None, segments.next());
    }

    #[test]
    fn chunk_segmenter_1() {
        let mut segments = ChunkSegmenter::new("a");
        assert_eq!("a", segments.next().unwrap());
        assert_eq!(None, segments.next());
    }

    #[test]
    fn chunk_segmenter_2() {
        let mut segments = ChunkSegmenter::new("abcde");
        assert_eq!("abc", segments.next().unwrap());
        assert_eq!("de", segments.next().unwrap());
        assert_eq!(None, segments.next());
    }

    #[test]
    fn chunk_segmenter_3() {
        let mut segments = ChunkSegmenter::new("abcdefghi");
        assert_eq!("abcd", segments.next().unwrap());
        assert_eq!("efg", segments.next().unwrap());
        assert_eq!("hi", segments.next().unwrap());
        assert_eq!(None, segments.next());
    }

    // TODO: test multibyte characters
}
