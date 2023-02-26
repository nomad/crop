use std::ops::{Add, AddAssign, Range, RangeBounds, Sub, SubAssign};

use super::chunk_slice::ChunkSlice;
use super::metrics::ByteMetric;
use super::utils::*;
use crate::range_bounds_to_start_end;
use crate::tree::{BalancedLeaf, Leaf, ReplaceableLeaf, Summarize};

#[cfg(any(test, feature = "small_chunks"))]
const ROPE_CHUNK_MAX_BYTES: usize = 4;

#[cfg(not(any(test, feature = "small_chunks")))]
const ROPE_CHUNK_MAX_BYTES: usize = 1024;

const ROPE_CHUNK_MIN_BYTES: usize = ROPE_CHUNK_MAX_BYTES / 2;

#[derive(Clone, PartialEq)]
pub(super) struct RopeChunk {
    pub(super) text: String,
}

impl std::fmt::Debug for RopeChunk {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.text, f)
    }
}

impl Default for RopeChunk {
    #[inline]
    fn default() -> Self {
        Self { text: String::with_capacity(Self::chunk_max()) }
    }
}

impl RopeChunk {
    #[inline]
    fn as_slice(&self) -> &ChunkSlice {
        use std::borrow::Borrow;
        self.borrow()
    }

    /// Balances `left` using `right`.
    ///
    /// # Panics
    ///
    /// Panics if `left` is not underfilled, in `right` is underfilled and if
    /// `left` and `right` can be combined in a single chunk.
    #[inline]
    fn balance_left_with_right(
        left: &mut Self,
        left_summary: &mut ChunkSummary,
        right: &mut Self,
        right_summary: &mut ChunkSummary,
    ) {
        // TODO: this is basically the same as
        // `ChunkSlice::balance_left_with_right()` excess it doesn't allocate a
        // new left chunk. Can we DRY this up?

        debug_assert!(left.len() < RopeChunk::min_bytes());
        debug_assert!(right.len() > RopeChunk::min_bytes());
        debug_assert!(left.len() + right.len() > RopeChunk::max_bytes());

        let missing = RopeChunk::min_bytes() - left.len();

        let (mut to_left, mut new_right) =
            right.as_slice().split_adjusted::<false>(missing);

        if left.len() + to_left.len() < RopeChunk::chunk_min() {
            (to_left, new_right) =
                right.as_slice().split_adjusted::<true>(missing);
        }

        left.push_str(to_left);

        let to_left_summary = to_left.summarize();

        *left_summary += to_left_summary;

        *right = new_right.to_owned();

        *right_summary -= to_left_summary;

        debug_assert!(left.is_within_chunk_bounds());
        debug_assert!(right.is_within_chunk_bounds());
    }

    /// Balances `right` using `left`.
    ///
    /// # Panics
    ///
    /// Panics if `right` is not underfilled, in `left` is underfilled and if
    /// `left` and `right` can be combined in a single chunk.
    #[inline]
    fn balance_right_with_left(
        left: &mut Self,
        left_summary: &mut ChunkSummary,
        right: &mut Self,
        right_summary: &mut ChunkSummary,
    ) {
        ((*left, *left_summary), (*right, *right_summary)) =
            ChunkSlice::balance_right_with_left(
                left.as_slice(),
                *left_summary,
                right.as_slice(),
                *right_summary,
            );
    }

    /// The number of bytes `RopeChunk`s must always stay under.
    pub(super) const fn chunk_max() -> usize {
        // We can exceed the max by 3 bytes at most, which happens when the
        // chunk boundary would have landed after the first byte of a 4 byte
        // codepoint.
        Self::max_bytes() + 3
    }

    /// The number of bytes `RopeChunk`s must always stay over.
    pub(super) const fn chunk_min() -> usize {
        if Self::min_bytes() > 3 {
            // The wiggle room is 3 bytes for the reason already explained in
            // the comment above.
            Self::min_bytes() - 3
        } else {
            1
        }
    }

    /// The number of bytes `RopeChunk`s should aim to stay under.
    pub(super) const fn max_bytes() -> usize {
        ROPE_CHUNK_MAX_BYTES
    }

    /// The number of bytes `RopeChunk`s should aim to stay over.
    pub(super) const fn min_bytes() -> usize {
        ROPE_CHUNK_MIN_BYTES
    }

    /// Returns whether the length of this chunk is within
    /// [`RopeChunk::chunk_min()`] and [`RopeChunk::chunk_max()`].
    pub(super) fn is_within_chunk_bounds(&self) -> bool {
        self.len() >= Self::chunk_min() && self.len() <= Self::chunk_max()
    }

    /// Pushes as mush of `slice` as possible into this chunk, returning the
    /// rest.
    #[inline]
    pub(super) fn push_with_remainder<'a>(
        &mut self,
        slice: &'a ChunkSlice,
    ) -> &'a ChunkSlice {
        if self.len() >= Self::max_bytes() {
            // If the current text is already longer than
            // `RopeChunk::max_bytes()` the only edge case to consider is not
            // splitting CRLF pairs.
            if ends_in_cr(self) && starts_with_lf(slice) {
                // SAFETY: the slice starts with a `\n` so 1 is a char
                // boundary.
                let (lf, rest) = unsafe { slice.split_unchecked(1) };
                self.push_str(lf);
                return rest;
            } else {
                return slice;
            }
        }

        let (push, rest) =
            slice.split_adjusted::<true>(Self::max_bytes() - self.len());

        self.push_str(push);

        debug_assert!(self.len() <= Self::chunk_max());

        rest
    }

    /// Slices the chunk in the given range.
    ///
    /// # Safety
    ///
    /// This functions is unsafe because it doesn't do any bound/char boundary
    /// checks on neither the start nor the end of the byte range, leaving that
    /// up to the caller.
    #[inline]
    unsafe fn slice_unchecked(&self, byte_range: Range<usize>) -> &ChunkSlice {
        debug_assert!(byte_range.start <= byte_range.end);
        debug_assert!(byte_range.end <= self.len());
        debug_assert!(self.is_char_boundary(byte_range.start));
        debug_assert!(self.is_char_boundary(byte_range.end));

        self.get_unchecked(byte_range).into()
    }

    #[inline]
    fn split_off_adjusted<const WITH_RIGHT_BIAS: bool>(
        &mut self,
        byte_offset: usize,
    ) -> Self {
        let split_at = adjust_split_point::<WITH_RIGHT_BIAS>(
            self.as_slice(),
            byte_offset,
        );
        // SAFETY: we've adjusted the split point so now it's guaranteed to be
        // valid.
        unsafe { self.split_off_unchecked(split_at) }
    }

    /// Splits the chunk at the given byte offset, returning the right side of
    /// the split. The chunk will have `byte_offset` bytes after splitting.
    ///
    /// # Safety
    ///
    /// The function is unsafe because it does not check that `byte_offset` is
    /// within bounds and a valid char boundary, leaving that up to the caller.
    #[inline]
    unsafe fn split_off_unchecked(&mut self, byte_offset: usize) -> Self {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));

        let rhs = self.as_mut_vec().split_off(byte_offset);
        Self { text: String::from_utf8_unchecked(rhs) }
    }

    /// Removes all the contents after `byte_offset` from the chunk, leaving
    /// the capacity untouched.
    ///
    /// # Safety
    ///
    /// The function is unsafe because it does not check that `byte_offset` is
    /// a valid char boundary, leaving that up to the caller.
    #[inline]
    unsafe fn truncate_unchecked(&mut self, byte_offset: usize) {
        debug_assert!(self.is_char_boundary(byte_offset));
        self.as_mut_vec().truncate(byte_offset);
    }
}

impl std::borrow::Borrow<ChunkSlice> for RopeChunk {
    #[inline]
    fn borrow(&self) -> &ChunkSlice {
        (&*self.text).into()
    }
}

impl std::ops::Deref for RopeChunk {
    type Target = String;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.text
    }
}

impl std::ops::DerefMut for RopeChunk {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.text
    }
}

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub(super) struct ChunkSummary {
    pub(super) bytes: usize,
    pub(super) line_breaks: usize,
}

impl Add<Self> for ChunkSummary {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Self) -> Self {
        self += rhs;
        self
    }
}

impl Sub<Self> for ChunkSummary {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: Self) -> Self {
        self -= rhs;
        self
    }
}

impl Add<&Self> for ChunkSummary {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: &Self) -> Self {
        self += rhs;
        self
    }
}

impl Sub<&Self> for ChunkSummary {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: &Self) -> Self {
        self -= rhs;
        self
    }
}

impl AddAssign<Self> for ChunkSummary {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.bytes += rhs.bytes;
        self.line_breaks += rhs.line_breaks;
    }
}

impl SubAssign<Self> for ChunkSummary {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.bytes -= rhs.bytes;
        self.line_breaks -= rhs.line_breaks;
    }
}

impl AddAssign<&Self> for ChunkSummary {
    #[inline]
    fn add_assign(&mut self, rhs: &Self) {
        *self += *rhs;
    }
}

impl SubAssign<&Self> for ChunkSummary {
    #[inline]
    fn sub_assign(&mut self, rhs: &Self) {
        *self -= *rhs;
    }
}

impl From<&str> for RopeChunk {
    #[inline]
    fn from(s: &str) -> Self {
        <&ChunkSlice>::from(s).to_owned()
    }
}

impl Summarize for RopeChunk {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        self.as_slice().summarize()
    }
}

impl Leaf for RopeChunk {
    type BaseMetric = ByteMetric;

    type Slice = ChunkSlice;
}

impl BalancedLeaf for RopeChunk {
    #[inline]
    fn is_underfilled(_: &ChunkSlice, summary: &ChunkSummary) -> bool {
        summary.bytes < Self::min_bytes()
    }

    #[inline]
    fn balance_leaves(
        (left, left_summary): (&mut Self, &mut ChunkSummary),
        (right, right_summary): (&mut Self, &mut ChunkSummary),
    ) {
        if left.len() >= RopeChunk::min_bytes()
            && right.len() >= RopeChunk::min_bytes()
        {
        }
        // If both slices can fit in a single chunk we join them.
        else if left.len() + right.len() <= RopeChunk::max_bytes() {
            left.push_str(right);
            right.clear();
            *left_summary += *right_summary;
            *right_summary = ChunkSummary::default();
        }
        // If the left side is lacking we take text from the right side.
        else if left.len() < RopeChunk::min_bytes() {
            debug_assert!(right.len() > RopeChunk::min_bytes());

            Self::balance_left_with_right(
                left,
                left_summary,
                right,
                right_summary,
            );
        }
        // Viceversa, if the right side is lacking we take text from the left
        // side.
        else {
            debug_assert!(right.len() < RopeChunk::min_bytes());
            debug_assert!(left.len() > RopeChunk::min_bytes());

            Self::balance_right_with_left(
                left,
                left_summary,
                right,
                right_summary,
            );
        }
    }

    #[inline]
    fn balance_slices<'a>(
        (left, &left_summary): (&'a ChunkSlice, &'a ChunkSummary),
        (right, &right_summary): (&'a ChunkSlice, &'a ChunkSummary),
    ) -> ((Self, ChunkSummary), Option<(Self, ChunkSummary)>) {
        if left.len() >= RopeChunk::min_bytes()
            && right.len() >= RopeChunk::min_bytes()
        {
            (
                (left.to_owned(), left_summary),
                Some((right.to_owned(), right_summary)),
            )
        }
        // If both slices can fit in a single chunk we join them.
        else if left.len() + right.len() <= RopeChunk::max_bytes() {
            let left = {
                let mut l = left.to_owned();
                l.push_str(right);
                l
            };

            ((left, left_summary + right_summary), None)
        }
        // If the left side is lacking we take text from the right side.
        else if left.len() < RopeChunk::min_bytes() {
            debug_assert!(right.len() > RopeChunk::min_bytes());

            let (left, right) = ChunkSlice::balance_left_with_right(
                left,
                left_summary,
                right,
                right_summary,
            );

            (left, Some(right))
        }
        // Viceversa, if the right side is lacking we take text from the left
        // side.
        else {
            debug_assert!(right.len() < RopeChunk::min_bytes());
            debug_assert!(left.len() > RopeChunk::min_bytes());

            let (left, right) = ChunkSlice::balance_right_with_left(
                left,
                left_summary,
                right,
                right_summary,
            );

            (left, Some(right))
        }
    }
}

impl ReplaceableLeaf<ByteMetric> for RopeChunk {
    type ExtraLeaves = std::vec::IntoIter<Self>;

    #[inline]
    fn replace<R>(
        &mut self,
        summary: &mut ChunkSummary,
        range: R,
        mut slice: &ChunkSlice,
    ) -> Option<Self::ExtraLeaves>
    where
        R: RangeBounds<ByteMetric>,
    {
        let (start, end) = {
            let (s, e) = range_bounds_to_start_end(range, 0, self.len());

            debug_assert!(s <= e);
            debug_assert!(e <= self.len());

            assert!(self.is_char_boundary(s));
            assert!(self.is_char_boundary(e));

            (s, e)
        };

        // SAFETY: all the following calls to `RopeChunk::slice_unchecked()`,
        // `RopeChunk::split_off_unchecked()` and
        // `RopeChunk::truncate_unchecked()` are safe because `start` doesn't
        // exceed `end`, they are both within bounds and they both lie on char
        // boundaries.

        if self.len() - (end - start) + slice.len() <= Self::max_bytes() {
            if end > start {
                // SAFETY: see above.
                let range_summary = unsafe {
                    if end - start < self.len() / 2 {
                        self.slice_unchecked(start..end).summarize()
                    } else {
                        *summary
                            - self.slice_unchecked(0..start).summarize()
                            - self.slice_unchecked(end..self.len()).summarize()
                    }
                };

                *summary -= range_summary;
                *summary += slice.summarize();
                self.replace_range(start..end, slice);
            } else {
                *summary += slice.summarize();
                self.insert_str(start, slice);
            }

            return None;
        }

        // SAFETY: see above.
        let last = unsafe { self.split_off_unchecked(end) };
        let mut last = last.as_slice();

        // SAFETY: see above.
        unsafe { self.truncate_unchecked(start) };

        debug_assert!(
            self.len() + slice.len() + last.len() > Self::max_bytes()
        );

        let mut first = None;

        if self.len() < Self::min_bytes() {
            let mut missing = Self::min_bytes() - self.len();
            let (left, right) = slice.split_adjusted::<true>(missing);
            self.push_str(left);
            slice = right;

            // The slice alone wasn't enough, we need to also push some bytes
            // from `last`
            if left.len() < missing {
                debug_assert!(right.is_empty());
                missing -= left.len();
                let (left, right) = last.split_adjusted::<false>(missing);
                self.push_str(left);
                last = right;
            }
        } else if slice.len() + last.len() < Self::min_bytes() {
            let split = Self::min_bytes() - slice.len() - last.len();

            let mut to_first =
                self.split_off_adjusted::<true>(self.len() - split);

            if to_first.len() + slice.len() + last.len() < Self::chunk_min() {
                to_first =
                    self.split_off_adjusted::<false>(self.len() - split);
            }

            first = Some(to_first);
        }

        *summary = self.summarize();

        debug_assert!(self.is_within_chunk_bounds());

        Some(
            ExtraLeaves::new(first, slice, last)
                .collect::<Vec<_>>()
                .into_iter(),
        )
    }

    #[inline]
    fn remove(&mut self, summary: &mut ChunkSummary, up_to: ByteMetric) {
        let extra = self.replace(summary, ..up_to, "".into());
        debug_assert!(extra.is_none());
    }
}

/// An iterator very similar in spirit to
/// [`ChunkSegmenter`](super::ChunkSegmenter), except there we have
/// the luxury of having a contiguous slice to split, while here the input
/// slice is broken up into 3 pieces.
#[derive(Debug)]
struct ExtraLeaves<'a> {
    first: Option<RopeChunk>,
    yielded_first: bool,
    slice: &'a ChunkSlice,
    last: &'a ChunkSlice,
    yielded: usize,
    total: usize,
}

impl<'a> ExtraLeaves<'a> {
    /// # Panics
    ///
    /// Panics if the combined length of `first`, `slice` and `last` is
    /// less than [`RopeChunk::chunk_min()`].
    #[inline]
    pub(super) fn new(
        first: Option<RopeChunk>,
        slice: &'a ChunkSlice,
        last: &'a ChunkSlice,
    ) -> Self {
        debug_assert!(
            first.as_ref().map(|f| f.len()).unwrap_or(0)
                + slice.len()
                + last.len()
                >= RopeChunk::chunk_min()
        );

        Self {
            total: slice.len() + last.len(),
            yielded: 0,
            yielded_first: false,
            first,
            slice,
            last,
        }
    }

    #[inline]
    fn yield_first(&mut self) -> RopeChunk {
        debug_assert!(!self.yielded_first);

        self.yielded_first = true;

        if let Some(mut first) = self.first.take() {
            if first.len() + self.total <= RopeChunk::max_bytes() {
                first.push_str(self.slice);
                first.push_str(self.last);
                self.yielded = self.total;
                first
            } else {
                let mut add_to_first = RopeChunk::max_bytes() - first.len();

                if self.total - add_to_first < RopeChunk::min_bytes() {
                    add_to_first = self.total - RopeChunk::min_bytes();
                }

                let take_from_slice = if add_to_first > self.slice.len() {
                    self.slice.len()
                } else {
                    adjust_split_point::<true>(self.slice, add_to_first)
                };

                first.push_str(&self.slice[..take_from_slice]);
                self.slice = self.slice[take_from_slice..].into();
                self.yielded += take_from_slice;

                // If the slice alone wasn't enough we need to take from
                // `last`.
                if add_to_first > take_from_slice {
                    add_to_first -= take_from_slice;

                    let take_from_last =
                        adjust_split_point::<true>(self.last, add_to_first);
                    first.push_str(&self.last[..take_from_last]);
                    self.last = self.last[take_from_last..].into();
                    self.yielded += take_from_last;
                }

                first
            }
        } else {
            self.yield_next().unwrap()
        }
    }

    #[inline]
    fn yield_next(&mut self) -> Option<RopeChunk> {
        debug_assert!(self.yielded_first);
        debug_assert!(self.first.is_none());

        let remaining = self.total - self.yielded;

        let chunk: RopeChunk = if remaining == 0 {
            return None;
        } else if remaining > RopeChunk::max_bytes() {
            let mut chunk = RopeChunk::default();

            let mut chunk_len = RopeChunk::max_bytes();

            if remaining - chunk_len < RopeChunk::min_bytes() {
                chunk_len = remaining - RopeChunk::min_bytes();
            }

            let take_from_slice = if chunk_len > self.slice.len() {
                self.slice.len()
            } else {
                adjust_split_point::<true>(self.slice, chunk_len)
            };

            chunk.push_str(&self.slice[..take_from_slice]);
            self.slice = self.slice[take_from_slice..].into();

            // If the slice alone wasn't enough we need to take from
            // `last`.
            if chunk_len > take_from_slice {
                chunk_len -= take_from_slice;

                let take_from_last =
                    adjust_split_point::<true>(self.last, chunk_len);
                chunk.push_str(&self.last[..take_from_last]);
                self.last = self.last[take_from_last..].into();
            }

            chunk
        } else {
            debug_assert!(remaining >= RopeChunk::chunk_min());
            let mut last = self.slice.to_owned();
            last.push_str(self.last);
            last
        };

        self.yielded += chunk.len();

        Some(chunk)
    }
}

impl Iterator for ExtraLeaves<'_> {
    type Item = RopeChunk;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if !self.yielded_first {
            Some(self.yield_first())
        } else {
            self.yield_next()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let lo = (self.total - self.yielded) / RopeChunk::max_bytes();
        (lo, Some(lo + 1))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_off_0() {
        let mut r = RopeChunk::from("abcd");
        let rhs = unsafe { r.split_off_unchecked(3) };
        assert_eq!("abc", &*r);
        assert_eq!("d", &*rhs);
    }

    #[test]
    fn extra_leaves_0() {
        let mut extras =
            ExtraLeaves::new(Some("a".into()), "a".into(), "bcdefgh".into());

        assert_eq!("aabc", &*extras.next().unwrap());
        assert_eq!("def", &*extras.next().unwrap());
        assert_eq!("gh", &*extras.next().unwrap());
        assert_eq!(None, extras.next());
    }

    #[test]
    fn extra_leaves_1() {
        let mut extras =
            ExtraLeaves::new(Some("a".into()), "abcdefgh".into(), "".into());

        assert_eq!("aabc", &*extras.next().unwrap());
        assert_eq!("def", &*extras.next().unwrap());
        assert_eq!("gh", &*extras.next().unwrap());
        assert_eq!(None, extras.next());
    }

    #[test]
    fn extra_leaves_2() {
        let mut extras =
            ExtraLeaves::new(Some("a".into()), "abcdefgh".into(), "b".into());

        assert_eq!("aabc", &*extras.next().unwrap());
        assert_eq!("defg", &*extras.next().unwrap());
        assert_eq!("hb", &*extras.next().unwrap());
        assert_eq!(None, extras.next());
    }

    #[test]
    fn extra_leaves_3() {
        let mut extras = ExtraLeaves::new(None, "a".into(), "b".into());

        assert_eq!("ab", &*extras.next().unwrap());
        assert_eq!(None, extras.next());
    }

    #[test]
    fn extra_leaves_4() {
        let mut extras =
            ExtraLeaves::new(Some("a".into()), "b".into(), "".into());

        assert_eq!("ab", &*extras.next().unwrap());
        assert_eq!(None, extras.next());
    }
}
