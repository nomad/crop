use std::ops::{Add, AddAssign, Range, RangeBounds, Sub, SubAssign};

use super::chunk_slice::ChunkSlice;
use super::metrics::ByteMetric;
use super::utils::*;
use crate::range_bounds_to_start_end;
use crate::tree::{BalancedLeaf, Leaf, ReplaceableLeaf, Summarize};

#[cfg(all(not(test), not(feature = "integration_tests")))]
const ROPE_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(any(test, feature = "integration_tests"))]
const ROPE_CHUNK_MAX_BYTES: usize = 4;

const ROPE_CHUNK_MIN_BYTES: usize = ROPE_CHUNK_MAX_BYTES / 2;

#[derive(Clone, PartialEq)]
pub(super) struct RopeChunk {
    pub(super) text: String,
}

impl std::fmt::Debug for RopeChunk {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.text)
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

    /// TODO: docs
    pub(super) fn is_within_chunk_bounds(&self) -> bool {
        self.len() >= Self::chunk_min() && self.len() <= Self::chunk_max()
    }

    /// # Safety
    ///
    /// TODO:
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
        unsafe { self.split_off_unchecked(split_at) }
    }

    /// Splits the chunk at the given byte offset, returning the right side of
    /// the split. The chunk will have `byte_offset` bytes after splitting.
    ///
    /// # Safety
    ///
    /// The function is unsafe because it does not check that `byte_offset` is
    /// a valid char boundary, leaving that up to the caller.
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
        let (a, b) = Self::balance_slices(
            (left.as_slice(), left_summary),
            (right.as_slice(), right_summary),
        );

        *left = a.0;
        *left_summary = a.1;

        let b = b.unwrap_or_default();

        *right = b.0;
        *right_summary = b.1;
    }

    #[inline]
    fn balance_slices<'a>(
        (left, &left_summary): (&'a ChunkSlice, &'a ChunkSummary),
        (right, &right_summary): (&'a ChunkSlice, &'a ChunkSummary),
    ) -> ((Self, ChunkSummary), Option<(Self, ChunkSummary)>) {
        ChunkSlice::balance(left, left_summary, right, right_summary)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rope_chunk_split_off() {
        let mut r = RopeChunk::from("abcd");
        let rhs = unsafe { r.split_off_unchecked(3) };
        assert_eq!("abc", &*r);
        assert_eq!("d", &*rhs);
    }
}

use extra_leaves::ExtraLeaves;

mod extra_leaves {
    use super::*;

    /// TODO: docs
    #[derive(Debug)]
    pub(super) struct ExtraLeaves<'a> {
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
        /// Panics if `first`, `slice` and `last` combined are less than
        /// [`RopeChunk::chunk_min()`].
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
                    let mut add_to_first =
                        RopeChunk::max_bytes() - first.len();

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

                        let take_from_last = adjust_split_point::<true>(
                            self.last,
                            add_to_first,
                        );
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
