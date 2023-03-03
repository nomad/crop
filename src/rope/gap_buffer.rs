use std::ops::{Add, AddAssign, Range, RangeBounds, Sub, SubAssign};

use super::gap_slice::GapSlice;
use super::metrics::ByteMetric;
use super::utils::*;
use crate::tree::{
    AsSlice,
    BalancedLeaf,
    BaseMeasured,
    ReplaceableLeaf,
    Summarize,
};

/// A gap buffer with a max capacity of `2^16 - 1` bytes.
///
/// A gap buffer with two gaps, one in the middle and one at the end.
///
/// The second gap being at the end means that we still have 2 segments, not 3.
///
/// "Off this wave" -> "Off [   ]this wave[  ]"
#[derive(Clone, PartialEq)]
pub(super) struct GapBuffer<const MAX_BYTES: usize> {
    bytes: Box<[u8; MAX_BYTES]>,
    len_first_segment: u16,
    len_gap: u16,
    len_second_segment: u16,
}

impl<const MAX_BYTES: usize> std::fmt::Debug for GapBuffer<MAX_BYTES> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.as_slice(), f)
    }
}

impl<const MAX_BYTES: usize> Default for GapBuffer<MAX_BYTES> {
    #[inline]
    fn default() -> Self {
        Self {
            bytes: Box::new([0u8; MAX_BYTES]),
            len_first_segment: 0,
            len_gap: 0,
            len_second_segment: 0,
        }
    }
}

impl<const MAX_BYTES: usize> From<&str> for GapBuffer<MAX_BYTES> {
    /// # Panics
    ///
    /// Panics if the byte length of the string is greater than `MAX_BYTES`.
    #[inline]
    fn from(s: &str) -> Self {
        debug_assert!(s.len() <= MAX_BYTES);

        let bytes = {
            let mut b = Box::new([0u8; MAX_BYTES]);
            b[0..s.len()].copy_from_slice(s.as_bytes());
            b
        };

        Self {
            bytes,
            len_first_segment: s.len() as u16,
            len_gap: 0,
            len_second_segment: 0,
        }
    }
}

impl<const MAX_BYTES: usize> GapBuffer<MAX_BYTES> {
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

    #[inline]
    pub(super) fn chunk_segmenter(s: &str) -> ChunkSegmenter<'_, MAX_BYTES> {
        ChunkSegmenter { s, yielded: 0 }
    }

    #[inline]
    fn first_segment(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the bytes in
        // the first segment as valid UTF-8.
        unsafe {
            std::str::from_utf8_unchecked(
                &self.bytes[..self.len_first_segment()],
            )
        }
    }

    /// Returns `true` if it ends with a newline (either LF or CRLF).
    #[inline]
    pub(super) fn has_trailing_newline(&self) -> bool {
        last_byte_is_newline(self.last_segment())
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The second segment if it's not empty, or the first one otherwise.
    #[inline]
    pub(super) fn last_segment(&self) -> &str {
        if !self.second_segment().is_empty() {
            self.second_segment()
        } else {
            self.first_segment()
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.len_first_segment() + self.len_second_segment()
    }

    #[inline]
    fn len_first_segment(&self) -> usize {
        self.len_first_segment as _
    }

    #[inline]
    fn len_middle_gap(&self) -> usize {
        self.len_gap as _
    }

    #[inline]
    fn len_second_segment(&self) -> usize {
        self.len_second_segment as _
    }

    #[inline]
    fn len_trailing_gap(&self) -> usize {
        MAX_BYTES - self.len_middle_gap() - self.len()
    }

    /// The number of bytes `RopeChunk`s should aim to stay over.
    pub(super) const fn min_bytes() -> usize {
        MAX_BYTES / 2
    }

    /// Pushes as mush of the slice as possible into this chunk, returning the
    /// rest (if any).
    pub(super) fn push_with_remainder<'a>(
        &mut self,
        s: &'a str,
    ) -> Option<&'a str> {
        debug_assert!(s.len() <= MAX_BYTES);
        debug_assert_eq!(self.len_middle_gap(), 0);
        debug_assert_eq!(self.len_second_segment(), 0);

        let space_left = MAX_BYTES - self.len_first_segment();
        let (push, rest) = split_adjusted::<false>(s, space_left);

        debug_assert!(push.len() <= space_left);

        let pushed_range = {
            let start = self.len_first_segment();
            let end = start + push.len();
            start..end
        };

        self.bytes[pushed_range].copy_from_slice(push.as_bytes());
        self.len_first_segment += push.len() as u16;

        (!rest.is_empty()).then_some(rest)
    }

    #[inline]
    fn second_segment(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the bytes in
        // the second segment as valid UTF-8.
        unsafe {
            std::str::from_utf8_unchecked(
                &self.bytes[..self.len_first_segment()],
            )
        }
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

impl<const MAX_BYTES: usize> Summarize for GapBuffer<MAX_BYTES> {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        self.as_slice().summarize()
    }
}

impl<const MAX_BYTES: usize> BaseMeasured for GapBuffer<MAX_BYTES> {
    type BaseMetric = ByteMetric;
}

impl<const MAX_BYTES: usize> From<GapSlice<'_>> for GapBuffer<MAX_BYTES> {
    #[inline]
    fn from(slice: GapSlice<'_>) -> Self {
        todo!();
    }
}

impl<const MAX_BYTES: usize> AsSlice for GapBuffer<MAX_BYTES> {
    type Slice<'a> = GapSlice<'a>;

    #[inline]
    fn as_slice(&self) -> GapSlice<'_> {
        GapSlice {
            bytes: &*self.bytes,
            len_first_segment: self.len_first_segment,
            len_gap: self.len_gap,
            len_second_segment: self.len_second_segment,
        }
    }
}

impl<const MAX_BYTES: usize> BalancedLeaf for GapBuffer<MAX_BYTES> {
    #[inline]
    fn is_underfilled(_: GapSlice<'_>, summary: &ChunkSummary) -> bool {
        summary.bytes < Self::min_bytes()
    }

    #[inline]
    fn balance_leaves(
        (left, left_summary): (&mut Self, &mut ChunkSummary),
        (right, right_summary): (&mut Self, &mut ChunkSummary),
    ) {
        todo!();
    }

    #[inline]
    fn balance_slices(
        (left, &left_summary): (GapSlice<'_>, &ChunkSummary),
        (right, &right_summary): (GapSlice<'_>, &ChunkSummary),
    ) -> ((Self, ChunkSummary), Option<(Self, ChunkSummary)>) {
        todo!();
    }
}

impl<const MAX_BYTES: usize> ReplaceableLeaf<ByteMetric>
    for GapBuffer<MAX_BYTES>
{
    type ExtraLeaves = std::vec::IntoIter<Self>;

    #[inline]
    fn replace<R>(
        &mut self,
        summary: &mut ChunkSummary,
        range: R,
        mut slice: GapSlice<'_>,
    ) -> Option<Self::ExtraLeaves>
    where
        R: RangeBounds<ByteMetric>,
    {
        todo!();
    }

    #[inline]
    fn remove(&mut self, summary: &mut ChunkSummary, up_to: ByteMetric) {
        todo!();
        // let extra = self.replace(summary, ..up_to, "".into());
        // debug_assert!(extra.is_none());
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
pub(super) struct ChunkSegmenter<'a, const MAX_BYTES: usize> {
    s: &'a str,
    yielded: usize,
}

impl<'a, const MAX_BYTES: usize> Iterator for ChunkSegmenter<'a, MAX_BYTES> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut remaining = self.s.len() - self.yielded;

        let chunk = if remaining == 0 {
            return None;
        } else if remaining > MAX_BYTES {
            let mut chunk_len = MAX_BYTES;

            remaining -= chunk_len;

            let min = GapBuffer::<MAX_BYTES>::min_bytes();

            if remaining < min {
                chunk_len -= min - remaining;
            }

            chunk_len =
                adjust_split_point::<true>(&self.s[self.yielded..], chunk_len);

            &self.s[self.yielded..(self.yielded + chunk_len)]
        } else {
            debug_assert!(
                self.yielded == 0
                    || remaining >= GapBuffer::<MAX_BYTES>::chunk_min()
            );

            &self.s[self.s.len() - remaining..]
        };

        self.yielded += chunk.len();

        Some(chunk)
    }
}

impl<const MAX_BYTES: usize> std::iter::FusedIterator
    for ChunkSegmenter<'_, MAX_BYTES>
{
}
