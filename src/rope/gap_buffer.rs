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
        todo!();
    }
}

impl<const MAX_BYTES: usize> Default for GapBuffer<MAX_BYTES> {
    #[inline]
    fn default() -> Self {
        Self {
            bytes: Box::new([0u8; MAX_BYTES]),
            len_first_segment: 0,
            len_gap: MAX_BYTES as u16,
            len_second_segment: 0,
        }
    }
}

impl<const MAX_BYTES: usize> GapBuffer<MAX_BYTES> {
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
        todo!();
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

pub(super) struct StringSegmenter<'a, const MAX_BYTES: usize> {
    s: &'a str,
}

impl<'a, const MAX_BYTES: usize> StringSegmenter<'a, MAX_BYTES> {
    #[inline]
    pub(super) fn new(s: &'a str) -> Self {
        Self { s }
    }
}

impl<'a, const MAX_BYTES: usize> Iterator for StringSegmenter<'a, MAX_BYTES> {
    type Item = GapBuffer<MAX_BYTES>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        todo!();
    }
}
