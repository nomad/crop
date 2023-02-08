use std::fmt::{self, Debug};
use std::ops::{Add, AddAssign, Range, Sub, SubAssign};
use std::str;

use super::metrics::ByteMetric;
use super::utils::*;
use crate::tree::{Leaf, ReplaceableLeaf, Summarize};

#[cfg(all(not(test), not(feature = "integration_tests")))]
const ROPE_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(any(test, feature = "integration_tests"))]
const ROPE_CHUNK_MAX_BYTES: usize = 4;

const ROPE_CHUNK_MIN_BYTES: usize = ROPE_CHUNK_MAX_BYTES / 2;

#[derive(Clone)]
pub(super) struct RopeChunk {
    pub(super) text: String,
}

impl Debug for RopeChunk {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

impl Summarize for RopeChunk {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        ChunkSummary {
            bytes: self.text.len(),
            line_breaks: str_indices::lines_lf::count_breaks(&self.text),
        }
    }
}

impl Leaf for RopeChunk {
    type BaseMetric = ByteMetric;

    type Slice = ChunkSlice;

    #[inline]
    fn is_big_enough(&self, summary: &ChunkSummary) -> bool {
        summary.bytes >= RopeChunk::min_bytes()
    }

    #[inline]
    fn balance_slices<'a>(
        (left, left_summary): (&'a ChunkSlice, &'a ChunkSummary),
        (right, right_summary): (&'a ChunkSlice, &'a ChunkSummary),
    ) -> ((Self, ChunkSummary), Option<(Self, ChunkSummary)>) {
        if left.len() >= Self::min_bytes() && right.len() >= Self::min_bytes()
        {
            (
                (left.to_owned(), *left_summary),
                Some((right.to_owned(), *right_summary)),
            )
        }
        // If both slices can fit in a single chunk we join them.
        else if left.len() + right.len() <= Self::max_bytes() {
            let mut left = left.to_owned();
            left.push_str(right);

            let mut left_summary = *left_summary;
            left_summary += right_summary;

            ((left, left_summary), None)
        }
        // If the left side is lacking we take text from the right side.
        else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let (left, right) = balance_left_with_right(
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
            debug_assert!(right.len() < Self::min_bytes());
            debug_assert!(left.len() > Self::min_bytes());

            let (left, right) = balance_right_with_left(
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
    #[inline]
    fn replace(
        &mut self,
        summary: &mut ChunkSummary,
        Range { start: ByteMetric(start), end: ByteMetric(end) }: Range<
            ByteMetric,
        >,
        slice: &ChunkSlice,
    ) -> Option<(Self, ChunkSummary)> {
        if end > start {
            let removed: &ChunkSlice = self[start..end].into();
            *summary -= &removed.summarize();
        }

        *summary += &slice.summarize();

        self.replace_range(start..end, slice);

        if self.len() > Self::max_bytes() {
            todo!();
        } else {
            None
        }
    }
}

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

impl From<&str> for &ChunkSlice {
    #[inline]
    fn from(text: &str) -> Self {
        // SAFETY: a `ChunkSlice` has the same layout as a `str`.
        unsafe { &*(text as *const str as *const ChunkSlice) }
    }
}

impl std::ops::Deref for ChunkSlice {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.text
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

impl ToOwned for ChunkSlice {
    type Owned = RopeChunk;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        RopeChunk { text: self.text.to_owned() }
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
        self += &rhs;
        self
    }
}

impl Sub<Self> for ChunkSummary {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: Self) -> Self {
        self -= &rhs;
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

impl AddAssign<&Self> for ChunkSummary {
    #[inline]
    fn add_assign(&mut self, rhs: &Self) {
        self.bytes += rhs.bytes;
        self.line_breaks += rhs.line_breaks;
    }
}

impl SubAssign<&Self> for ChunkSummary {
    #[inline]
    fn sub_assign(&mut self, rhs: &Self) {
        self.bytes -= rhs.bytes;
        self.line_breaks -= rhs.line_breaks;
    }
}

pub(super) struct RopeChunkIter<'a> {
    text: &'a str,
    yielded: usize,
}

impl<'a> RopeChunkIter<'a> {
    #[inline]
    pub(super) fn new(text: &'a str) -> Self {
        Self { text, yielded: 0 }
    }
}

impl<'a> Iterator for RopeChunkIter<'a> {
    type Item = &'a str;

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

        Some(chunk)
    }
}
