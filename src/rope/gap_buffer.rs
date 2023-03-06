use std::ops::{Add, AddAssign, Range, RangeBounds, Sub, SubAssign};

use super::gap_slice::GapSlice;
use super::metrics::ByteMetric;
use super::utils::*;
use crate::range_bounds_to_start_end;
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
            len_second_segment: 0,
        }
    }
}

impl<const MAX_BYTES: usize> From<&str> for GapBuffer<MAX_BYTES> {
    /// # Panics
    ///
    /// Panics if the string is empty or if its byte length is greater than
    /// `MAX_BYTES`.
    #[inline]
    fn from(s: &str) -> Self {
        debug_assert!(!s.is_empty());
        debug_assert!(s.len() <= MAX_BYTES);
        Self::from_segments(&[s])
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

    /// TODO: docs
    ///
    /// # Panics
    ///
    /// Panics if the combined byte length of all the segments is zero or if
    /// it's greater than `MAX_BYTES`.
    ///
    /// TODO: examples
    #[inline]
    fn from_segments(segments: &[&str]) -> Self {
        let total_len = segments.iter().map(|s| s.len() as u16).sum::<u16>();

        debug_assert!(total_len > 0);
        debug_assert!(total_len <= MAX_BYTES as u16);

        let add_to_first = total_len / 2;

        let mut bytes = Box::new([0u8; MAX_BYTES]);

        let mut len_first_segment = 0;

        let mut segments = segments.iter();

        for &segment in segments.by_ref() {
            if len_first_segment + segment.len() as u16 <= add_to_first {
                let range = {
                    let start = len_first_segment as usize;
                    let end = start + segment.len();
                    start..end
                };

                bytes[range].copy_from_slice(segment.as_bytes());

                len_first_segment += segment.len() as u16;
            } else {
                let (to_first, to_second) = split_adjusted::<true>(
                    segment,
                    (add_to_first - len_first_segment) as usize,
                );

                let range = {
                    let start = len_first_segment as usize;
                    let end = start + to_first.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_first.as_bytes());

                len_first_segment += to_first.len() as u16;

                let len_second_segment = total_len - len_first_segment;

                let mut start = MAX_BYTES as u16 - len_second_segment;

                let range = {
                    let start = start as usize;
                    let end = start + to_second.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_second.as_bytes());

                start += to_second.len() as u16;

                for &segment in segments {
                    let range = {
                        let start = start as usize;
                        let end = start + segment.len();
                        start..end
                    };

                    bytes[range].copy_from_slice(segment.as_bytes());

                    start += segment.len() as u16;
                }

                return Self { bytes, len_first_segment, len_second_segment };
            }
        }

        unreachable!("This can only be reached if the total length is zero");
    }

    /// Returns `true` if it ends with a newline (either LF or CRLF).
    #[inline]
    pub(super) fn has_trailing_newline(&self) -> bool {
        last_byte_is_newline(self.last_segment())
    }

    /// Inserts the string at the given byte offset, moving the gap to the new
    /// insertion point if necessary.
    ///
    /// # Panics
    ///
    /// Panics if the byte offset is not a char boundary of if the byte length
    /// of the string is greater than the length of the gap.
    #[inline]
    pub(super) fn insert(&mut self, insert_at: usize, s: &str) {
        debug_assert!(self.is_char_boundary(insert_at));
        debug_assert!(s.len() <= self.len_gap());

        // The insertion point splits the first segment => move all the
        // text after the insertion to the start of the second segment.
        //
        // aa|bb~~~ccc => aa~~~bbccc
        if insert_at < self.len_first_segment() {
            let move_range = insert_at..self.len_first_segment();
            let len_moved = self.len_first_segment() - insert_at;
            self.len_second_segment += len_moved as u16;
            let start = MAX_BYTES - self.len_second_segment();
            self.bytes.copy_within(move_range, start);
            self.len_first_segment -= len_moved as u16;
        }
        // The insertion point splits the second segment => move all the
        // text before the insertion to the end of the first segment.
        //
        // aaa~~~bb|cc => aaabb~~cc
        else if insert_at > self.len_first_segment() {
            let len_moved = insert_at - self.len_first_segment();
            let move_range = {
                let start = MAX_BYTES - self.len_second_segment();
                let end = start + len_moved;
                start..end
            };
            let start = self.len_first_segment();
            self.bytes.copy_within(move_range, start);
            self.len_first_segment += len_moved as u16;
            self.len_second_segment -= len_moved as u16;
        }

        debug_assert_eq!(insert_at, self.len_first_segment());

        let insert_range = {
            let start = self.len_first_segment();
            let end = start + s.len();
            start..end
        };

        self.bytes[insert_range].copy_from_slice(s.as_bytes());
        self.len_first_segment += s.len() as u16;
    }

    #[inline]
    fn is_char_boundary(&self, byte_offset: usize) -> bool {
        debug_assert!(byte_offset <= self.len());

        if byte_offset <= self.len_first_segment() {
            self.first_segment().is_char_boundary(byte_offset)
        } else {
            self.second_segment()
                .is_char_boundary(byte_offset - self.len_first_segment())
        }
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
    fn len_gap(&self) -> usize {
        MAX_BYTES - self.len_first_segment() - self.len_second_segment()
    }

    #[inline]
    fn len_second_segment(&self) -> usize {
        self.len_second_segment as _
    }

    // #[inline]
    // fn len_trailing_gap(&self) -> usize {
    //     MAX_BYTES - self.len_middle_gap() - self.len()
    // }

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
        debug_assert_eq!(self.len_gap(), 0);
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

impl ChunkSummary {
    #[inline]
    pub(super) fn empty() -> Self {
        Self::default()
    }

    #[inline]
    pub(super) fn from_str(s: &str) -> Self {
        Self {
            bytes: s.len(),
            line_breaks: str_indices::lines_lf::count_breaks(s),
        }
    }
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
        // In the general case the slice will have less than `MAX_BYTES` bytes.
        //
        // We create an owned `GapBuffer` by splitting the bytes of the slice
        // equally between the first and second segments. Any remaining space
        // is left as a middle gap.

        let mut buffer = Self {
            bytes: Box::new([0u8; MAX_BYTES]),
            len_first_segment: 0,
            len_second_segment: 0,
        };

        let target_len_first = slice.len() / 2;

        let mut second_segment = slice.second_segment();

        if slice.len_first_segment() >= target_len_first {
            // Add everything up to the target to our first segment, then add
            // the rest to our second segment.

            let to_first = adjust_split_point::<true>(
                slice.first_segment(),
                target_len_first,
            );

            buffer.bytes[..to_first].copy_from_slice(
                &slice.first_segment().as_bytes()[..to_first],
            );

            buffer.len_first_segment = to_first as u16;

            let range = {
                let to_second = slice.len_first_segment() - to_first;
                let end = MAX_BYTES - second_segment.len();
                let start = end - to_second;
                start..end
            };

            buffer.bytes[range].copy_from_slice(
                &slice.first_segment().as_bytes()[to_first..],
            );

            buffer.len_second_segment =
                (slice.len_first_segment() - to_first) as u16;
        } else {
            // Add the slice's first segment plus part of its second segment to
            // our first segment.

            buffer.bytes[..slice.len_first_segment()]
                .copy_from_slice(slice.first_segment().as_bytes());

            let space_left_on_first =
                target_len_first - slice.len_first_segment();

            let (to_first, rest) =
                split_adjusted::<true>(second_segment, space_left_on_first);

            let range = {
                let start = slice.len_first_segment();
                let end = start + to_first.len();
                start..end
            };

            buffer.bytes[range].copy_from_slice(to_first.as_bytes());

            buffer.len_first_segment =
                (slice.len_first_segment() + to_first.len()) as u16;

            second_segment = rest;
        }

        buffer.bytes[MAX_BYTES - second_segment.len()..]
            .copy_from_slice(second_segment.as_bytes());

        buffer.len_second_segment += second_segment.len() as u16;

        buffer
    }
}

impl<const MAX_BYTES: usize> AsSlice for GapBuffer<MAX_BYTES> {
    type Slice<'a> = GapSlice<'a>;

    #[inline]
    fn as_slice(&self) -> GapSlice<'_> {
        let range = match (
            self.len_first_segment() > 0,
            self.len_second_segment() > 0,
        ) {
            (true, true) => 0..MAX_BYTES,
            (true, false) => 0..self.len_first_segment(),
            (false, true) => MAX_BYTES - self.len_second_segment()..MAX_BYTES,
            (false, false) => 0..0,
        };

        GapSlice {
            bytes: &self.bytes[range],
            len_first_segment: self.len_first_segment,
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
        if left.len() + right.len() <= MAX_BYTES {
            // aa--bbb + c-----ddd
            //
            // tot is 2 + 3 +  1 + 3 = 9 / 2 = 4, 5
            //
            // aabb---bcddd
            //
            // this is basically the same as from_segments except the first
            // segment is owned
        } else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing = Self::min_bytes() - left.len();

            // we have to take 5 bytes from right
            // we have to  push them

            // 1. move all of left's second segment to first
            // 2. move min(len, 5) from right's first to left's second
            // 3. this is fucking ugly ngl

            // missin
            todo!();
        } else if right.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing = Self::min_bytes() - right.len();
        }
    }

    #[inline]
    fn balance_slices(
        (left, &left_summary): (GapSlice<'_>, &ChunkSummary),
        (right, &right_summary): (GapSlice<'_>, &ChunkSummary),
    ) -> ((Self, ChunkSummary), Option<(Self, ChunkSummary)>) {
        // Neither side is underfilled.
        if left.len() >= Self::min_bytes() && right.len() >= Self::min_bytes()
        {
            ((left.into(), left_summary), Some((right.into(), right_summary)))
        }
        // The two slices can be combined in a single chunk.
        else if left.len() + right.len() <= MAX_BYTES {
            let combined = Self::from_segments(&[
                left.first_segment(),
                left.second_segment(),
                right.first_segment(),
                right.second_segment(),
            ]);

            ((combined, left_summary + right_summary), None)
        }
        // The left side is underfilled -> take text from the right side.
        else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing = Self::min_bytes() - left.len();

            if right.len_first_segment() >= missing {
                let (to_left, keep_right) =
                    split_adjusted::<true>(right.first_segment(), missing);

                let to_left_summary = ChunkSummary::from_str(to_left);

                let left = Self::from_segments(&[
                    left.first_segment(),
                    left.second_segment(),
                    to_left,
                ]);

                let right =
                    Self::from_segments(&[keep_right, right.second_segment()]);

                (
                    (left, left_summary + to_left_summary),
                    Some((right, right_summary - to_left_summary)),
                )
            } else {
                let missing = missing - right.len_first_segment();

                let (to_left, keep_right) =
                    split_adjusted::<true>(right.second_segment(), missing);

                let to_left_summary =
                    ChunkSummary::from_str(right.first_segment())
                        + ChunkSummary::from_str(to_left);

                let left = Self::from_segments(&[
                    left.first_segment(),
                    left.second_segment(),
                    right.first_segment(),
                    to_left,
                ]);

                let right = Self::from_segments(&[keep_right]);

                (
                    (left, left_summary + to_left_summary),
                    Some((right, right_summary - to_left_summary)),
                )
            }
        }
        // The right side is underfilled -> take text from the left side.
        else if right.len() < Self::min_bytes() {
            debug_assert!(left.len() > Self::min_bytes());

            let missing = Self::min_bytes() - right.len();

            if left.len_second_segment() >= missing {
                let (keep_left, to_right) = split_adjusted::<true>(
                    left.second_segment(),
                    left.len_second_segment() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right);

                let left =
                    Self::from_segments(&[left.first_segment(), keep_left]);

                let right = Self::from_segments(&[
                    to_right,
                    right.first_segment(),
                    right.second_segment(),
                ]);

                (
                    (left, left_summary - to_right_summary),
                    Some((right, right_summary + to_right_summary)),
                )
            } else {
                let missing = missing - left.len_second_segment();

                let (keep_left, to_right) = split_adjusted::<true>(
                    left.first_segment(),
                    left.len_first_segment() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right)
                    + ChunkSummary::from_str(left.second_segment());

                let right = Self::from_segments(&[
                    to_right,
                    left.second_segment(),
                    right.first_segment(),
                    right.second_segment(),
                ]);

                let left = Self::from_segments(&[keep_left]);

                (
                    (left, left_summary - to_right_summary),
                    Some((right, right_summary + to_right_summary)),
                )
            }
        } else {
            unreachable!();
        }
    }
}

impl<const MAX_BYTES: usize> ReplaceableLeaf<ByteMetric>
    for GapBuffer<MAX_BYTES>
{
    type Replacement<'a> = &'a str;
    type ExtraLeaves = std::vec::IntoIter<Self>;

    #[inline]
    fn replace<R>(
        &mut self,
        summary: &mut ChunkSummary,
        range: R,
        mut s: &str,
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

        // len - end + start + s.len() <= MAX
        // MAX - gap - end + start + s.len() <= MAX
        // s.len() + (end - start) <= gap

        if s.len() + (end - start) <= self.len_gap() {
            match (end > start, !s.is_empty()) {
                // (true, true) => self.replace(&mut summary, start..end, s),
                (true, true) => todo!(),

                // (true, false) => self.delete(&mut summary, start..end),
                (true, false) => todo!(),

                (false, true) => {
                    *summary += ChunkSummary::from_str(s);
                    self.insert(start, s)
                },

                (false, false) => {},
            }

            return None;
        }

        // This shouldn't be too too different from the contiguous case, except
        // it is.

        todo!();
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

            chunk_len = adjust_split_point::<false>(
                &self.s[self.yielded..],
                chunk_len,
            );

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
