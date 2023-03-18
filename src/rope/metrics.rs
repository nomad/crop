use core::ops::{Add, AddAssign, Sub, SubAssign};

use super::gap_buffer::{ChunkSummary, GapBuffer};
use super::gap_slice::GapSlice;
use super::utils::*;
use crate::tree::{
    DoubleEndedUnitMetric,
    Metric,
    SlicingMetric,
    Summarize,
    UnitMetric,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ByteMetric(pub(super) usize);

impl Add<Self> for ByteMetric {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl Sub for ByteMetric {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl AddAssign for ByteMetric {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        self.0 += other.0
    }
}

impl SubAssign for ByteMetric {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        self.0 -= other.0
    }
}

impl Add<usize> for ByteMetric {
    type Output = usize;

    #[inline]
    fn add(self, other: usize) -> usize {
        self.0 + other
    }
}

impl From<ByteMetric> for usize {
    #[inline]
    fn from(ByteMetric(value): ByteMetric) -> usize {
        value
    }
}

impl<const MAX_BYTES: usize> Metric<GapBuffer<MAX_BYTES>> for ByteMetric {
    #[inline]
    fn zero() -> Self {
        Self(0)
    }

    #[inline]
    fn one() -> Self {
        Self(1)
    }

    #[inline]
    fn measure(summary: &ChunkSummary) -> Self {
        Self(summary.bytes)
    }
}

impl<const MAX_BYTES: usize> SlicingMetric<GapBuffer<MAX_BYTES>>
    for ByteMetric
{
    #[inline]
    fn split<'a>(
        chunk: GapSlice<'a>,
        ByteMetric(byte_offset): Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        chunk.assert_char_boundary(byte_offset);

        if byte_offset <= chunk.len_left() {
            let line_breaks_left_left = if byte_offset <= chunk.len_left() / 2
            {
                count_line_breaks(&chunk.left_chunk()[..byte_offset]) as u16
            } else {
                chunk.line_breaks_left
                    - count_line_breaks(&chunk.left_chunk()[byte_offset..])
                        as u16
            };

            let line_breaks_left_right =
                chunk.line_breaks_left - line_breaks_left_left;

            let left = GapSlice {
                bytes: &chunk.bytes[..byte_offset],
                len_left: byte_offset as u16,
                line_breaks_left: line_breaks_left_left,
                len_right: 0,
            };

            let bytes = if byte_offset == chunk.len_left() {
                &chunk.bytes[chunk.bytes.len() - chunk.len_right()..]
            } else {
                &chunk.bytes[byte_offset..]
            };

            let right = GapSlice {
                bytes,
                len_left: chunk.len_left - left.len_left,
                line_breaks_left: line_breaks_left_right,
                len_right: chunk.len_right,
            };

            let left_summary = ChunkSummary {
                bytes: left.len(),
                line_breaks: line_breaks_left_left as usize,
            };

            let right_summary = ChunkSummary {
                bytes: right.len(),
                line_breaks: summary.line_breaks - left_summary.line_breaks,
            };

            (left, left_summary, right, right_summary)
        } else {
            let split_point = chunk.len_gap() + byte_offset;

            let left = GapSlice {
                bytes: &chunk.bytes[..split_point],
                len_left: chunk.len_left,
                line_breaks_left: chunk.line_breaks_left,
                len_right: byte_offset as u16 - chunk.len_left,
            };

            let right = GapSlice {
                bytes: &chunk.bytes[split_point..],
                len_left: 0,
                line_breaks_left: 0,
                len_right: chunk.len_right - left.len_right,
            };

            // Summarize the shorter side, then get the other summary by
            // subtracting it from the total.

            let (left_summary, right_summary) =
                if byte_offset < chunk.len() / 2 {
                    let left_summary = left.summarize();
                    let right_summary = summary - left_summary;
                    (left_summary, right_summary)
                } else {
                    let right_summary = right.summarize();
                    let left_summary = summary - right_summary;
                    (left_summary, right_summary)
                };

            (left, left_summary, right, right_summary)
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct RawLineMetric(pub(super) usize);

impl Add for RawLineMetric {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl Sub for RawLineMetric {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl AddAssign for RawLineMetric {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        self.0 += other.0
    }
}

impl SubAssign for RawLineMetric {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        self.0 -= other.0
    }
}

impl<const MAX_BYTES: usize> Metric<GapBuffer<MAX_BYTES>> for RawLineMetric {
    #[inline]
    fn zero() -> Self {
        Self(0)
    }

    #[inline]
    fn one() -> Self {
        Self(1)
    }

    #[inline]
    fn measure(summary: &ChunkSummary) -> Self {
        Self(summary.line_breaks)
    }
}

impl<const MAX_BYTES: usize> SlicingMetric<GapBuffer<MAX_BYTES>>
    for RawLineMetric
{
    #[inline]
    fn split<'a>(
        chunk: GapSlice<'a>,
        RawLineMetric(line_offset): Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (left, right) = chunk.split_at_line(line_offset);

        let left_summary =
            ChunkSummary { bytes: left.len(), line_breaks: line_offset };

        let right_summary = summary - left_summary;

        (left, left_summary, right, right_summary)
    }
}

impl<const MAX_BYTES: usize> UnitMetric<GapBuffer<MAX_BYTES>>
    for RawLineMetric
{
    #[inline]
    fn first_unit<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (first, first_summary, rest, rest_summary) =
            <Self as SlicingMetric<GapBuffer<MAX_BYTES>>>::split(
                chunk,
                RawLineMetric(1),
                summary,
            );

        (first, first_summary, first_summary, rest, rest_summary)
    }
}

impl<const MAX_BYTES: usize> DoubleEndedUnitMetric<GapBuffer<MAX_BYTES>>
    for RawLineMetric
{
    #[inline]
    fn last_unit<'a>(
        slice: GapSlice<'a>,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary, ChunkSummary)
    where
        'a: 'a,
    {
        let (rest, last, last_summary) = if slice.has_trailing_newline() {
            let (rest, last) = slice.split_at_line(summary.line_breaks - 1);

            let last_summary =
                ChunkSummary { bytes: last.len(), line_breaks: 1 };

            (rest, last, last_summary)
        } else {
            let (rest, last) = slice.split_at_line(summary.line_breaks);

            let last_summary =
                ChunkSummary { bytes: last.len(), line_breaks: 0 };

            (rest, last, last_summary)
        };

        let rest_summary = summary - last_summary;

        (rest, rest_summary, last, last_summary, last_summary)
    }

    #[inline]
    fn remainder<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        if chunk.has_trailing_newline() {
            (chunk, *summary, GapSlice::empty(), ChunkSummary::empty())
        } else {
            let (rest, rest_summary, last, last_summary, _) =
                <Self as DoubleEndedUnitMetric<GapBuffer<MAX_BYTES>>>::last_unit(chunk, summary);

            (rest, rest_summary, last, last_summary)
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct LineMetric(pub(super) usize);

impl Add for LineMetric {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl Sub for LineMetric {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl AddAssign for LineMetric {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        self.0 += other.0
    }
}

impl SubAssign for LineMetric {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        self.0 -= other.0
    }
}

impl<const MAX_BYTES: usize> Metric<GapBuffer<MAX_BYTES>> for LineMetric {
    #[inline]
    fn zero() -> Self {
        Self(0)
    }

    #[inline]
    fn one() -> Self {
        Self(1)
    }

    #[inline]
    fn measure(summary: &ChunkSummary) -> Self {
        Self(summary.line_breaks)
    }
}

impl<const MAX_BYTES: usize> UnitMetric<GapBuffer<MAX_BYTES>> for LineMetric {
    #[inline]
    fn first_unit<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (mut first, mut first_summary, advance, rest, rest_summary) =
            <RawLineMetric as UnitMetric<GapBuffer<MAX_BYTES>>>::first_unit(
                chunk, summary,
            );

        debug_assert!(first.has_trailing_newline());
        debug_assert_eq!(first_summary.line_breaks, 1);

        let bytes_removed = first.truncate_trailing_line_break();

        first_summary.bytes -= bytes_removed;
        first_summary.line_breaks = 0;

        (first, first_summary, advance, rest, rest_summary)
    }
}

impl<const MAX_BYTES: usize> DoubleEndedUnitMetric<GapBuffer<MAX_BYTES>>
    for LineMetric
{
    #[inline]
    fn last_unit<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary, ChunkSummary)
    where
        'a: 'a,
    {
        let (rest, rest_summary, mut last, mut last_summary, advance) =
            <RawLineMetric as DoubleEndedUnitMetric<GapBuffer<MAX_BYTES>>>::last_unit(chunk, summary);

        debug_assert_eq!(last_summary, advance);

        if last_summary.line_breaks == 0 {
            return (rest, rest_summary, last, last_summary, last_summary);
        }

        debug_assert!(last.has_trailing_newline());
        debug_assert_eq!(last_summary.line_breaks, 1);

        let bytes_removed = last.truncate_trailing_line_break();

        last_summary.bytes -= bytes_removed;
        last_summary.line_breaks = 0;

        (rest, rest_summary, last, last_summary, advance)
    }

    #[inline]
    fn remainder<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        <RawLineMetric as DoubleEndedUnitMetric<GapBuffer<MAX_BYTES>>>::remainder(chunk, summary)
    }
}
