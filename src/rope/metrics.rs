use std::ops::{Add, AddAssign, Sub, SubAssign};

use super::gap_buffer::{ChunkSummary, GapBuffer};
use super::gap_slice::GapSlice;
use super::utils::*;
use crate::tree::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ByteMetric(pub(super) usize);

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
        ByteMetric(up_to): Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        if up_to == chunk.len() {
            (chunk, summary, GapSlice::empty(), ChunkSummary::empty())
        } else {
            let (left, right) = chunk.split_at_offset(up_to);

            // Summarize the shorter side, then get the other summary by
            // subtracting it from the total.

            let (left_summary, right_summary) = if up_to < chunk.len() / 2 {
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
        let byte_offset = chunk.byte_of_line(line_offset);

        let (left, right) = chunk.split_at_offset(byte_offset);

        let left_summary =
            ChunkSummary { bytes: byte_offset, line_breaks: line_offset };

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
        let mut last_summary =
            ChunkSummary { bytes: summary.bytes, line_breaks: 0 };

        let bytes = slice
            .first_segment()
            .bytes()
            .chain(slice.second_segment().bytes());

        for (idx, byte) in bytes.rev().enumerate() {
            if byte == b'\n' {
                if idx == 0 {
                    last_summary.line_breaks = 1;

                    // // Increase the line break count in the left chunk if the
                    // // last byte is a newline and it belongs to the left chunk
                    // // of the slice.
                    // if slice.len_second_segment() == 0 {
                    //     last_summary.line_breaks_left_chunk = 1;
                    // }
                } else {
                    last_summary.bytes = idx;
                    break;
                }
            }
        }

        let (rest, last) =
            slice.split_at_offset(slice.len() - last_summary.bytes);

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

        let bytes_line_break = bytes_line_break(first.last_segment());

        first = first.byte_slice(..first.len() - bytes_line_break);
        first_summary.bytes -= bytes_line_break;
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

        let bytes_line_break = bytes_line_break(last.last_segment());

        last = last.byte_slice(..last.len() - bytes_line_break);
        last_summary.bytes -= bytes_line_break;
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
