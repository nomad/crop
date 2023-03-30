use core::ops::{Add, AddAssign, Sub, SubAssign};

use super::gap_buffer::{ChunkSummary, GapBuffer};
use super::gap_slice::GapSlice;
use super::utils::*;
use crate::tree::{DoubleEndedUnitMetric, Metric, SlicingMetric, UnitMetric};

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
    #[track_caller]
    #[inline]
    fn slice_up_to<'a>(
        chunk: GapSlice<'a>,
        ByteMetric(offset): Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        chunk.assert_char_boundary(offset);

        if offset <= chunk.len_left() {
            let line_breaks_left = if offset <= chunk.len_left() / 2 {
                count_line_breaks(&chunk.left_chunk()[..offset]) as u16
            } else {
                chunk.line_breaks_left
                    - count_line_breaks(&chunk.left_chunk()[offset..]) as u16
            };

            let slice = GapSlice {
                bytes: &chunk.bytes[..offset],
                len_left: offset as u16,
                line_breaks_left,
                len_right: 0,
            };

            let summary = ChunkSummary {
                bytes: slice.len(),
                line_breaks: line_breaks_left as usize,
            };

            (slice, summary)
        } else {
            let slice = GapSlice {
                bytes: &chunk.bytes[..offset + chunk.len_gap()],
                len_left: chunk.len_left,
                line_breaks_left: chunk.line_breaks_left,
                len_right: offset as u16 - chunk.len_left,
            };

            let offset = offset - chunk.len_left();

            let line_breaks_right = if offset <= chunk.len_right() / 2 {
                count_line_breaks(&chunk.right_chunk()[..offset])
            } else {
                summary.line_breaks
                    - slice.line_breaks_left as usize
                    - count_line_breaks(&chunk.right_chunk()[offset..])
            };

            let summary = ChunkSummary {
                bytes: slice.len(),
                line_breaks: slice.line_breaks_left as usize
                    + line_breaks_right,
            };

            (slice, summary)
        }
    }

    #[inline]
    fn slice_from<'a>(
        chunk: GapSlice<'a>,
        ByteMetric(offset): Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        if offset <= chunk.len_left() {
            let line_breaks_left = if offset <= chunk.len_left() / 2 {
                chunk.line_breaks_left
                    - count_line_breaks(&chunk.left_chunk()[..offset]) as u16
            } else {
                count_line_breaks(&chunk.left_chunk()[offset..]) as u16
            };

            let bytes = if offset == chunk.len_left() {
                &chunk.bytes[chunk.bytes.len() - chunk.len_right()..]
            } else {
                &chunk.bytes[offset..]
            };

            let slice = GapSlice {
                bytes,
                len_left: chunk.len_left - offset as u16,
                line_breaks_left,
                len_right: chunk.len_right,
            };

            let summary = ChunkSummary {
                bytes: slice.len(),
                line_breaks: summary.line_breaks
                    - chunk.line_breaks_left as usize
                    + slice.line_breaks_left as usize,
            };

            (slice, summary)
        } else {
            let bytes = &chunk.bytes[offset + chunk.len_gap()..];

            let slice = GapSlice {
                bytes,
                len_left: 0,
                line_breaks_left: 0,
                len_right: bytes.len() as u16,
            };

            let offset = offset - chunk.len_left();

            let line_breaks_right = if offset <= chunk.len_right() / 2 {
                summary.line_breaks
                    - chunk.line_breaks_left as usize
                    - count_line_breaks(&chunk.right_chunk()[..offset])
            } else {
                count_line_breaks(&chunk.right_chunk()[offset..])
            };

            let summary = ChunkSummary {
                bytes: slice.len(),
                line_breaks: line_breaks_right,
            };

            (slice, summary)
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
    fn slice_up_to<'a>(
        chunk: GapSlice<'a>,
        RawLineMetric(line_offset): Self,
        _: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (slice, _) = chunk.split_at_line(line_offset);

        let summary =
            ChunkSummary { bytes: slice.len(), line_breaks: line_offset };

        (slice, summary)
    }

    #[inline]
    fn slice_from<'a>(
        chunk: GapSlice<'a>,
        RawLineMetric(line_offset): Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (_, slice) = chunk.split_at_line(line_offset);

        let summary = ChunkSummary {
            bytes: slice.len(),
            line_breaks: summary.line_breaks - line_offset,
        };

        (slice, summary)
    }
}

impl<const MAX_BYTES: usize> UnitMetric<GapBuffer<MAX_BYTES>>
    for RawLineMetric
{
    #[inline]
    fn first_unit<'a>(
        chunk: GapSlice<'a>,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (first, rest) = chunk.split_at_line(1);

        let first_summary =
            ChunkSummary { bytes: first.len(), line_breaks: 1 };

        (first, first_summary, first_summary, rest, summary - first_summary)
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
