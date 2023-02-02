use std::ops::{Add, AddAssign, Sub, SubAssign};

use super::utils::*;
use super::{ChunkSlice, ChunkSummary, RopeChunk};
use crate::tree::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ByteMetric(pub(super) usize);

impl Add for ByteMetric {
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

impl Metric<RopeChunk> for ByteMetric {
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

impl SlicingMetric<RopeChunk> for ByteMetric {
    #[inline]
    fn split<'a>(
        chunk: &'a ChunkSlice,
        ByteMetric(up_to): Self,
        _: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary, &'a ChunkSlice, ChunkSummary) {
        let left = chunk[..up_to].into();
        let right = chunk[up_to..].into();
        (left, left.summarize(), right, right.summarize())
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

impl Metric<RopeChunk> for RawLineMetric {
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

impl SlicingMetric<RopeChunk> for RawLineMetric {
    #[inline]
    fn split<'a>(
        chunk: &'a ChunkSlice,
        RawLineMetric(at): Self,
        summary: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary, &'a ChunkSlice, ChunkSummary) {
        split_slice_at_line_break(chunk, at, summary)
    }
}

impl UnitMetric<RopeChunk> for RawLineMetric {
    #[inline]
    fn first_unit<'a>(
        chunk: &'a ChunkSlice,
        summary: &ChunkSummary,
    ) -> (
        &'a ChunkSlice,
        ChunkSummary,
        ChunkSummary,
        &'a ChunkSlice,
        ChunkSummary,
    ) {
        let (first, first_summary, rest, rest_summary) =
            Self::split(chunk, RawLineMetric(1), summary);

        (first, first_summary, first_summary, rest, rest_summary)
    }
}

impl DoubleEndedUnitMetric<RopeChunk> for RawLineMetric {
    #[inline]
    fn last_unit<'a>(
        chunk: &'a ChunkSlice,
        summary: &ChunkSummary,
    ) -> (
        &'a ChunkSlice,
        ChunkSummary,
        &'a ChunkSlice,
        ChunkSummary,
        ChunkSummary,
    ) {
        let mut last_summary =
            ChunkSummary { bytes: summary.bytes, line_breaks: 0 };

        for (idx, byte) in chunk.bytes().rev().enumerate() {
            if byte == b'\n' {
                if idx == 0 {
                    last_summary.line_breaks = 1;
                } else {
                    last_summary.bytes = idx;
                    break;
                }
            }
        }

        let last = chunk[chunk.len() - last_summary.bytes..].into();

        let rest = chunk[..chunk.len() - last_summary.bytes].into();

        let rest_summary = ChunkSummary {
            bytes: chunk.len() - last_summary.bytes,
            line_breaks: summary.line_breaks - last_summary.line_breaks,
        };

        (rest, rest_summary, last, last_summary, last_summary)
    }

    #[inline]
    fn remainder<'a>(
        chunk: &'a ChunkSlice,
        summary: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary, &'a ChunkSlice, ChunkSummary) {
        let mut remainder_summary =
            ChunkSummary { bytes: summary.bytes, line_breaks: 0 };

        let bytes = chunk.as_bytes().iter();

        for (idx, &byte) in bytes.rev().enumerate() {
            if byte == b'\n' {
                remainder_summary.bytes = idx;
                break;
            }
        }

        let remainder =
            chunk[summary.bytes - remainder_summary.bytes..].into();

        let rest = chunk[..chunk.len() - remainder_summary.bytes].into();

        let rest_summary = ChunkSummary {
            bytes: summary.bytes - remainder_summary.bytes,
            line_breaks: summary.line_breaks,
        };

        (rest, rest_summary, remainder, remainder_summary)
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

impl Metric<RopeChunk> for LineMetric {
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

impl UnitMetric<RopeChunk> for LineMetric {
    #[inline]
    fn first_unit<'a>(
        chunk: &'a ChunkSlice,
        summary: &ChunkSummary,
    ) -> (
        &'a ChunkSlice,
        ChunkSummary,
        ChunkSummary,
        &'a ChunkSlice,
        ChunkSummary,
    ) {
        let (mut first, mut first_summary, advance, rest, rest_summary) =
            RawLineMetric::first_unit(chunk, summary);

        debug_assert_eq!(*first.as_bytes().last().unwrap() as char, '\n');
        debug_assert_eq!(first_summary.line_breaks, 1);

        let bytes_line_break = ((first.len() > 1
            && first.as_bytes()[first.len() - 2] == b'\r')
            as usize)
            + 1;

        first = (&first[..first.len() - bytes_line_break]).into();
        first_summary.bytes -= bytes_line_break;
        first_summary.line_breaks = 0;

        (first, first_summary, advance, rest, rest_summary)
    }
}

impl DoubleEndedUnitMetric<RopeChunk> for LineMetric {
    #[inline]
    fn last_unit<'a>(
        chunk: &'a ChunkSlice,
        summary: &ChunkSummary,
    ) -> (
        &'a ChunkSlice,
        ChunkSummary,
        &'a ChunkSlice,
        ChunkSummary,
        ChunkSummary,
    ) {
        let (rest, rest_summary, mut last, mut last_summary, advance) =
            RawLineMetric::last_unit(chunk, summary);

        debug_assert_eq!(last_summary, advance);

        if last_summary.line_breaks == 0 {
            return (rest, rest_summary, last, last_summary, advance);
        }

        debug_assert_eq!(*last.as_bytes().last().unwrap() as char, '\n');
        debug_assert_eq!(last_summary.line_breaks, 1);

        let bytes_line_break = ((last.len() > 1
            && last.as_bytes()[last.len() - 2] == b'\r')
            as usize)
            + 1;

        last = (&last[..last.len() - bytes_line_break]).into();
        last_summary.bytes -= bytes_line_break;
        last_summary.line_breaks = 0;

        (rest, rest_summary, last, last_summary, advance)
    }

    #[inline]
    fn remainder<'a>(
        chunk: &'a ChunkSlice,
        summary: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary, &'a ChunkSlice, ChunkSummary) {
        RawLineMetric::remainder(chunk, summary)
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use super::*;

    #[test]
    fn split_lines_left_1() {
        let chunk = "this is\na chunk\n".into();

        let (left, left_summary, right, right_summary) =
            RawLineMetric::split(chunk, RawLineMetric(1), &chunk.summarize());

        assert_eq!("this is\n", left.deref());
        assert_eq!(1, left_summary.line_breaks);

        assert_eq!("a chunk\n", right.deref());
        assert_eq!(1, right_summary.line_breaks);

        let (left, left_summary, right, _) =
            RawLineMetric::split(chunk, RawLineMetric(2), &chunk.summarize());

        assert_eq!("this is\na chunk\n", left.deref());
        assert_eq!(2, left_summary.line_breaks);
        assert_eq!("", right.deref());
    }

    #[test]
    fn split_lines_right_1() {
        let chunk = "\nthis is\na chunk".into();

        let (left, _, right, right_summary) =
            RawLineMetric::split(chunk, RawLineMetric(1), &chunk.summarize());

        assert_eq!("\n", left.deref());
        assert_eq!("this is\na chunk", right.deref());
        assert_eq!(1, right_summary.line_breaks);

        let (left, left_summary, right, right_summary) =
            RawLineMetric::split(chunk, RawLineMetric(2), &chunk.summarize());

        assert_eq!("\nthis is\n", left.deref());
        assert_eq!(2, left_summary.line_breaks);

        assert_eq!("a chunk", right.deref());
        assert_eq!(0, right_summary.line_breaks);
    }

    #[test]
    fn split_crlf_left() {
        let chunk = "\r\n".into();

        let (left, left_summary, right, _) =
            RawLineMetric::split(chunk, RawLineMetric(1), &chunk.summarize());

        assert_eq!("\r\n", left.deref());
        assert_eq!(1, left_summary.line_breaks);
        assert_eq!("", right.deref());
    }
}
