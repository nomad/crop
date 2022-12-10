use std::ops::{Add, AddAssign, Range, Sub, SubAssign};

use super::utils::*;
use super::{ChunkSlice, ChunkSummary, RopeChunk};
use crate::tree::{Metric, Summarize};

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

    #[inline]
    fn split<'a>(
        chunk: &'a ChunkSlice,
        ByteMetric(up_to): Self,
        summary: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary, &'a ChunkSlice, ChunkSummary) {
        let left = chunk[..up_to].into();
        let right = chunk[up_to..].into();
        (left, left.summarize(), right, right.summarize())
    }

    #[inline]
    fn slice<'a>(
        chunk: &'a ChunkSlice,
        range: Range<Self>,
        _summary: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary) {
        let slice = chunk[range.start.0..range.end.0].into();
        (slice, slice.summarize())
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

    #[inline]
    fn split<'a>(
        chunk: &'a ChunkSlice,
        LineMetric(at): Self,
        summary: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary, &'a ChunkSlice, ChunkSummary) {
        split_slice_at_line_break(chunk, at, summary)
    }

    #[inline]
    fn slice<'a>(
        chunk: &'a ChunkSlice,
        Range { start: LineMetric(start), end: LineMetric(end) }: Range<Self>,
        _summary: &ChunkSummary,
    ) -> (&'a ChunkSlice, ChunkSummary) {
        let slice = slice_between_line_breaks(chunk, start, end);
        (
            slice,
            ChunkSummary { bytes: slice.len(), line_breaks: start - end - 1 },
        )
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
            LineMetric::split(chunk, LineMetric(1), &chunk.summarize());

        assert_eq!("this is", left.deref());
        assert_eq!(0, left_summary.line_breaks);

        assert_eq!("a chunk\n", right.deref());
        assert_eq!(1, right_summary.line_breaks);

        let (left, left_summary, right, right_summary) =
            LineMetric::split(chunk, LineMetric(2), &chunk.summarize());

        assert_eq!("this is\na chunk", left.deref());
        assert_eq!(1, left_summary.line_breaks);
        // assert_eq!(None, maybe_right);
    }

    #[test]
    fn split_lines_right_1() {
        let chunk = "\nthis is\na chunk".into();

        let (left, left_summary, right, right_summary) =
            LineMetric::split(chunk, LineMetric(1), &chunk.summarize());

        assert_eq!("this is\na chunk", right.deref());
        assert_eq!(1, right_summary.line_breaks);
        // assert_eq!(None, maybe_left);

        let (left, left_summary, right, right_summary) =
            LineMetric::split(chunk, LineMetric(2), &chunk.summarize());

        assert_eq!("\nthis is", left.deref());
        assert_eq!(1, left_summary.line_breaks);

        assert_eq!("a chunk", right.deref());
        assert_eq!(0, right_summary.line_breaks);
    }

    #[test]
    fn split_crlf_left() {
        let chunk = "\r\n".into();

        let (left, summary, _, _) =
            LineMetric::split(chunk, LineMetric(1), &chunk.summarize());

        assert_eq!("", left.deref());
        assert_eq!(ChunkSummary::default(), summary);
        // assert_eq!(None, right);
    }
}
