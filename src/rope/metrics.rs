use std::ops::{Add, AddAssign, Range, Sub, SubAssign};

use super::utils::*;
use super::{TextChunk, TextSlice, TextSummary};
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

impl Metric<TextChunk> for ByteMetric {
    #[inline]
    fn zero() -> Self {
        Self(0)
    }

    #[inline]
    fn one() -> Self {
        Self(1)
    }

    #[inline]
    fn measure(summary: &TextSummary) -> Self {
        Self(summary.bytes)
    }

    #[inline]
    fn split_left<'a>(
        chunk: &'a TextSlice,
        ByteMetric(up_to): Self,
        summary: &TextSummary,
    ) -> (&'a TextSlice, TextSummary, Option<(&'a TextSlice, TextSummary)>)
    {
        if up_to == chunk.len() {
            (chunk, *summary, None)
        } else {
            let left = chunk[..up_to].into();
            let right = chunk[up_to..].into();
            (left, left.summarize(), Some((right, right.summarize())))
        }
    }

    #[inline]
    fn split_right<'a>(
        chunk: &'a TextSlice,
        ByteMetric(from): Self,
        summary: &TextSummary,
    ) -> (Option<(&'a TextSlice, TextSummary)>, &'a TextSlice, TextSummary)
    {
        if from == 0 {
            (None, chunk, *summary)
        } else {
            let left = chunk[..from].into();
            let right = chunk[from..].into();
            (Some((left, left.summarize())), right, right.summarize())
        }
    }

    #[inline]
    fn slice<'a>(
        chunk: &'a TextSlice,
        range: Range<Self>,
        _summary: &TextSummary,
    ) -> (&'a TextSlice, TextSummary) {
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

impl Metric<TextChunk> for LineMetric {
    #[inline]
    fn zero() -> Self {
        Self(0)
    }

    #[inline]
    fn one() -> Self {
        Self(1)
    }

    #[inline]
    fn measure(summary: &TextSummary) -> Self {
        Self(summary.line_breaks)
    }

    #[inline]
    fn split_left<'a>(
        chunk: &'a TextSlice,
        LineMetric(up_to): Self,
        summary: &TextSummary,
    ) -> (&'a TextSlice, TextSummary, Option<(&'a TextSlice, TextSummary)>)
    {
        let (left, right) = split_slice_at_line_break(chunk, up_to, summary);

        let (left, left_summary) =
            left.unwrap_or(("".into(), TextSummary::default()));

        (left, left_summary, right)
    }

    #[inline]
    fn split_right<'a>(
        chunk: &'a TextSlice,
        LineMetric(from): Self,
        summary: &TextSummary,
    ) -> (Option<(&'a TextSlice, TextSummary)>, &'a TextSlice, TextSummary)
    {
        let (left, right) = split_slice_at_line_break(chunk, from, summary);

        let (right, right_summary) =
            right.unwrap_or(("".into(), TextSummary::default()));

        (left, right, right_summary)
    }

    #[inline]
    fn slice<'a>(
        chunk: &'a TextSlice,
        Range { start: LineMetric(start), end: LineMetric(end) }: Range<Self>,
        _summary: &TextSummary,
    ) -> (&'a TextSlice, TextSummary) {
        let slice = slice_between_line_breaks(chunk, start, end);
        (
            slice,
            TextSummary { bytes: slice.len(), line_breaks: start - end - 1 },
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

        let (left, left_summary, maybe_right) =
            LineMetric::split_left(chunk, LineMetric(1), &chunk.summarize());

        assert_eq!("this is", left.deref());
        assert_eq!(0, left_summary.line_breaks);

        let (right, right_summary) = maybe_right.unwrap();
        assert_eq!("a chunk\n", right.deref());
        assert_eq!(1, right_summary.line_breaks);

        let (left, left_summary, maybe_right) =
            LineMetric::split_left(chunk, LineMetric(2), &chunk.summarize());

        assert_eq!("this is\na chunk", left.deref());
        assert_eq!(1, left_summary.line_breaks);
        assert_eq!(None, maybe_right);
    }

    #[test]
    fn split_lines_right_1() {
        let chunk = "\nthis is\na chunk".into();

        let (maybe_left, right, right_summary) =
            LineMetric::split_right(chunk, LineMetric(1), &chunk.summarize());

        assert_eq!("this is\na chunk", right.deref());
        assert_eq!(1, right_summary.line_breaks);
        assert_eq!(None, maybe_left);

        let (maybe_left, right, right_summary) =
            LineMetric::split_right(chunk, LineMetric(2), &chunk.summarize());

        let (left, left_summary) = maybe_left.unwrap();
        assert_eq!("\nthis is", left.deref());
        assert_eq!(1, left_summary.line_breaks);

        assert_eq!("a chunk", right.deref());
        assert_eq!(0, right_summary.line_breaks);
    }

    #[test]
    fn split_crlf_left() {
        let chunk = "\r\n".into();

        let (left, summary, right) =
            LineMetric::split_left(chunk, LineMetric(1), &chunk.summarize());

        assert_eq!("", left.deref());
        assert_eq!(TextSummary::default(), summary);
        assert_eq!(None, right);
    }
}
