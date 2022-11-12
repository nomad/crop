use std::ops::{Add, AddAssign, Range, Sub, SubAssign};

use super::{TextChunk, TextSlice, TextSummary};
use crate::tree::Metric;

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
    fn measure(summary: &TextSummary) -> Self {
        Self(summary.bytes)
    }

    #[inline]
    fn slice(chunk: &TextSlice, range: Range<Self>) -> &TextSlice {
        chunk[range.start.0..range.end.0].into()
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
    fn measure(summary: &TextSummary) -> Self {
        todo!()
    }

    #[inline]
    fn slice(chunk: &TextSlice, range: Range<Self>) -> &TextSlice {
        todo!()
    }
}
