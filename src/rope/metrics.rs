use std::ops::{Add, AddAssign, Range, Sub, SubAssign};

use super::{TextChunk, TextSummary};
use crate::tree::Metric;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ByteMetric(pub(super) usize);

impl Add for ByteMetric {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl Sub for ByteMetric {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl AddAssign for ByteMetric {
    fn add_assign(&mut self, other: Self) {
        self.0 += other.0
    }
}

impl SubAssign for ByteMetric {
    fn sub_assign(&mut self, other: Self) {
        self.0 -= other.0
    }
}

impl Metric<TextChunk> for ByteMetric {
    fn zero() -> Self {
        Self(0)
    }

    fn measure(summary: &TextSummary) -> Self {
        Self(summary.bytes)
    }

    fn slice(chunk: &TextChunk, range: Range<Self>) -> &TextChunk {
        todo!()
        // Some(&chunk.text[range.start.0..range.end.0])
    }
}
