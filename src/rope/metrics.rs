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
        todo!();
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
        RawLineMetric(at): Self,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        todo!();
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
        todo!();
    }
}

impl<const MAX_BYTES: usize> DoubleEndedUnitMetric<GapBuffer<MAX_BYTES>>
    for RawLineMetric
{
    #[inline]
    fn last_unit<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary, ChunkSummary)
    where
        'a: 'a,
    {
        todo!();
    }

    #[inline]
    fn remainder<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        todo!();
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
        todo!();
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
        todo!();
    }

    #[inline]
    fn remainder<'a>(
        chunk: GapSlice<'a>,
        summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary, GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        todo!();
    }
}
