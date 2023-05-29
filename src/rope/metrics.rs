use core::ops::{Add, AddAssign, Sub, SubAssign};

use super::gap_buffer::GapBuffer;
use super::gap_slice::GapSlice;
use super::utils;
use crate::tree::{DoubleEndedUnitMetric, Metric, SlicingMetric, UnitMetric};

#[derive(Copy, Clone, Default, Debug, PartialEq)]
#[doc(hidden)]
pub struct ChunkSummary {
    bytes: usize,
    line_breaks: usize,
}

impl From<&str> for ChunkSummary {
    #[inline]
    fn from(s: &str) -> Self {
        Self { bytes: s.len(), line_breaks: utils::count_line_breaks(s) }
    }
}

impl From<char> for ChunkSummary {
    #[inline]
    fn from(ch: char) -> Self {
        Self { bytes: ch.len_utf8(), line_breaks: (ch == '\n') as usize }
    }
}

impl ChunkSummary {
    #[inline]
    pub fn bytes(&self) -> usize {
        self.bytes
    }

    #[inline]
    pub fn line_breaks(&self) -> usize {
        self.line_breaks
    }

    #[doc(hidden)]
    #[inline]
    pub fn new() -> Self {
        Self::default()
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

/// Conversion trait from the metric implement this trait to the corresponding
/// byte offset.
pub trait ToByteOffset: Metric<ChunkSummary> {
    /// Should return the byte offset of `self` in the given string.
    fn to_byte_offset(&self, in_str: &str) -> usize;
}

/// Trait to get the summary of a string up to a given offset.
pub trait SummaryUpTo: Metric<ChunkSummary> {
    /// Return the summary of the given string up to `offset`, where
    ///
    /// * `str_summary` is the string's summary,
    /// * `byte_offset` is byte offset of `offset`.
    fn up_to(
        in_str: &str,
        str_summary: ChunkSummary,
        offset: Self,
        byte_offset: usize,
    ) -> ChunkSummary;
}

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

impl ToByteOffset for ByteMetric {
    #[inline]
    fn to_byte_offset(&self, _: &str) -> usize {
        self.0
    }
}

impl SummaryUpTo for ByteMetric {
    #[inline]
    fn up_to(
        in_str: &str,
        str_summary: ChunkSummary,
        offset: Self,
        byte_offset: usize,
    ) -> ChunkSummary {
        debug_assert_eq!(offset.0, byte_offset);

        ChunkSummary {
            bytes: byte_offset,

            line_breaks: utils::line_breaks_up_to(
                in_str,
                byte_offset,
                str_summary.line_breaks,
            ),
        }
    }
}

impl Metric<ChunkSummary> for ByteMetric {
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
        byte_offset: Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        chunk.assert_char_boundary(byte_offset.0);

        let (left, _) = chunk.split_at_offset(byte_offset, summary);
        left
    }

    #[track_caller]
    #[inline]
    fn slice_from<'a>(
        chunk: GapSlice<'a>,
        byte_offset: Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        chunk.assert_char_boundary(byte_offset.0);

        let (_, right) = chunk.split_at_offset(byte_offset, summary);
        right
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RawLineMetric(pub usize);

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

impl ToByteOffset for RawLineMetric {
    #[inline]
    fn to_byte_offset(&self, s: &str) -> usize {
        utils::byte_of_line(s, self.0)
    }
}

impl SummaryUpTo for RawLineMetric {
    #[inline]
    fn up_to(
        _: &str,
        _: ChunkSummary,
        Self(line_offset): Self,
        byte_offset: usize,
    ) -> ChunkSummary {
        ChunkSummary { bytes: byte_offset, line_breaks: line_offset }
    }
}

impl Metric<ChunkSummary> for RawLineMetric {
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
        line_offset: Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (left, _) = chunk.split_at_offset(line_offset, summary);
        left
    }

    #[inline]
    fn slice_from<'a>(
        chunk: GapSlice<'a>,
        line_offset: Self,
        &summary: &ChunkSummary,
    ) -> (GapSlice<'a>, ChunkSummary)
    where
        'a: 'a,
    {
        let (_, right) = chunk.split_at_offset(line_offset, summary);
        right
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
        let ((first, first_summary), (rest, rest_summary)) =
            chunk.split_at_offset(RawLineMetric(1), summary);

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
        let split_offset =
            summary.line_breaks - (slice.has_trailing_newline() as usize);

        let ((rest, rest_summary), (last, last_summary)) =
            slice.split_at_offset(RawLineMetric(split_offset), summary);

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
            (chunk, *summary, GapSlice::empty(), ChunkSummary::new())
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

impl Metric<ChunkSummary> for LineMetric {
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

        first_summary = first.truncate_trailing_line_break(first_summary);

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

        last_summary = last.truncate_trailing_line_break(last_summary);

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
