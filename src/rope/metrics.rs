use core::ops::{Add, AddAssign, Sub, SubAssign};

use super::gap_buffer::GapBuffer;
use super::gap_slice::GapSlice;
use crate::tree::{
    DoubleEndedUnitMetric,
    LeafSlice,
    Metric,
    SlicingMetric,
    Summary,
    UnitMetric,
};

#[derive(Copy, Clone, Default, Debug, PartialEq)]
#[doc(hidden)]
pub struct ChunkSummary {
    bytes: usize,
    line_breaks: usize,
    #[cfg(feature = "utf16-metric")]
    utf16_code_units: usize,
}

impl From<&str> for ChunkSummary {
    #[inline]
    fn from(s: &str) -> Self {
        Self {
            bytes: s.len(),
            line_breaks: count::line_breaks(s),
            #[cfg(feature = "utf16-metric")]
            utf16_code_units: count::utf16_code_units(s),
        }
    }
}

impl From<char> for ChunkSummary {
    #[inline]
    fn from(ch: char) -> Self {
        Self {
            bytes: ch.len_utf8(),
            line_breaks: (ch == '\n') as usize,
            #[cfg(feature = "utf16-metric")]
            utf16_code_units: ch.len_utf16(),
        }
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

    #[cfg(feature = "utf16-metric")]
    #[inline]
    pub fn utf16_code_units(&self) -> usize {
        self.utf16_code_units
    }
}

impl Summary for ChunkSummary {
    type Leaf = GapBuffer;

    #[inline]
    fn empty() -> Self {
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

impl AddAssign<Self> for ChunkSummary {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.bytes += rhs.bytes;
        self.line_breaks += rhs.line_breaks;
        #[cfg(feature = "utf16-metric")]
        {
            self.utf16_code_units += rhs.utf16_code_units;
        }
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

impl SubAssign<Self> for ChunkSummary {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.bytes -= rhs.bytes;
        self.line_breaks -= rhs.line_breaks;
        #[cfg(feature = "utf16-metric")]
        {
            self.utf16_code_units -= rhs.utf16_code_units;
        }
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

            line_breaks: count::line_breaks_up_to(
                in_str,
                byte_offset,
                str_summary.line_breaks,
            ),

            #[cfg(feature = "utf16-metric")]
            utf16_code_units: count::utf16_code_units_up_to(
                in_str,
                byte_offset,
                str_summary.utf16_code_units,
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

    #[inline]
    fn measure_leaf(gap_buffer: &GapBuffer) -> Self {
        Self(gap_buffer.len())
    }

    #[inline]
    fn measure_slice(gap_slice: &GapSlice) -> Self {
        Self(gap_slice.len())
    }
}

impl SlicingMetric<GapBuffer> for ByteMetric {
    #[track_caller]
    #[inline]
    fn slice_up_to<'a>(chunk: GapSlice<'a>, byte_offset: Self) -> GapSlice<'a>
    where
        'a: 'a,
    {
        chunk.assert_char_boundary(byte_offset.0);
        chunk.split_at_offset(byte_offset).0
    }

    #[track_caller]
    #[inline]
    fn slice_from<'a>(chunk: GapSlice<'a>, byte_offset: Self) -> GapSlice<'a>
    where
        'a: 'a,
    {
        chunk.assert_char_boundary(byte_offset.0);
        chunk.split_at_offset(byte_offset).1
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
        convert::byte_of_line(s, self.0)
    }
}

impl SummaryUpTo for RawLineMetric {
    #[cfg_attr(not(feature = "utf16-metric"), allow(unused_variables))]
    #[inline]
    fn up_to(
        in_str: &str,
        str_summary: ChunkSummary,
        Self(line_offset): Self,
        byte_offset: usize,
    ) -> ChunkSummary {
        ChunkSummary {
            bytes: byte_offset,

            line_breaks: line_offset,

            #[cfg(feature = "utf16-metric")]
            utf16_code_units: count::utf16_code_units_up_to(
                in_str,
                byte_offset,
                str_summary.utf16_code_units,
            ),
        }
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

    #[inline]
    fn measure_leaf(gap_buffer: &GapBuffer) -> Self {
        Self(
            gap_buffer.left_summary.line_breaks
                + gap_buffer.right_summary.line_breaks,
        )
    }

    #[inline]
    fn measure_slice(gap_slice: &GapSlice) -> Self {
        Self(
            gap_slice.left_summary.line_breaks
                + gap_slice.right_summary.line_breaks,
        )
    }
}

impl SlicingMetric<GapBuffer> for RawLineMetric {
    #[inline]
    fn slice_up_to<'a>(chunk: GapSlice<'a>, line_offset: Self) -> GapSlice<'a>
    where
        'a: 'a,
    {
        chunk.split_at_offset(line_offset).0
    }

    #[inline]
    fn slice_from<'a>(chunk: GapSlice<'a>, line_offset: Self) -> GapSlice<'a>
    where
        'a: 'a,
    {
        chunk.split_at_offset(line_offset).1
    }
}

impl UnitMetric<GapBuffer> for RawLineMetric {
    #[inline]
    fn first_unit<'a>(
        chunk: GapSlice<'a>,
    ) -> (GapSlice<'a>, GapSlice<'a>, ByteMetric)
    where
        'a: 'a,
    {
        let (first, rest) = chunk.split_at_offset(RawLineMetric(1));
        (first, rest, first.measure())
    }
}

impl DoubleEndedUnitMetric<GapBuffer> for RawLineMetric {
    #[inline]
    fn last_unit<'a>(
        slice: GapSlice<'a>,
    ) -> (GapSlice<'a>, GapSlice<'a>, ByteMetric)
    where
        'a: 'a,
    {
        let split_offset = slice.summarize().line_breaks
            - (slice.has_trailing_newline() as usize);

        let (rest, last) = slice.split_at_offset(RawLineMetric(split_offset));

        (rest, last, last.measure())
    }

    #[inline]
    fn remainder<'a>(chunk: GapSlice<'a>) -> (GapSlice<'a>, GapSlice<'a>)
    where
        'a: 'a,
    {
        if chunk.has_trailing_newline() {
            (chunk, GapSlice::empty())
        } else {
            let (rest, last, _) =
                <Self as DoubleEndedUnitMetric<GapBuffer>>::last_unit(chunk);

            (rest, last)
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

    #[inline]
    fn measure_leaf(gap_buffer: &GapBuffer) -> Self {
        Self(RawLineMetric::measure_leaf(gap_buffer).0)
    }

    #[inline]
    fn measure_slice(gap_slice: &GapSlice) -> Self {
        Self(RawLineMetric::measure_slice(gap_slice).0)
    }
}

impl UnitMetric<GapBuffer> for LineMetric {
    #[inline]
    fn first_unit<'a>(
        chunk: GapSlice<'a>,
    ) -> (GapSlice<'a>, GapSlice<'a>, ByteMetric)
    where
        'a: 'a,
    {
        let (mut first, rest, first_byte_len) =
            <RawLineMetric as UnitMetric<GapBuffer>>::first_unit(chunk);

        first.truncate_trailing_line_break();

        (first, rest, first_byte_len)
    }
}

impl DoubleEndedUnitMetric<GapBuffer> for LineMetric {
    #[inline]
    fn last_unit<'a>(
        chunk: GapSlice<'a>,
    ) -> (GapSlice<'a>, GapSlice<'a>, ByteMetric)
    where
        'a: 'a,
    {
        let (rest, mut last, last_byte_len) =
            <RawLineMetric as DoubleEndedUnitMetric<GapBuffer>>::last_unit(
                chunk,
            );

        last.truncate_trailing_line_break();

        (rest, last, last_byte_len)
    }

    #[inline]
    fn remainder<'a>(chunk: GapSlice<'a>) -> (GapSlice<'a>, GapSlice<'a>)
    where
        'a: 'a,
    {
        <RawLineMetric as DoubleEndedUnitMetric<GapBuffer>>::remainder(chunk)
    }
}

#[cfg(feature = "utf16-metric")]
pub use utf16_metric::Utf16Metric;

#[cfg(feature = "utf16-metric")]
mod utf16_metric {
    use super::*;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Utf16Metric(pub usize);

    impl Add<Self> for Utf16Metric {
        type Output = Self;

        #[inline]
        fn add(self, other: Self) -> Self {
            Self(self.0 + other.0)
        }
    }

    impl Sub for Utf16Metric {
        type Output = Self;

        #[inline]
        fn sub(self, other: Self) -> Self {
            Self(self.0 - other.0)
        }
    }

    impl AddAssign for Utf16Metric {
        #[inline]
        fn add_assign(&mut self, other: Self) {
            self.0 += other.0
        }
    }

    impl SubAssign for Utf16Metric {
        #[inline]
        fn sub_assign(&mut self, other: Self) {
            self.0 -= other.0
        }
    }

    impl ToByteOffset for Utf16Metric {
        #[track_caller]
        #[inline]
        fn to_byte_offset(&self, in_str: &str) -> usize {
            // TODO: we should panic the given UTF-16 offset doesn't lie on a
            // char boundary. Right now we just return the byte offset up to
            // the previous char boundary.
            convert::byte_of_utf16_code_unit(in_str, self.0)
        }
    }

    impl SummaryUpTo for Utf16Metric {
        #[inline]
        fn up_to(
            in_str: &str,
            str_summary: ChunkSummary,
            Self(utf16_code_unit_offset): Self,
            byte_offset: usize,
        ) -> ChunkSummary {
            ChunkSummary {
                bytes: byte_offset,

                line_breaks: count::line_breaks_up_to(
                    in_str,
                    byte_offset,
                    str_summary.line_breaks,
                ),

                utf16_code_units: utf16_code_unit_offset,
            }
        }
    }

    impl Metric<ChunkSummary> for Utf16Metric {
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
            Self(summary.utf16_code_units)
        }

        #[inline]
        fn measure_leaf(gap_buffer: &GapBuffer) -> Self {
            Self(
                gap_buffer.left_summary.utf16_code_units
                    + gap_buffer.right_summary.utf16_code_units,
            )
        }

        #[inline]
        fn measure_slice(gap_slice: &GapSlice) -> Self {
            Self(
                gap_slice.left_summary.utf16_code_units
                    + gap_slice.right_summary.utf16_code_units,
            )
        }
    }

    impl SlicingMetric<GapBuffer> for Utf16Metric {
        #[track_caller]
        #[inline]
        fn slice_up_to<'a>(
            chunk: GapSlice<'a>,
            utf16_code_unit_offset: Self,
        ) -> GapSlice<'a>
        where
            'a: 'a,
        {
            chunk.split_at_offset(utf16_code_unit_offset).0
        }

        #[track_caller]
        #[inline]
        fn slice_from<'a>(
            chunk: GapSlice<'a>,
            utf16_code_unit_offset: Self,
        ) -> GapSlice<'a>
        where
            'a: 'a,
        {
            chunk.split_at_offset(utf16_code_unit_offset).1
        }
    }
}

use str_utils::*;

mod str_utils {
    #[cfg(not(miri))]
    use str_indices::lines_lf as lines;
    #[cfg(all(not(miri), feature = "utf16-metric"))]
    use str_indices::utf16;

    pub mod count {
        #[cfg(not(miri))]
        use super::*;

        #[inline]
        pub fn line_breaks(s: &str) -> usize {
            #[cfg(not(miri))]
            {
                lines::count_breaks(s)
            }
            #[cfg(miri)]
            {
                s.bytes().filter(|&b| b == b'\n').count()
            }
        }

        #[cfg(feature = "utf16-metric")]
        #[inline]
        pub fn utf16_code_units(s: &str) -> usize {
            #[cfg(not(miri))]
            {
                utf16::count(s)
            }
            #[cfg(miri)]
            {
                s.encode_utf16().count()
            }
        }

        #[inline(always)]
        pub fn line_breaks_up_to(
            s: &str,
            byte_offset: usize,
            tot_line_breaks: usize,
        ) -> usize {
            metric_up_to(s, byte_offset, tot_line_breaks, line_breaks)
        }

        #[cfg(feature = "utf16-metric")]
        #[inline(always)]
        pub fn utf16_code_units_up_to(
            s: &str,
            byte_offset: usize,
            tot_utf16_code_units: usize,
        ) -> usize {
            metric_up_to(
                s,
                byte_offset,
                tot_utf16_code_units,
                utf16_code_units,
            )
        }

        #[inline(always)]
        fn metric_up_to(
            s: &str,
            byte_offset: usize,
            tot: usize,
            count: fn(&str) -> usize,
        ) -> usize {
            debug_assert!(s.is_char_boundary(byte_offset));

            debug_assert_eq!(tot, count(s));

            // Count the shorter side and get the other by subtracting it from
            // the total if necessary.
            if byte_offset <= s.len() / 2 {
                count(&s[..byte_offset])
            } else {
                tot - count(&s[byte_offset..])
            }
        }
    }

    pub mod convert {
        #[cfg(not(miri))]
        use super::*;

        #[inline]
        pub fn byte_of_line(s: &str, line_offset: usize) -> usize {
            #[cfg(not(miri))]
            {
                lines::to_byte_idx(s, line_offset)
            }

            #[cfg(miri)]
            {
                if line_offset == 0 {
                    return 0;
                }

                let mut seen = 0;
                let mut stop = false;

                s.bytes()
                    .take_while(|&b| {
                        !stop && {
                            if b == b'\n' {
                                seen += 1;
                                if seen == line_offset {
                                    stop = true;
                                }
                            }
                            true
                        }
                    })
                    .count()
            }
        }

        #[cfg(feature = "utf16-metric")]
        #[inline]
        pub fn byte_of_utf16_code_unit(
            s: &str,
            utf16_code_unit_offset: usize,
        ) -> usize {
            #[cfg(not(miri))]
            {
                utf16::to_byte_idx(s, utf16_code_unit_offset)
            }

            #[cfg(miri)]
            {
                let encoded_utf16 = s.encode_utf16().collect::<Vec<_>>();

                let decoded_utf16 = String::from_utf16(
                    &encoded_utf16[..utf16_code_unit_offset],
                )
                .unwrap();

                decoded_utf16.len()
            }
        }
    }
}
