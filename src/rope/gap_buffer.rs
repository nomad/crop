use std::ops::{Add, AddAssign, Range, RangeBounds, Sub, SubAssign};

use super::gap_slice::GapSlice;
use super::metrics::ByteMetric;
use super::utils::*;
use crate::range_bounds_to_start_end;
use crate::tree::{
    AsSlice,
    BalancedLeaf,
    BaseMeasured,
    ReplaceableLeaf,
    Summarize,
};

/// A gap buffer with a max capacity of `2^16 - 1` bytes.
///
/// A gap buffer with two gaps, one in the middle and one at the end.
///
/// The second gap being at the end means that we still have 2 segments, not 3.
///
/// "Off this wave" -> "Off [   ]this wave[  ]"
#[derive(Clone)]
pub(super) struct GapBuffer<const MAX_BYTES: usize> {
    bytes: Box<[u8; MAX_BYTES]>,
    len_first_segment: u16,
    len_second_segment: u16,
}

impl<const MAX_BYTES: usize> std::fmt::Debug for GapBuffer<MAX_BYTES> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.as_slice(), f)
    }
}

impl<const MAX_BYTES: usize> Default for GapBuffer<MAX_BYTES> {
    #[inline]
    fn default() -> Self {
        Self {
            bytes: Box::new([0u8; MAX_BYTES]),
            len_first_segment: 0,
            len_second_segment: 0,
        }
    }
}

impl<const MAX_BYTES: usize> From<&str> for GapBuffer<MAX_BYTES> {
    /// # Panics
    ///
    /// Panics if the string is empty or if its byte length is greater than
    /// `MAX_BYTES`.
    #[inline]
    fn from(s: &str) -> Self {
        debug_assert!(!s.is_empty());
        debug_assert!(s.len() <= MAX_BYTES);
        Self::from_segments(&[s])
    }
}

impl<const MAX_BYTES: usize> GapBuffer<MAX_BYTES> {
    #[inline]
    fn append(&mut self, s: &str) {
        debug_assert!(s.len() <= self.len_gap());

        let start = MAX_BYTES - self.len_second_segment();

        // Shift the second segment to the left.
        self.bytes.copy_within(start.., start - s.len());

        // Append the string.
        self.bytes[MAX_BYTES - s.len()..].copy_from_slice(s.as_bytes());

        self.len_second_segment += s.len() as u16;
    }

    #[inline]
    fn append_two(&mut self, a: &str, b: &str) {
        debug_assert!(a.len() + b.len() <= self.len_gap());

        // Shift the second segment to the left.
        let start = MAX_BYTES - self.len_second_segment();
        self.bytes.copy_within(start.., start - a.len() - b.len());

        // Append the first string.
        let range = {
            let end = MAX_BYTES - b.len();
            end - a.len()..end
        };
        self.bytes[range].copy_from_slice(a.as_bytes());

        // Append the second string.
        let range = MAX_BYTES - b.len()..MAX_BYTES;
        self.bytes[range].copy_from_slice(b.as_bytes());

        self.len_second_segment += (a.len() + b.len()) as u16;
    }

    #[inline]
    fn prepend(&mut self, s: &str) {
        debug_assert!(s.len() <= self.len_gap());

        // Shift the first segment to the right.
        let len_first = self.len_first_segment();
        self.bytes.copy_within(..len_first, s.len());

        // Prepend the string.
        self.bytes[..s.len()].copy_from_slice(s.as_bytes());

        self.len_first_segment += s.len() as u16;
    }

    #[inline]
    fn prepend_two(&mut self, a: &str, b: &str) {
        debug_assert!(a.len() + b.len() <= self.len_gap());

        // Shift the first segment to the right.
        let len_first = self.len_first_segment();
        self.bytes.copy_within(..len_first, a.len() + b.len());

        // Prepend the first string.
        self.bytes[..a.len()].copy_from_slice(a.as_bytes());

        // Prepend the second string.
        self.bytes[a.len()..a.len() + b.len()].copy_from_slice(b.as_bytes());

        self.len_first_segment += (a.len() + b.len()) as u16;
    }

    #[inline]
    fn remove_up_to(&mut self, byte_offset: usize) {
        debug_assert!(self.is_char_boundary(byte_offset));

        if byte_offset <= self.len_first_segment() {
            let len_moved = self.len_first_segment() - byte_offset;
            let moved_range = {
                let end = self.len_first_segment();
                end - len_moved..end
            };
            self.bytes.copy_within(moved_range, 0);
            self.len_first_segment = len_moved as u16;
        } else {
            self.len_first_segment = 0;
            self.len_second_segment -=
                (byte_offset - self.len_first_segment()) as u16;
        }
    }

    #[inline]
    fn remove_from(&mut self, byte_offset: usize) {
        debug_assert!(self.is_char_boundary(byte_offset));

        if byte_offset <= self.len_first_segment() {
            self.len_first_segment = byte_offset as u16;
            self.len_second_segment = 0;
        } else {
            let byte_offset = byte_offset - self.len_first_segment();
            let start = MAX_BYTES - self.len_second_segment();
            let end = start + byte_offset;
            self.bytes.copy_within(start..end, MAX_BYTES - byte_offset);
            self.len_second_segment = byte_offset as u16;
        }
    }

    /// The number of bytes `RopeChunk`s must always stay over.
    pub(super) const fn chunk_min() -> usize {
        if Self::min_bytes() > 3 {
            // The wiggle room is 3 bytes for the reason already explained in
            // the comment above.
            Self::min_bytes() - 3
        } else {
            1
        }
    }

    #[inline]
    pub(super) fn chunk_segmenter(s: &str) -> ChunkSegmenter<'_, MAX_BYTES> {
        ChunkSegmenter { s, yielded: 0 }
    }

    #[inline]
    fn first_segment(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the bytes in
        // the first segment as valid UTF-8.
        unsafe {
            std::str::from_utf8_unchecked(
                &self.bytes[..self.len_first_segment()],
            )
        }
    }

    /// TODO: docs
    ///
    /// # Panics
    ///
    /// Panics if the combined byte length of all the segments is zero or if
    /// it's greater than `MAX_BYTES`.
    ///
    /// TODO: examples
    #[inline]
    fn from_segments(segments: &[&str]) -> Self {
        let total_len = segments.iter().map(|s| s.len() as u16).sum::<u16>();

        debug_assert!(total_len > 0);
        debug_assert!(total_len <= MAX_BYTES as u16);

        let add_to_first = total_len / 2;

        let mut bytes = Box::new([0u8; MAX_BYTES]);

        let mut len_first_segment = 0;

        let mut segments = segments.iter();

        for &segment in segments.by_ref() {
            if len_first_segment + segment.len() as u16 <= add_to_first {
                let range = {
                    let start = len_first_segment as usize;
                    let end = start + segment.len();
                    start..end
                };

                bytes[range].copy_from_slice(segment.as_bytes());

                len_first_segment += segment.len() as u16;
            } else {
                let (to_first, to_second) = split_adjusted::<true>(
                    segment,
                    (add_to_first - len_first_segment) as usize,
                );

                let range = {
                    let start = len_first_segment as usize;
                    let end = start + to_first.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_first.as_bytes());

                len_first_segment += to_first.len() as u16;

                let len_second_segment = total_len - len_first_segment;

                let mut start = MAX_BYTES as u16 - len_second_segment;

                let range = {
                    let start = start as usize;
                    let end = start + to_second.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_second.as_bytes());

                start += to_second.len() as u16;

                for &segment in segments {
                    let range = {
                        let start = start as usize;
                        let end = start + segment.len();
                        start..end
                    };

                    bytes[range].copy_from_slice(segment.as_bytes());

                    start += segment.len() as u16;
                }

                return Self { bytes, len_first_segment, len_second_segment };
            }
        }

        unreachable!("This can only be reached if the total length is zero");
    }

    /// Returns `true` if it ends with a newline (either LF or CRLF).
    #[inline]
    pub(super) fn has_trailing_newline(&self) -> bool {
        last_byte_is_newline(self.last_segment())
    }

    /// TODO: docs
    #[inline]
    fn move_gap_to_offset(&mut self, byte_offset: usize) {
        debug_assert!(self.is_char_boundary(byte_offset));

        let offset = byte_offset;

        #[allow(clippy::comparison_chain)]
        // The offset splits the first segment => move all the text after the
        // offset to the start of the second segment.
        //
        // aa|bb~~~ccc => aa~~~bbccc
        if offset < self.len_first_segment() {
            let move_range = offset..self.len_first_segment();
            let len_moved = self.len_first_segment() - offset;
            self.len_second_segment += len_moved as u16;
            let start = MAX_BYTES - self.len_second_segment();
            self.bytes.copy_within(move_range, start);
            self.len_first_segment -= len_moved as u16;
        }
        // The offset splits the second segment => move all the text before the
        // offset to the end of the first segment.
        //
        // aaa~~~bb|cc => aaabb~~cc
        else if offset > self.len_first_segment() {
            let len_moved = offset - self.len_first_segment();
            let move_range = {
                let start = MAX_BYTES - self.len_second_segment();
                let end = start + len_moved;
                start..end
            };
            let start = self.len_first_segment();
            self.bytes.copy_within(move_range, start);
            self.len_first_segment += len_moved as u16;
            self.len_second_segment -= len_moved as u16;
        }

        debug_assert_eq!(offset, self.len_first_segment());
    }

    /// Inserts the string at the given byte offset, moving the gap to the new
    /// insertion point if necessary.
    ///
    /// # Panics
    ///
    /// Panics if the byte offset is not a char boundary of if the byte length
    /// of the string is greater than the length of the gap.
    #[inline]
    pub(super) fn insert(&mut self, insert_at: usize, s: &str) {
        debug_assert!(insert_at <= self.len());
        debug_assert!(self.is_char_boundary(insert_at));
        debug_assert!(s.len() <= self.len_gap());

        self.move_gap_to_offset(insert_at);

        debug_assert_eq!(insert_at, self.len_first_segment());

        let insert_range = {
            let start = self.len_first_segment();
            let end = start + s.len();
            start..end
        };

        self.bytes[insert_range].copy_from_slice(s.as_bytes());
        self.len_first_segment += s.len() as u16;
    }

    #[inline]
    fn is_char_boundary(&self, byte_offset: usize) -> bool {
        debug_assert!(byte_offset <= self.len());

        if byte_offset <= self.len_first_segment() {
            self.first_segment().is_char_boundary(byte_offset)
        } else {
            self.second_segment()
                .is_char_boundary(byte_offset - self.len_first_segment())
        }
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The second segment if it's not empty, or the first one otherwise.
    #[inline]
    pub(super) fn last_segment(&self) -> &str {
        if !self.second_segment().is_empty() {
            self.second_segment()
        } else {
            self.first_segment()
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.len_first_segment() + self.len_second_segment()
    }

    #[inline]
    fn len_first_segment(&self) -> usize {
        self.len_first_segment as _
    }

    #[inline]
    fn len_gap(&self) -> usize {
        MAX_BYTES - self.len_first_segment() - self.len_second_segment()
    }

    #[inline]
    fn len_second_segment(&self) -> usize {
        self.len_second_segment as _
    }

    // #[inline]
    // fn len_trailing_gap(&self) -> usize {
    //     MAX_BYTES - self.len_middle_gap() - self.len()
    // }

    /// The number of bytes `RopeChunk`s should aim to stay over.
    pub(super) const fn min_bytes() -> usize {
        MAX_BYTES / 2
    }

    /// Pushes as mush of the slice as possible into this chunk, returning the
    /// rest (if any).
    pub(super) fn push_with_remainder<'a>(
        &mut self,
        s: &'a str,
    ) -> Option<&'a str> {
        debug_assert_eq!(self.len_second_segment(), 0);

        let space_left = MAX_BYTES - self.len_first_segment();
        let (push, rest) = split_adjusted::<false>(s, space_left);

        debug_assert!(push.len() <= space_left);

        let pushed_range = {
            let start = self.len_first_segment();
            let end = start + push.len();
            start..end
        };

        self.bytes[pushed_range].copy_from_slice(push.as_bytes());
        self.len_first_segment += push.len() as u16;

        (!rest.is_empty()).then_some(rest)
    }

    #[inline]
    fn replace(&mut self, byte_range: Range<usize>, s: &str) {
        let Range { start, end } = byte_range;

        let len_replaced = end - start;

        debug_assert!(start <= end);
        debug_assert!(end <= self.len());
        debug_assert!(self.is_char_boundary(start));
        debug_assert!(self.is_char_boundary(end));
        debug_assert!(s.len() <= len_replaced + self.len_gap());

        self.move_gap_to_offset(end);

        debug_assert_eq!(end, self.len_first_segment());

        if !s.is_empty() {
            #[allow(clippy::comparison_chain)]
            // We're adding more text than we're deleting.
            if len_replaced < s.len() {
                let adding = s.len() - len_replaced;

                let replace = &s.as_bytes()[..len_replaced];
                let add = &s.as_bytes()[len_replaced..];

                self.bytes[start..end].copy_from_slice(replace);

                self.bytes[end..end + adding].copy_from_slice(add);

                self.len_first_segment += adding as u16;
            }
            // We're deleting more text than we're adding.
            else if len_replaced > s.len() {
                self.bytes[start..start + s.len()]
                    .copy_from_slice(s.as_bytes());

                self.len_first_segment = (start + s.len()) as u16;
            } else {
                self.bytes[start..end].copy_from_slice(s.as_bytes());
            }
        } else {
            self.len_first_segment -= len_replaced as u16;
        }
    }

    /// Replaces the text in the byte range with the string, then removes all
    /// the text after the byte offset.
    ///
    /// # Panics
    ///
    /// Panics if either the start of the byte range, the end or
    /// `truncate_from` don't lie on a char boundary, if `truncate_from` is
    /// smaller than the end of the byte range or if the combination of all the
    /// parameters would cause self to go over `MAX_BYTES`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut buffer = GapBuffer::<10>::from("aaabbb"); // "aaa~~~~bbb"
    ///
    /// // Replace "ab" with "ccc", then truncate before the last `b`.
    /// buffer.replace_and_truncate(2..4, "ccc", 5); // "aac~~~~ccb"
    ///
    /// assert_eq!(buffer.first_segment(), "aac");
    /// assert_eq!(buffer.second_segment(), "ccb");
    /// ```
    #[inline]
    fn replace_and_truncate(
        &mut self,
        byte_range: Range<usize>,
        s: &str,
        truncate_from: usize,
    ) {
        let Range { start, end } = byte_range;

        debug_assert!(start <= end);
        debug_assert!(end <= truncate_from);
        debug_assert!(truncate_from <= self.len());
        debug_assert!(self.is_char_boundary(start));
        debug_assert!(self.is_char_boundary(end));
        debug_assert!(self.is_char_boundary(truncate_from));

        let first = self.as_slice().byte_slice(..start);
        let second = self.as_slice().byte_slice(end..truncate_from);

        // TODO: do this properly.

        *self = Self::from_segments(&[
            first.first_segment(),
            first.second_segment(),
            s,
            second.first_segment(),
            second.second_segment(),
        ]);

        // match (
        //     start <= self.len_first_segment(),
        //     end <= self.len_first_segment(),
        //     truncate_from <= self.len_first_segment(),
        // ) {
        //     (true, true, true) => {
        //         self.len_second_segment = 0;

        //         if (end - start) <= s.len() {
        //             todo!();
        //         }
        //         // self.bytes[start..end].

        //         self.len_first_segment =
        //             (start + s.len() + (truncate_from - end)) as u16;
        //     },

        //     (true, true, false) => {
        //         todo!();
        //     },

        //     (true, false, false) => {
        //         todo!();
        //     },

        //     (false, false, false) => {
        //         todo!();
        //     },

        //     _ => unreachable!(),
        // }
    }

    #[inline]
    fn second_segment(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the bytes in
        // the second segment as valid UTF-8.
        unsafe {
            std::str::from_utf8_unchecked(
                &self.bytes[MAX_BYTES - self.len_second_segment()..],
            )
        }
    }

    /// Returns the summary obtained by summarizing only the text in the given
    /// byte range.
    ///
    /// # Panics
    ///
    /// Panics if `total` is different from the output of `self.summarize()` or
    /// if either the start or the end of the byte range don't lie on a char
    /// boundary.
    #[inline]
    fn summarize_byte_range(
        &self,
        byte_range: Range<usize>,
        total: ChunkSummary,
    ) -> ChunkSummary {
        debug_assert_eq!(total, self.summarize());

        let Range { start, end } = byte_range;

        debug_assert!(start <= end);
        debug_assert!(end <= self.len());
        debug_assert!(self.is_char_boundary(start));
        debug_assert!(self.is_char_boundary(end));

        // Get the summary by directly summarizing the byte range.
        if end - start <= self.len() / 2 {
            match (
                start <= self.len_first_segment(),
                end <= self.len_first_segment(),
            ) {
                (true, true) => {
                    ChunkSummary::from_str(&self.first_segment()[start..end])
                },

                (true, false) => {
                    let end = end - self.len_first_segment();
                    ChunkSummary::from_str(&self.first_segment()[start..])
                        + ChunkSummary::from_str(&self.second_segment()[..end])
                },

                (false, false) => {
                    let start = start - self.len_first_segment();
                    let end = end - self.len_first_segment();
                    ChunkSummary::from_str(&self.second_segment()[start..end])
                },

                _ => unreachable!("start <= end"),
            }
        }
        // Get the summary by subtracting the opposite byte ranges from the
        // total.
        else {
            let complement = match (
                start <= self.len_first_segment(),
                end <= self.len_first_segment(),
            ) {
                (true, true) => {
                    ChunkSummary::from_str(&self.first_segment()[..start])
                        + ChunkSummary::from_str(&self.first_segment()[end..])
                },

                (true, false) => {
                    let end = end - self.len_first_segment();
                    ChunkSummary::from_str(&self.first_segment()[..start])
                        + ChunkSummary::from_str(&self.second_segment()[end..])
                },

                (false, false) => {
                    let start = start - self.len_first_segment();
                    let end = end - self.len_first_segment();
                    ChunkSummary::from_str(&self.second_segment()[..start])
                        + ChunkSummary::from_str(&self.second_segment()[end..])
                },

                _ => unreachable!("start <= end"),
            };

            total - complement
        }
    }

    /// Removes all the text after the byte offset, then pushes the string.
    ///
    /// # Panics
    ///
    /// Panics if the offset doesn't lie on a char boundary or if it's out of
    /// bounds (i.e. > [len()](Self::len())).
    ///
    /// # Examples
    ///
    /// ```
    /// let mut buffer = GapBuffer::<10>::from("aaabbbb"); // "aaa~~~bbbb"
    /// buffer.truncate_and_push(4, "cc"); // => "aaa~~~~bcc"
    /// assert_eq!(buffer.first_segment(), "aaa");
    /// assert_eq!(buffer.second_segment(), "bcc");
    ///
    /// let mut buffer = GapBuffer::<10>::from("aaaabbbb"); // "aaaa~~bbbb";
    /// buffer.truncate_and_push(2, ""); // => "aa~~~~~~~~~"
    /// assert_eq!(buffer.first_segment(), "aa");
    /// assert_eq!(buffer.second_segment(), "");
    /// ```
    #[inline]
    fn truncate_and_push(&mut self, byte_offset: usize, push_back: &str) {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));
        debug_assert!(byte_offset + push_back.len() <= MAX_BYTES);

        if byte_offset <= self.len_first_segment() {
            self.len_first_segment = (byte_offset + push_back.len()) as u16;
            self.len_second_segment = 0;
            let pushed_range = {
                let start = byte_offset;
                start..start + push_back.len()
            };
            self.bytes[pushed_range].copy_from_slice(push_back.as_bytes());
        } else {
            let len_moved = byte_offset - self.len_first_segment();
            let move_range = {
                let start = MAX_BYTES - self.len_second_segment();
                start..start + len_moved
            };
            let push_from = MAX_BYTES - push_back.len();
            self.bytes.copy_within(move_range, push_from - len_moved);
            self.bytes[push_from..].copy_from_slice(push_back.as_bytes());
            self.len_second_segment = (len_moved + push_back.len()) as u16;
        }
    }
}

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub(super) struct ChunkSummary {
    pub(super) bytes: usize,
    pub(super) line_breaks: usize,
}

impl ChunkSummary {
    #[inline]
    pub(super) fn empty() -> Self {
        Self::default()
    }

    #[inline]
    pub(super) fn from_str(s: &str) -> Self {
        Self {
            bytes: s.len(),
            line_breaks: str_indices::lines_lf::count_breaks(s),
        }
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

impl<const MAX_BYTES: usize> Summarize for GapBuffer<MAX_BYTES> {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        self.as_slice().summarize()
    }
}

impl<const MAX_BYTES: usize> BaseMeasured for GapBuffer<MAX_BYTES> {
    type BaseMetric = ByteMetric;
}

impl<const MAX_BYTES: usize> From<GapSlice<'_>> for GapBuffer<MAX_BYTES> {
    #[inline]
    fn from(slice: GapSlice<'_>) -> Self {
        // In the general case the slice will have less than `MAX_BYTES` bytes.
        //
        // We create an owned `GapBuffer` by splitting the bytes of the slice
        // equally between the first and second segments. Any remaining space
        // is left as a middle gap.

        let mut buffer = Self {
            bytes: Box::new([0u8; MAX_BYTES]),
            len_first_segment: 0,
            len_second_segment: 0,
        };

        let target_len_first = slice.len() / 2;

        let mut second_segment = slice.second_segment();

        if slice.len_first_segment() >= target_len_first {
            // Add everything up to the target to our first segment, then add
            // the rest to our second segment.

            let to_first = adjust_split_point::<true>(
                slice.first_segment(),
                target_len_first,
            );

            buffer.bytes[..to_first].copy_from_slice(
                &slice.first_segment().as_bytes()[..to_first],
            );

            buffer.len_first_segment = to_first as u16;

            let range = {
                let to_second = slice.len_first_segment() - to_first;
                let end = MAX_BYTES - second_segment.len();
                let start = end - to_second;
                start..end
            };

            buffer.bytes[range].copy_from_slice(
                &slice.first_segment().as_bytes()[to_first..],
            );

            buffer.len_second_segment =
                (slice.len_first_segment() - to_first) as u16;
        } else {
            // Add the slice's first segment plus part of its second segment to
            // our first segment.

            buffer.bytes[..slice.len_first_segment()]
                .copy_from_slice(slice.first_segment().as_bytes());

            let space_left_on_first =
                target_len_first - slice.len_first_segment();

            let (to_first, rest) =
                split_adjusted::<true>(second_segment, space_left_on_first);

            let range = {
                let start = slice.len_first_segment();
                let end = start + to_first.len();
                start..end
            };

            buffer.bytes[range].copy_from_slice(to_first.as_bytes());

            buffer.len_first_segment =
                (slice.len_first_segment() + to_first.len()) as u16;

            second_segment = rest;
        }

        buffer.bytes[MAX_BYTES - second_segment.len()..]
            .copy_from_slice(second_segment.as_bytes());

        buffer.len_second_segment += second_segment.len() as u16;

        buffer
    }
}

impl<const MAX_BYTES: usize> AsSlice for GapBuffer<MAX_BYTES> {
    type Slice<'a> = GapSlice<'a>;

    #[inline]
    fn as_slice(&self) -> GapSlice<'_> {
        let range = match (
            self.len_first_segment() > 0,
            self.len_second_segment() > 0,
        ) {
            (true, true) => 0..MAX_BYTES,
            (true, false) => 0..self.len_first_segment(),
            (false, true) => MAX_BYTES - self.len_second_segment()..MAX_BYTES,
            (false, false) => 0..0,
        };

        GapSlice {
            bytes: &self.bytes[range],
            len_first_segment: self.len_first_segment,
            len_second_segment: self.len_second_segment,
        }
    }
}

impl<const MAX_BYTES: usize> BalancedLeaf for GapBuffer<MAX_BYTES> {
    #[inline]
    fn is_underfilled(_: GapSlice<'_>, summary: &ChunkSummary) -> bool {
        summary.bytes < Self::min_bytes()
    }

    #[inline]
    fn balance_leaves(
        (left, left_summary): (&mut Self, &mut ChunkSummary),
        (right, right_summary): (&mut Self, &mut ChunkSummary),
    ) {
        // The two leaves can be combined in a single chunk.
        if left.len() + right.len() <= MAX_BYTES {
            let range = MAX_BYTES - left.len_second_segment()..MAX_BYTES;
            let start = left.len_first_segment();
            left.bytes.copy_within(range, start);
            left.len_first_segment += left.len_second_segment;

            let range = {
                let end = MAX_BYTES - right.len_second_segment();
                end - right.len_first_segment()..end
            };

            left.bytes[range]
                .copy_from_slice(right.first_segment().as_bytes());

            left.bytes[MAX_BYTES - right.len_second_segment()..]
                .copy_from_slice(right.second_segment().as_bytes());

            left.len_second_segment =
                right.len_first_segment + right.len_second_segment;

            *left_summary += *right_summary;

            right.len_first_segment = 0;
            right.len_second_segment = 0;
            *right_summary = ChunkSummary::empty();
        }
        // The left side is underfilled -> take text from the right side.
        else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing = Self::min_bytes() - left.len();

            if missing <= right.len_first_segment() {
                let (to_left, _) =
                    split_adjusted::<false>(right.first_segment(), missing);

                let to_left_summary = ChunkSummary::from_str(to_left);

                left.append(to_left);

                right.remove_up_to(to_left.len());

                *left_summary += to_left_summary;
                *right_summary -= to_left_summary;
            } else {
                let missing = missing - right.len_first_segment();

                let (to_left, _) =
                    split_adjusted::<false>(right.second_segment(), missing);

                let to_left_summary =
                    ChunkSummary::from_str(right.first_segment())
                        + ChunkSummary::from_str(to_left);

                left.append_two(right.first_segment(), to_left);

                right.remove_up_to(right.len_first_segment() + to_left.len());

                *left_summary += to_left_summary;
                *right_summary -= to_left_summary;
            }
        }
        // The right side is underfilled -> take text from the left side.
        else if right.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing = Self::min_bytes() - right.len();

            if missing <= left.len_first_segment() {
                let (_, to_right) = split_adjusted::<true>(
                    left.second_segment(),
                    left.len_second_segment() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right);

                right.prepend(to_right);

                left.remove_from(left.len() - to_right.len());

                *left_summary -= to_right_summary;
                *right_summary += to_right_summary;
            } else {
                let missing = missing - left.len_second_segment();

                let (_, to_right) = split_adjusted::<false>(
                    left.first_segment(),
                    left.len_first_segment() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right)
                    + ChunkSummary::from_str(left.second_segment());

                right.prepend_two(to_right, left.second_segment());

                left.remove_from(
                    left.len() - left.len_second_segment() - to_right.len(),
                );

                *left_summary -= to_right_summary;
                *right_summary += to_right_summary;
            }
        }
    }

    #[inline]
    fn balance_slices(
        (left, &left_summary): (GapSlice<'_>, &ChunkSummary),
        (right, &right_summary): (GapSlice<'_>, &ChunkSummary),
    ) -> ((Self, ChunkSummary), Option<(Self, ChunkSummary)>) {
        // Neither side is underfilled.
        if left.len() >= Self::min_bytes() && right.len() >= Self::min_bytes()
        {
            ((left.into(), left_summary), Some((right.into(), right_summary)))
        }
        // The two slices can be combined in a single chunk.
        else if left.len() + right.len() <= MAX_BYTES {
            let combined = Self::from_segments(&[
                left.first_segment(),
                left.second_segment(),
                right.first_segment(),
                right.second_segment(),
            ]);

            ((combined, left_summary + right_summary), None)
        }
        // The left side is underfilled -> take text from the right side.
        else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing = Self::min_bytes() - left.len();

            if right.len_first_segment() >= missing {
                let (to_left, keep_right) =
                    split_adjusted::<true>(right.first_segment(), missing);

                let left = Self::from_segments(&[
                    left.first_segment(),
                    left.second_segment(),
                    to_left,
                ]);

                let right =
                    Self::from_segments(&[keep_right, right.second_segment()]);

                let to_left_summary = ChunkSummary::from_str(to_left);

                (
                    (left, left_summary + to_left_summary),
                    Some((right, right_summary - to_left_summary)),
                )
            } else {
                let missing = missing - right.len_first_segment();

                let (to_left, keep_right) =
                    split_adjusted::<true>(right.second_segment(), missing);

                let to_left_summary =
                    ChunkSummary::from_str(right.first_segment())
                        + ChunkSummary::from_str(to_left);

                let left = Self::from_segments(&[
                    left.first_segment(),
                    left.second_segment(),
                    right.first_segment(),
                    to_left,
                ]);

                let right = Self::from_segments(&[keep_right]);

                (
                    (left, left_summary + to_left_summary),
                    Some((right, right_summary - to_left_summary)),
                )
            }
        }
        // The right side is underfilled -> take text from the left side.
        else if right.len() < Self::min_bytes() {
            debug_assert!(left.len() > Self::min_bytes());

            let missing = Self::min_bytes() - right.len();

            if left.len_second_segment() >= missing {
                let (keep_left, to_right) = split_adjusted::<true>(
                    left.second_segment(),
                    left.len_second_segment() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right);

                let left =
                    Self::from_segments(&[left.first_segment(), keep_left]);

                let right = Self::from_segments(&[
                    to_right,
                    right.first_segment(),
                    right.second_segment(),
                ]);

                (
                    (left, left_summary - to_right_summary),
                    Some((right, right_summary + to_right_summary)),
                )
            } else {
                let missing = missing - left.len_second_segment();

                let (keep_left, to_right) = split_adjusted::<true>(
                    left.first_segment(),
                    left.len_first_segment() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right)
                    + ChunkSummary::from_str(left.second_segment());

                let right = Self::from_segments(&[
                    to_right,
                    left.second_segment(),
                    right.first_segment(),
                    right.second_segment(),
                ]);

                let left = Self::from_segments(&[keep_left]);

                (
                    (left, left_summary - to_right_summary),
                    Some((right, right_summary + to_right_summary)),
                )
            }
        } else {
            unreachable!();
        }
    }
}

impl<const MAX_BYTES: usize> ReplaceableLeaf<ByteMetric>
    for GapBuffer<MAX_BYTES>
{
    type Replacement<'a> = &'a str;

    type ExtraLeaves = std::vec::IntoIter<Self>;

    #[inline]
    fn replace<R>(
        &mut self,
        summary: &mut ChunkSummary,
        range: R,
        replacement: &str,
    ) -> Option<Self::ExtraLeaves>
    where
        R: RangeBounds<ByteMetric>,
    {
        let (start, end) = {
            let (s, e) = range_bounds_to_start_end(range, 0, self.len());

            debug_assert!(s <= e);
            debug_assert!(e <= self.len());

            assert!(self.is_char_boundary(s));
            assert!(self.is_char_boundary(e));

            (s, e)
        };

        if replacement.len() + (end - start) <= self.len_gap() {
            if end > start {
                *summary -= self.summarize_byte_range(start..end, *summary);
                *summary += ChunkSummary::from_str(replacement);
                self.replace(start..end, replacement);
            } else {
                *summary += ChunkSummary::from_str(replacement);
                self.insert(start, replacement)
            }

            return None;
        }

        let mut start = start;

        let mut push_back = "";

        let mut extra_chunks = ["", ""];

        let mut replacement = replacement;

        let (mut penultimate_extra, mut last_extra) =
            if end <= self.len_first_segment() {
                (&self.first_segment()[end..], self.second_segment())
            } else {
                let end = end - self.len_first_segment();
                (&self.second_segment()[end..], "")
            };

        let mut truncate_from = end;

        // The start of the replaced byte range is small enough to leave
        // this chunk underfilled => add to self from the replacement and the
        // extras.
        if start < Self::min_bytes() {
            // accaaaa|aaaaaaa
            //  \/
            //  bbbbb
            //
            // a + bbbbb|aaaa|aaaaaaa
            //
            // add bbbbb
            //
            // abbbbb   |aaaa|aaaaaaa
            //
            // still not enough, split aaaa at 1 and add it
            //
            // abbbbba | aaa|aaaaaaa
            //
            // accaaaa|aaaaaaa
            //
            // take 0..1,
            // truncate 1..3
            // add "bbbbb"
            // take 3..4
            // truncate 4..
            //
            // which is like saying
            //
            // replace 1..3 with "bbbbb", truncate 4..
            //
            // while now I'm saying
            //
            // truncate 1..
            // add "bbbbb"
            // add "a"

            let missing = Self::min_bytes() - start;

            // The replacement text is long enough to re-fill self. E.g. if
            // we're replacing 2..3 of "aaaaa~bbbb" with "cccc", with
            // max_bytes = 10 and min_bytes = 5:
            //
            // `self[..start] = "aa", "aa".len() = 2 < min_bytes`
            // `replacement = "cccc"`
            // `penultimate_extra = "aa"`
            // `last_extra = "bbbb"`
            // `missing = 5 - start = 3`
            //
            // In this case `"cccc".len() = 4 >= missing`, so we split "cccc"
            // at 3 getting "ccc" and "c". "ccc" will be pushed to this chunk
            // and "c" is the new replacement.
            if replacement.len() >= missing {
                let (left, right) =
                    split_adjusted::<true>(replacement, missing);

                push_back = left;
                replacement = right;
            }
            // TODO: docs
            else if replacement.len() + penultimate_extra.len() >= missing {
                let missing = missing - replacement.len();

                let (left, right) =
                    split_adjusted::<true>(penultimate_extra, missing);

                push_back = replacement;
                truncate_from += left.len();

                replacement = "";
                penultimate_extra = right;
            }
            // TODO: docs
            else {
                let missing =
                    missing - replacement.len() - penultimate_extra.len();

                let (left, right) =
                    split_adjusted::<true>(last_extra, missing);

                push_back = replacement;
                truncate_from += penultimate_extra.len() + left.len();

                replacement = "";
                penultimate_extra = "";
                last_extra = right;
            }
        }
        // The replacement text and the extra chunks are not long enough to
        // form a new gap buffer that's not underfilled => add text from
        // self.
        else if replacement.len() + (self.len() - end) < Self::min_bytes() {
            let missing =
                Self::min_bytes() - replacement.len() - self.len() + end;

            let (this_left, this_right) = if start <= self.len_first_segment()
            {
                ("", &self.first_segment()[..start])
            } else {
                let start = start - self.len_first_segment();
                (self.first_segment(), &self.second_segment()[..start])
            };

            if this_right.len() >= missing {
                let split_at = adjust_split_point::<true>(
                    this_right,
                    this_right.len() - missing,
                );

                extra_chunks[0] = &this_right[split_at..];

                start = this_left.len() + split_at;
            } else {
                let missing = missing - this_right.len();

                let split_at = adjust_split_point::<true>(
                    this_left,
                    this_left.len() - missing,
                );

                extra_chunks[0] = &this_left[split_at..];
                extra_chunks[1] = this_right;

                start = split_at;
            }
        };

        let extras: Vec<Self> = ChunkResegmenter::new([
            extra_chunks[0],
            extra_chunks[1],
            replacement,
            penultimate_extra,
            last_extra,
        ])
        .collect();

        if end == truncate_from {
            self.truncate_and_push(start, push_back);
        } else {
            self.replace_and_truncate(start..end, push_back, truncate_from);
        }

        *summary = self.summarize();

        Some(extras.into_iter())
    }
}

/// An iterator over the valid split points of a `ChunkSlice`.
///
/// All the `ChunkSlice`s yielded by this iterator are guaranteed to never
/// split char boundaries and CRLF pairs and to be within the chunk bounds of
/// [`RopeChunk`]s.
///
/// The only exception is if the slice fed to [`Self::new()`] is shorter than
/// [`RopeChunk::chunk_min()`], in which case this will only yield that slice.
pub(super) struct ChunkSegmenter<'a, const MAX_BYTES: usize> {
    s: &'a str,
    yielded: usize,
}

impl<'a, const MAX_BYTES: usize> Iterator for ChunkSegmenter<'a, MAX_BYTES> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut remaining = self.s.len() - self.yielded;

        let chunk = if remaining == 0 {
            return None;
        } else if remaining > MAX_BYTES {
            let mut chunk_len = MAX_BYTES;

            remaining -= chunk_len;

            let min = GapBuffer::<MAX_BYTES>::min_bytes();

            if remaining < min {
                chunk_len -= min - remaining;
            }

            chunk_len = adjust_split_point::<false>(
                &self.s[self.yielded..],
                chunk_len,
            );

            &self.s[self.yielded..(self.yielded + chunk_len)]
        } else {
            debug_assert!(
                self.yielded == 0
                    || remaining >= GapBuffer::<MAX_BYTES>::chunk_min()
            );

            &self.s[self.s.len() - remaining..]
        };

        self.yielded += chunk.len();

        Some(chunk)
    }
}

impl<const MAX_BYTES: usize> std::iter::FusedIterator
    for ChunkSegmenter<'_, MAX_BYTES>
{
}

/// TODO: docs
pub(super) struct ChunkResegmenter<
    'a,
    const CHUNKS: usize,
    const MAX_BYTES: usize,
> {
    segments: [&'a str; CHUNKS],
    start: usize,
    yielded: usize,
    total: usize,
}

impl<'a, const CHUNKS: usize, const MAX_BYTES: usize>
    ChunkResegmenter<'a, CHUNKS, MAX_BYTES>
{
    #[inline]
    fn new(segments: [&'a str; CHUNKS]) -> Self {
        let total = segments.iter().map(|s| s.len()).sum::<usize>();

        debug_assert!(total >= GapBuffer::<MAX_BYTES>::chunk_min());

        Self { total, segments, yielded: 0, start: 0 }
    }
}

impl<'a, const CHUNKS: usize, const MAX_BYTES: usize> Iterator
    for ChunkResegmenter<'a, CHUNKS, MAX_BYTES>
{
    type Item = GapBuffer<MAX_BYTES>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let remaining = self.total - self.yielded;

        let next = if remaining == 0 {
            return None;
        } else if remaining > MAX_BYTES {
            let mut idx_last = self.start;

            let mut bytes_in_next = 0;

            let min_bytes = GapBuffer::<MAX_BYTES>::min_bytes();

            for (idx, &segment) in
                self.segments[self.start..].iter().enumerate()
            {
                let new_bytes_in_next = bytes_in_next + segment.len();

                let next_too_big = new_bytes_in_next > MAX_BYTES;

                let rest_too_small = remaining - new_bytes_in_next < min_bytes;

                if next_too_big || rest_too_small {
                    idx_last += idx;
                    break;
                } else {
                    bytes_in_next = new_bytes_in_next;
                }
            }

            let mut last_chunk_len = MAX_BYTES - bytes_in_next;

            // new remaining = remaining - bytes_in_next - last_chunk_len
            if remaining - bytes_in_next < last_chunk_len + min_bytes {
                last_chunk_len = remaining - bytes_in_next - min_bytes
            }

            let (left, right) = split_adjusted::<false>(
                self.segments[idx_last],
                last_chunk_len,
            );

            self.segments[idx_last] = left;

            let next = GapBuffer::<MAX_BYTES>::from_segments(
                &self.segments[self.start..=idx_last],
            );

            self.segments[idx_last] = right;

            self.start = idx_last;

            next
        } else {
            debug_assert!(remaining >= GapBuffer::<MAX_BYTES>::chunk_min());
            GapBuffer::<MAX_BYTES>::from_segments(&self.segments[self.start..])
        };

        debug_assert!(next.len() >= GapBuffer::<MAX_BYTES>::chunk_min());

        self.yielded += next.len();

        Some(next)
    }
}

impl<const CHUNKS: usize, const MAX_BYTES: usize> std::iter::FusedIterator
    for ChunkResegmenter<'_, CHUNKS, MAX_BYTES>
{
}

#[cfg(test)]
mod tests {
    use super::*;

    impl<const N: usize> PartialEq<GapBuffer<N>> for &str {
        fn eq(&self, rhs: &GapBuffer<N>) -> bool {
            self.len() == rhs.len()
                && rhs.first_segment() == &self[..rhs.len_first_segment()]
                && rhs.second_segment() == &self[rhs.len_first_segment()..]
        }
    }

    // We only need this to compare `Option<GapBuffer>` with `None`.
    impl<const N: usize> PartialEq<GapBuffer<N>> for GapBuffer<N> {
        fn eq(&self, _rhs: &GapBuffer<N>) -> bool {
            unimplemented!();
        }
    }

    #[test]
    fn chunk_resegmenter_0() {
        let chunks = ["aaaa", "b"];
        let mut resegmenter = ChunkResegmenter::<2, 4>::new(chunks);

        assert_eq!("aaa", resegmenter.next().unwrap());
        assert_eq!("ab", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn chunk_resegmenter_1() {
        let chunks = ["a", "a", "bcdefgh"];
        let mut resegmenter = ChunkResegmenter::<3, 4>::new(chunks);

        assert_eq!("aabc", resegmenter.next().unwrap());
        assert_eq!("def", resegmenter.next().unwrap());
        assert_eq!("gh", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn chunk_resegmenter_2() {
        let chunks = ["a", "abcdefgh", "b"];
        let mut resegmenter = ChunkResegmenter::<3, 4>::new(chunks);

        assert_eq!("aabc", resegmenter.next().unwrap());
        assert_eq!("defg", resegmenter.next().unwrap());
        assert_eq!("hb", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn chunk_resegmenter_3() {
        let chunks = ["a", "b"];
        let mut resegmenter = ChunkResegmenter::<2, 4>::new(chunks);

        assert_eq!("ab", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn chunk_resegmenter_4() {
        let chunks = ["a", "b", ""];
        let mut resegmenter = ChunkResegmenter::<3, 4>::new(chunks);

        assert_eq!("ab", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn chunk_resegmenter_5() {
        let chunks = ["こんい"];
        let mut resegmenter = ChunkResegmenter::<1, 4>::new(chunks);

        assert_eq!("こ", resegmenter.next().unwrap());
        assert_eq!("ん", resegmenter.next().unwrap());
        assert_eq!("い", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }
}
