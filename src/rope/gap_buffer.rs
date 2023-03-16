//! This module exports the [`GapBuffer`] struct and a few of its methods.
//!
//! It also implements several traits exported by the [tree](crate::tree)
//! module on it to be able to use it as the leaf of our [`Rope`](crate::Rope).

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

// To update:
//
// split_at_offset
// first_unit
// last_unit

/// A [gap buffer] with a max capacity of `2^16 - 1` bytes.
///
/// TODO: docs
///
/// [gap buffer]: https://en.wikipedia.org/wiki/Gap_buffer
#[derive(Clone)]
pub(super) struct GapBuffer<const MAX_BYTES: usize> {
    bytes: Box<[u8; MAX_BYTES]>,
    len_left: u16,
    line_breaks_left: u16,
    len_right: u16,
}

impl<const MAX_BYTES: usize> std::fmt::Debug for GapBuffer<MAX_BYTES> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("\"")?;
        debug_no_quotes(self.left_chunk(), f)?;
        write!(f, "{:~^1$}", "", self.len_gap())?;
        debug_no_quotes(self.right_chunk(), f)?;
        f.write_str("\"")
    }
}

impl<const MAX_BYTES: usize> Default for GapBuffer<MAX_BYTES> {
    #[inline]
    fn default() -> Self {
        Self {
            bytes: Box::new([0u8; MAX_BYTES]),
            len_left: 0,
            line_breaks_left: 0,
            len_right: 0,
        }
    }
}

impl<const MAX_BYTES: usize> From<&str> for GapBuffer<MAX_BYTES> {
    /// # Panics
    ///
    /// Panics if the string's byte length is greater than `MAX_BYTES`.
    #[inline]
    fn from(s: &str) -> Self {
        debug_assert!(s.len() <= MAX_BYTES);
        if s.is_empty() {
            Self::default()
        } else {
            Self::from_chunks(&[s])
        }
    }
}

impl<const MAX_BYTES: usize> GapBuffer<MAX_BYTES> {
    /// TODO: docs
    #[inline]
    fn add_text_from_right(
        &mut self,
        bytes_to_add: usize,
        right: &mut Self,
    ) -> ChunkSummary {
        debug_assert!(right.len() >= bytes_to_add);
        debug_assert!(self.len() + bytes_to_add <= MAX_BYTES);

        if bytes_to_add <= right.len_left() {
            let (move_left, keep_right) =
                split_adjusted::<false>(right.left_chunk(), bytes_to_add);

            let summary = if move_left.len() <= right.len_left() {
                ChunkSummary::from_str(move_left)
            } else {
                ChunkSummary {
                    bytes: move_left.len(),
                    line_breaks: right.line_breaks_left as usize
                        - count_line_breaks(keep_right),
                }
            };

            self.append_str(move_left);

            right.remove_up_to(move_left.len(), summary.line_breaks);

            summary
        } else {
            let (move_left, _) = split_adjusted::<false>(
                right.right_chunk(),
                bytes_to_add - right.len_left(),
            );

            let summary = ChunkSummary {
                bytes: right.len_left(),
                line_breaks: right.line_breaks_left as usize,
            } + ChunkSummary::from_str(move_left);

            self.append_two(right.left_chunk(), move_left);

            right.remove_up_to(summary.bytes, summary.line_breaks);

            summary
        }
    }

    /// TODO: docs
    #[inline]
    fn append_other(&mut self, tot_line_breaks: usize, other: &mut Self) {
        debug_assert_eq!(self.summarize().line_breaks, tot_line_breaks);

        let len_left = self.len_left();
        let len_rigth = self.len_right();

        // Move this buffer's right chunk after its left chunk.
        self.bytes.copy_within(MAX_BYTES - len_rigth..MAX_BYTES, len_left);

        self.len_left += self.len_right;

        let len_left = other.len_left();
        let len_right = other.len_right();

        // Move the other buffer's left chunk to this buffer's right chunk.
        let end = MAX_BYTES - len_right;
        let start = end - len_left;
        self.bytes[start..end].copy_from_slice(other.left_chunk().as_bytes());

        // Move the other buffer's right chunk to this buffer's right chunk.
        self.bytes[MAX_BYTES - len_right..]
            .copy_from_slice(other.right_chunk().as_bytes());

        self.len_left += self.len_right;
        self.line_breaks_left = tot_line_breaks as u16;
        self.len_right = other.len() as u16;

        other.len_left = 0;
        other.line_breaks_left = 0;
        other.len_right = 0;
    }

    /// Appends the given string to `self`, shifting the bytes currently in the
    /// right chunk to the left to make space. The left chunk is left
    /// untouched.
    ///
    /// # Panics
    ///
    /// Panics if the string's byte length is greater that the length of the
    /// gap.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    ///
    /// let mut buffer = GapBuffer::<10>::new("aabb");
    /// assert_eq!(buffer.left_chunk(), "aa");
    /// assert_eq!(buffer.right_chunk(), "bb");
    ///
    /// buffer.append_str("cc");
    /// assert_eq!(buffer.left_chunk(), "aa");
    /// assert_eq!(buffer.right_chunk(), "bbcc");
    /// ```
    #[inline]
    pub fn append_str(&mut self, s: &str) {
        debug_assert!(s.len() <= self.len_gap());

        let start = MAX_BYTES - self.len_right();

        // Shift the second segment to the left.
        self.bytes.copy_within(start.., start - s.len());

        // Append the string.
        self.bytes[MAX_BYTES - s.len()..].copy_from_slice(s.as_bytes());

        self.len_right += s.len() as u16;
    }

    /// Exactly the same as [append_str()](Self::append_str()), except it
    /// appends two strings instead of one.
    ///
    /// # Panics
    ///
    /// Panics if the combined byte length of the two strings is greater that
    /// the length of the gap.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    ///
    /// let mut buffer = GapBuffer::<10>::new("aabb");
    ///
    /// buffer.append_two("cc", "dd");
    /// assert_eq!(buffer.left_chunk(), "aa");
    /// assert_eq!(buffer.right_chunk(), "bbccdd");
    /// ```
    #[inline]
    fn append_two(&mut self, a: &str, b: &str) {
        debug_assert!(a.len() + b.len() <= self.len_gap());

        // Shift the second chunk to the left.
        let start = MAX_BYTES - self.len_right();
        self.bytes.copy_within(start.., start - a.len() - b.len());

        // Append the first string.
        let end = MAX_BYTES - b.len();
        self.bytes[end - a.len()..end].copy_from_slice(a.as_bytes());

        // Append the second string.
        let range = MAX_BYTES - b.len()..MAX_BYTES;
        self.bytes[range].copy_from_slice(b.as_bytes());

        self.len_right += (a.len() + b.len()) as u16;
    }

    /// TODO: docs
    #[inline]
    fn assert_char_boundary(&self, byte_offset: usize) {
        debug_assert!(byte_offset <= self.len());

        if !self.is_char_boundary(byte_offset) {
            if byte_offset < self.len_left() {
                byte_offset_not_char_boundary(self.left_chunk(), byte_offset)
            } else {
                byte_offset_not_char_boundary(
                    self.right_chunk(),
                    byte_offset - self.len_left(),
                )
            }
        }
    }

    /// The number of bytes `RopeChunk`s must always stay over.
    pub(super) const fn chunk_min() -> usize {
        // TODO: explain why the wiggle room is 3 bytes.
        Self::min_bytes().saturating_sub(3)
    }

    /// TODO: docs
    #[inline]
    pub(super) fn chunk_segmenter(s: &str) -> ChunkSegmenter<'_, MAX_BYTES> {
        ChunkSegmenter { s, yielded: 0 }
    }

    /// TODO: docs
    #[inline]
    fn left_chunk(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the bytes in
        // the first segment as valid UTF-8.
        unsafe {
            std::str::from_utf8_unchecked(&self.bytes[..self.len_left()])
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
    fn from_chunks(chunks: &[&str]) -> Self {
        let total_len = chunks.iter().map(|s| s.len() as u16).sum::<u16>();

        debug_assert!(total_len > 0);

        debug_assert!(total_len <= MAX_BYTES as u16);

        let add_to_first = total_len / 2;

        let mut bytes = Box::new([0u8; MAX_BYTES]);

        let mut len_left_chunk = 0;

        let mut line_breaks_left_chunk = 0;

        let mut chunks = chunks.iter();

        for &chunk in chunks.by_ref() {
            if len_left_chunk + chunk.len() as u16 <= add_to_first {
                let range = {
                    let start = len_left_chunk as usize;
                    let end = start + chunk.len();
                    start..end
                };

                bytes[range].copy_from_slice(chunk.as_bytes());

                len_left_chunk += chunk.len() as u16;

                line_breaks_left_chunk += count_line_breaks(chunk) as u16;
            } else {
                let (to_first, to_second) = split_adjusted::<true>(
                    chunk,
                    (add_to_first - len_left_chunk) as usize,
                );

                let range = {
                    let start = len_left_chunk as usize;
                    let end = start + to_first.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_first.as_bytes());

                len_left_chunk += to_first.len() as u16;

                line_breaks_left_chunk += count_line_breaks(to_first) as u16;

                let len_right_chunk = total_len - len_left_chunk;

                let mut start = MAX_BYTES as u16 - len_right_chunk;

                let range = {
                    let start = start as usize;
                    let end = start + to_second.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_second.as_bytes());

                start += to_second.len() as u16;

                for &segment in chunks {
                    let range = {
                        let start = start as usize;
                        let end = start + segment.len();
                        start..end
                    };

                    bytes[range].copy_from_slice(segment.as_bytes());

                    start += segment.len() as u16;
                }

                return Self {
                    bytes,
                    len_left: len_left_chunk,
                    line_breaks_left: line_breaks_left_chunk,
                    len_right: len_right_chunk,
                };
            }
        }

        unreachable!("This can only be reached if the total length is zero");
    }

    /// Returns `true` if the buffer ends with a newline ('\n') character.
    #[inline]
    pub(super) fn has_trailing_newline(&self) -> bool {
        last_byte_is_newline(self.last_chunk())
    }

    /// Inserts the string at the given byte offset, moving the gap to the new
    /// insertion point if necessary.
    ///
    /// # Panics
    ///
    /// Panics if the byte offset is not a char boundary of if the byte length
    /// of the string is greater than the length of the gap.
    #[inline]
    pub(super) fn insert(
        &mut self,
        insert_at: usize,
        s: &str,
        summary: ChunkSummary,
    ) -> ChunkSummary {
        debug_assert!(insert_at <= self.len());
        debug_assert!(self.is_char_boundary(insert_at));
        debug_assert!(s.len() <= self.len_gap());
        debug_assert_eq!(self.summarize(), summary);

        self.move_gap(insert_at, summary.line_breaks);

        debug_assert_eq!(insert_at, self.len_left());

        let insert_range = {
            let start = self.len_left();
            let end = start + s.len();
            start..end
        };

        self.bytes[insert_range].copy_from_slice(s.as_bytes());
        self.len_left += s.len() as u16;

        let inserted_line_breaks = count_line_breaks(s);

        self.line_breaks_left += inserted_line_breaks as u16;

        ChunkSummary {
            bytes: self.len(),
            line_breaks: summary.line_breaks + inserted_line_breaks,
        }
    }

    #[inline]
    fn is_char_boundary(&self, byte_offset: usize) -> bool {
        debug_assert!(byte_offset <= self.len());

        if byte_offset <= self.len_left() {
            self.left_chunk().is_char_boundary(byte_offset)
        } else {
            self.right_chunk().is_char_boundary(byte_offset - self.len_left())
        }
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The second segment if it's not empty, or the first one otherwise.
    #[inline]
    pub(super) fn last_chunk(&self) -> &str {
        if !self.right_chunk().is_empty() {
            self.right_chunk()
        } else {
            self.left_chunk()
        }
    }

    /// Returns the combined byte length of the buffer's left and right chunks.
    #[inline]
    fn len(&self) -> usize {
        self.len_left() + self.len_right()
    }

    #[inline]
    fn len_left(&self) -> usize {
        self.len_left as _
    }

    #[inline]
    fn len_gap(&self) -> usize {
        MAX_BYTES - self.len_left() - self.len_right()
    }

    #[inline]
    fn len_right(&self) -> usize {
        self.len_right as _
    }

    /// TODO: docs
    #[inline]
    fn line_breaks_left_before_offset(&self, offset: usize) -> u16 {
        if offset <= self.len_left() {
            if offset >= self.len_left() / 2 {
                count_line_breaks(&self.left_chunk()[offset..]) as u16
            } else {
                self.line_breaks_left
                    - count_line_breaks(&self.left_chunk()[..offset]) as u16
            }
        } else {
            self.line_breaks_left
        }
    }

    /// The minimum number of bytes this buffer should have to not be
    /// considered underfilled.
    pub(super) const fn min_bytes() -> usize {
        MAX_BYTES / 2
    }

    /// TODO: docs
    #[inline]
    fn move_gap(&mut self, byte_offset: usize, tot_line_breaks: usize) {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));
        debug_assert_eq!(self.summarize().line_breaks, tot_line_breaks);

        let offset = byte_offset;

        #[allow(clippy::comparison_chain)]
        // The offset splits the first segment => move all the text after the
        // offset to the start of the second segment.
        //
        // aa|bb~~~ccc => aa~~~bbccc
        if offset < self.len_left() {
            let move_range = offset..self.len_left();
            let len_moved = self.len_left() - offset;

            if len_moved <= self.len_left() / 2 {
                self.line_breaks_left -=
                    count_line_breaks(&self.left_chunk()[offset..]) as u16;
            } else {
                self.line_breaks_left =
                    count_line_breaks(&self.left_chunk()[..offset]) as u16;
            }

            self.len_right += len_moved as u16;
            let start = MAX_BYTES - self.len_right();
            self.bytes.copy_within(move_range, start);
            self.len_left -= len_moved as u16;
        }
        // The offset splits the second segment => move all the text before the
        // offset to the end of the first segment.
        //
        // aaa~~~bb|cc => aaabb~~~cc
        else if offset > self.len_left() {
            let len_moved = offset - self.len_left();

            let moved_line_breaks = if len_moved <= self.len_right() / 2 {
                count_line_breaks(&self.right_chunk()[..len_moved])
            } else {
                tot_line_breaks
                    - self.line_breaks_left as usize
                    - count_line_breaks(&self.right_chunk()[len_moved..])
            };

            self.line_breaks_left += moved_line_breaks as u16;

            let move_range = {
                let start = MAX_BYTES - self.len_right();
                let end = start + len_moved;
                start..end
            };

            let start = self.len_left();
            self.bytes.copy_within(move_range, start);
            self.len_left += len_moved as u16;
            self.len_right -= len_moved as u16;
        }

        debug_assert_eq!(offset, self.len_left());
    }

    /// TODO: docs
    #[inline]
    fn move_text_to_right(
        &mut self,
        bytes_to_move: usize,
        right: &mut Self,
    ) -> ChunkSummary {
        debug_assert!(bytes_to_move <= self.len());
        debug_assert!(right.len() + bytes_to_move <= MAX_BYTES);

        if bytes_to_move <= self.len_right() {
            let (_, move_right) = split_adjusted::<true>(
                self.right_chunk(),
                self.len_right() - bytes_to_move,
            );

            let summary = ChunkSummary::from_str(move_right);

            right.prepend(move_right, summary.line_breaks);

            self.remove_from(self.len() - move_right.len(), 0);

            summary
        } else {
            let (_, move_right) = split_adjusted::<true>(
                self.left_chunk(),
                self.len_left() - (bytes_to_move - self.len_right()),
            );

            let move_right_summary = ChunkSummary::from_str(move_right);

            let summary = move_right_summary
                + ChunkSummary::from_str(self.right_chunk());

            right.prepend_two(
                move_right,
                self.right_chunk(),
                summary.line_breaks,
            );

            self.remove_from(
                self.len() - self.len_right() - move_right.len(),
                move_right_summary.line_breaks as u16,
            );

            summary
        }
    }

    /// TODO: docs
    #[inline]
    fn prepend(&mut self, s: &str, prepended_line_breaks: usize) {
        debug_assert!(s.len() <= self.len_gap());
        debug_assert_eq!(count_line_breaks(s), prepended_line_breaks);

        // Shift the first segment to the right.
        let len_first = self.len_left();
        self.bytes.copy_within(..len_first, s.len());

        // Prepend the string.
        self.bytes[..s.len()].copy_from_slice(s.as_bytes());

        self.len_left += s.len() as u16;
        self.line_breaks_left += prepended_line_breaks as u16;
    }

    /// TODO: docs
    #[inline]
    fn prepend_two(&mut self, a: &str, b: &str, prepended_line_breaks: usize) {
        debug_assert!(a.len() + b.len() <= self.len_gap());
        debug_assert_eq!(
            count_line_breaks(a) + count_line_breaks(b),
            prepended_line_breaks
        );

        // Shift the first segment to the right.
        let len_first = self.len_left();
        self.bytes.copy_within(..len_first, a.len() + b.len());

        // Prepend the first string.
        self.bytes[..a.len()].copy_from_slice(a.as_bytes());

        // Prepend the second string.
        self.bytes[a.len()..a.len() + b.len()].copy_from_slice(b.as_bytes());

        self.len_left += (a.len() + b.len()) as u16;
        self.line_breaks_left += prepended_line_breaks as u16;
    }

    /// Pushes as mush of the slice as possible into this chunk, returning the
    /// rest (if any).
    ///
    /// TODO: better docs, panics, examples.
    pub(super) fn push_with_remainder<'a>(
        &mut self,
        s: &'a str,
    ) -> Option<&'a str> {
        debug_assert_eq!(self.len_right(), 0);

        let space_left = MAX_BYTES - self.len_left();
        let (push, rest) = split_adjusted::<false>(s, space_left);

        debug_assert!(push.len() <= space_left);

        let start = self.len_left();
        self.bytes[start..start + push.len()].copy_from_slice(push.as_bytes());

        self.len_left += push.len() as u16;
        self.line_breaks_left += count_line_breaks(push) as u16;

        (!rest.is_empty()).then_some(rest)
    }

    /// TODO: docs
    #[inline]
    fn remove_from(
        &mut self,
        byte_offset: usize,
        removed_line_breaks_left: u16,
    ) {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));
        debug_assert!(removed_line_breaks_left <= self.line_breaks_left);

        if byte_offset <= self.len_left() {
            self.len_left = byte_offset as u16;
            self.len_right = 0;
            self.line_breaks_left -= removed_line_breaks_left;
        } else {
            debug_assert_eq!(removed_line_breaks_left, 0);
            let byte_offset = byte_offset - self.len_left();
            let start = MAX_BYTES - self.len_right();
            let end = start + byte_offset;
            self.bytes.copy_within(start..end, MAX_BYTES - byte_offset);
            self.len_right = byte_offset as u16;
        }
    }

    /// TODO: docs
    #[inline]
    fn remove_up_to(
        &mut self,
        byte_offset: usize,
        removed_line_breaks: usize,
    ) {
        debug_assert!(self.is_char_boundary(byte_offset));

        debug_assert_eq!(
            self.summarize_range(0..byte_offset, self.summarize()).line_breaks,
            removed_line_breaks
        );

        if byte_offset <= self.len_left() {
            let len_moved = self.len_left() - byte_offset;
            let moved_range = {
                let end = self.len_left();
                end - len_moved..end
            };
            self.bytes.copy_within(moved_range, 0);
            self.len_left = len_moved as u16;
        } else {
            self.len_right -= (byte_offset - self.len_left()) as u16;
            self.len_left = 0;
        }

        self.line_breaks_left =
            self.line_breaks_left.saturating_sub(removed_line_breaks as u16);
    }

    /// TODO: docs
    #[inline]
    fn replace_non_overflowing(
        &mut self,
        byte_range: Range<usize>,
        s: &str,
        summary: ChunkSummary,
    ) -> ChunkSummary {
        let Range { start, end } = byte_range;

        let len_replaced = end - start;

        debug_assert!(start <= end);
        debug_assert!(end <= self.len());
        debug_assert!(self.is_char_boundary(start));
        debug_assert!(self.is_char_boundary(end));
        debug_assert!(self.len() - (end - start) + s.len() <= MAX_BYTES);

        self.move_gap(end, summary.line_breaks);

        debug_assert_eq!(end, self.len_left());

        let removed_summary = self.summarize_range(start..end, summary);

        let added_summary = ChunkSummary::from_str(s);

        if !s.is_empty() {
            #[allow(clippy::comparison_chain)]
            // We're adding more text than we're deleting.
            if len_replaced < s.len() {
                let replace = &s.as_bytes()[..len_replaced];
                let add = &s.as_bytes()[len_replaced..];

                self.bytes[start..end].copy_from_slice(replace);

                let adding = s.len() - len_replaced;

                self.bytes[end..end + adding].copy_from_slice(add);

                self.len_left += adding as u16;
            }
            // We're deleting more text than we're adding.
            else if len_replaced > s.len() {
                self.bytes[start..start + s.len()]
                    .copy_from_slice(s.as_bytes());

                self.len_left = (start + s.len()) as u16;
            } else {
                self.bytes[start..end].copy_from_slice(s.as_bytes());
            }
        } else {
            self.len_left -= len_replaced as u16;
        }

        self.line_breaks_left -= removed_summary.line_breaks as u16;
        self.line_breaks_left += added_summary.line_breaks as u16;

        summary - removed_summary + added_summary
    }

    /// TODO: docs
    #[inline]
    fn replace_overflowing(
        &mut self,
        byte_range: Range<usize>,
        s: &str,
    ) -> (ChunkSummary, Vec<Self>) {
        let Range { start, end } = byte_range;

        debug_assert!(start <= end);
        debug_assert!(end <= self.len());
        debug_assert!(self.is_char_boundary(start));
        debug_assert!(self.is_char_boundary(end));
        debug_assert!(self.len() - (end - start) + s.len() > MAX_BYTES);

        let (extra_left, extra_right) = if end <= self.len_left() {
            (&self.left_chunk()[end..], self.right_chunk())
        } else {
            let end = end - self.len_left();
            ("", &self.right_chunk()[end..])
        };

        if start < Self::min_bytes() {
            let mut replacement = s;

            let mut truncate_from = end;

            let missing = Self::min_bytes() - start;

            let extras = if s.len() >= missing {
                let (left, right) = split_adjusted::<true>(s, missing);

                replacement = left;

                ChunkResegmenter::new([right, extra_left, extra_right])
                    .collect()
            } else if s.len() + extra_left.len() >= missing {
                let missing = missing - s.len();

                let (left, right) =
                    split_adjusted::<true>(extra_left, missing);

                truncate_from += left.len();

                ChunkResegmenter::new([right, extra_right]).collect()
            } else {
                let missing = missing - s.len() - extra_left.len();

                let (left, right) =
                    split_adjusted::<true>(extra_right, missing);

                truncate_from += extra_left.len() + left.len();

                ChunkResegmenter::new([right]).collect()
            };

            let removed_line_breaks_left = self.line_breaks_left
                - self.line_breaks_left_before_offset(truncate_from);

            self.remove_from(truncate_from, removed_line_breaks_left);

            let summary = self.summarize();

            let new_summary =
                self.replace_non_overflowing(start..end, replacement, summary);

            (new_summary, extras)
        } else if s.len() + (self.len() - end) < Self::min_bytes() {
            let truncate_from;

            let missing = Self::min_bytes() - s.len() - (self.len() - end);

            let (new_left, new_right) = if start <= self.len_left() {
                (&self.left_chunk()[..start], "")
            } else {
                let start = start - self.len_left();
                (self.left_chunk(), &self.right_chunk()[..start])
            };

            let (add_to_extras_1, add_to_extras_2) = if missing
                <= new_right.len()
            {
                let (keep_in_self, add_to_extras) = split_adjusted::<true>(
                    new_right,
                    new_right.len() - missing,
                );

                truncate_from = new_left.len() + keep_in_self.len();

                ("", add_to_extras)
            } else {
                let missing = missing - new_right.len();

                let (keep_in_self, add_to_extras) =
                    split_adjusted::<true>(new_left, new_left.len() - missing);

                truncate_from = keep_in_self.len();

                (add_to_extras, new_right)
            };

            let extras = ChunkResegmenter::new([
                add_to_extras_1,
                add_to_extras_2,
                s,
                extra_left,
                extra_right,
            ])
            .collect();

            let removed_line_breaks_left = self.line_breaks_left
                - self.line_breaks_left_before_offset(truncate_from);

            self.remove_from(truncate_from, removed_line_breaks_left);

            (self.summarize(), extras)
        } else {
            let extras =
                ChunkResegmenter::new([s, extra_left, extra_right]).collect();

            let removed_line_breaks_left = self.line_breaks_left
                - self.line_breaks_left_before_offset(start);

            self.remove_from(start, removed_line_breaks_left);

            (self.summarize(), extras)
        }
    }

    /// TODO: docs
    #[inline]
    fn right_chunk(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the bytes in
        // the second segment as valid UTF-8.
        unsafe {
            std::str::from_utf8_unchecked(
                &self.bytes[MAX_BYTES - self.len_right()..],
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
    ///
    /// TODO: examples
    #[inline]
    fn summarize_range(
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

        #[inline(always)]
        fn summarize_range<const MAX_BYTES: usize>(
            buffer: &GapBuffer<MAX_BYTES>,
            start: usize,
            end: usize,
        ) -> ChunkSummary {
            if end <= buffer.len_left() {
                let chunk = &buffer.left_chunk()[start..end];
                let line_breaks_left_chunk = count_line_breaks(chunk);

                ChunkSummary {
                    bytes: chunk.len(),
                    line_breaks: line_breaks_left_chunk,
                }
            } else if start <= buffer.len_left() {
                let end = end - buffer.len_left();

                let left_chunk = &buffer.left_chunk()[start..];
                let right_chunk = &buffer.right_chunk()[..end];

                let line_breaks_left_chunk = count_line_breaks(left_chunk);

                ChunkSummary {
                    bytes: left_chunk.len() + right_chunk.len(),
                    line_breaks: line_breaks_left_chunk
                        + count_line_breaks(right_chunk),
                }
            } else {
                let start = start - buffer.len_left();
                let end = end - buffer.len_left();

                let chunk = &buffer.right_chunk()[start..end];
                let line_breaks = count_line_breaks(chunk);

                ChunkSummary { bytes: chunk.len(), line_breaks }
            }
        }

        // Get the summary by directly summarizing the byte range.
        if end - start <= self.len() / 2 {
            summarize_range(self, start, end)
        }
        // Get the summary by subtracting the opposite byte ranges from the
        // total.
        else {
            total
                - summarize_range(self, 0, start)
                - summarize_range(self, end, MAX_BYTES)
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
    fn from_str(s: &str) -> Self {
        Self { bytes: s.len(), line_breaks: count_line_breaks(s) }
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
        let mut bytes = Box::new([0u8; MAX_BYTES]);

        bytes[..slice.len_left()]
            .copy_from_slice(slice.left_chunk().as_bytes());

        bytes[MAX_BYTES - slice.len_right()..]
            .copy_from_slice(slice.last_chunk().as_bytes());

        Self {
            bytes,
            len_left: slice.len_left,
            line_breaks_left: slice.line_breaks_left,
            len_right: slice.len_right,
        }
    }
}

impl<const MAX_BYTES: usize> AsSlice for GapBuffer<MAX_BYTES> {
    type Slice<'a> = GapSlice<'a>;

    #[inline]
    fn as_slice(&self) -> GapSlice<'_> {
        let bytes = match (self.len_left() > 0, self.len_right() > 0) {
            (true, true) => &*self.bytes,
            (true, false) => &self.bytes[..self.len_left()],
            (false, true) => &self.bytes[MAX_BYTES - self.len_right()..],
            (false, false) => &[],
        };

        GapSlice {
            bytes,
            len_left: self.len_left,
            line_breaks_left: self.line_breaks_left,
            len_right: self.len_right,
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
            left.append_other(left_summary.line_breaks, right);
            *left_summary += *right_summary;
            *right_summary = ChunkSummary::empty();

            debug_assert!(left.len() >= Self::chunk_min());
            debug_assert!(right.is_empty());
        }
        // The left side is underfilled => take text from the right side.
        else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing_left = Self::min_bytes() - left.len();
            let moved_left = left.add_text_from_right(missing_left, right);
            *left_summary += moved_left;
            *right_summary -= moved_left;

            debug_assert!(left.len() >= Self::chunk_min());
            debug_assert!(right.len() >= Self::chunk_min());
        }
        // The right side is underfilled => take text from the left side.
        else if right.len() < Self::min_bytes() {
            debug_assert!(left.len() > Self::min_bytes());

            let missing_right = Self::min_bytes() - right.len();
            let moved_right = left.move_text_to_right(missing_right, right);
            *left_summary -= moved_right;
            *right_summary += moved_right;

            debug_assert!(left.len() >= Self::chunk_min());
            debug_assert!(right.len() >= Self::chunk_min());
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
            let combined = Self::from_chunks(&[
                left.left_chunk(),
                left.last_chunk(),
                right.left_chunk(),
                right.last_chunk(),
            ]);

            ((combined, left_summary + right_summary), None)
        }
        // The left side is underfilled -> take text from the right side.
        else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());

            let missing = Self::min_bytes() - left.len();

            if right.len_left() >= missing {
                let (to_left, keep_right) =
                    split_adjusted::<true>(right.left_chunk(), missing);

                let left = Self::from_chunks(&[
                    left.left_chunk(),
                    left.last_chunk(),
                    to_left,
                ]);

                let right =
                    Self::from_chunks(&[keep_right, right.last_chunk()]);

                let to_left_summary = ChunkSummary::from_str(to_left);

                (
                    (left, left_summary + to_left_summary),
                    Some((right, right_summary - to_left_summary)),
                )
            } else {
                let missing = missing - right.len_left();

                let (to_left, keep_right) =
                    split_adjusted::<true>(right.last_chunk(), missing);

                let to_left_summary =
                    ChunkSummary::from_str(right.left_chunk())
                        + ChunkSummary::from_str(to_left);

                let left = Self::from_chunks(&[
                    left.left_chunk(),
                    left.last_chunk(),
                    right.left_chunk(),
                    to_left,
                ]);

                let right = Self::from_chunks(&[keep_right]);

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

            if left.len_right() >= missing {
                let (keep_left, to_right) = split_adjusted::<true>(
                    left.last_chunk(),
                    left.len_right() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right);

                let left = Self::from_chunks(&[left.left_chunk(), keep_left]);

                let right = Self::from_chunks(&[
                    to_right,
                    right.left_chunk(),
                    right.last_chunk(),
                ]);

                (
                    (left, left_summary - to_right_summary),
                    Some((right, right_summary + to_right_summary)),
                )
            } else {
                let missing = missing - left.len_right();

                let (keep_left, to_right) = split_adjusted::<true>(
                    left.left_chunk(),
                    left.len_left() - missing,
                );

                let to_right_summary = ChunkSummary::from_str(to_right)
                    + ChunkSummary::from_str(left.last_chunk());

                let right = Self::from_chunks(&[
                    to_right,
                    left.last_chunk(),
                    right.left_chunk(),
                    right.last_chunk(),
                ]);

                let left = Self::from_chunks(&[keep_left]);

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
        let (start, end) = range_bounds_to_start_end(range, 0, self.len());

        debug_assert!(start <= end);
        debug_assert!(end <= self.len());

        self.assert_char_boundary(start);
        self.assert_char_boundary(end);

        if self.len() - (end - start) + replacement.len() <= MAX_BYTES {
            let new_summary = if end > start {
                self.replace_non_overflowing(start..end, replacement, *summary)
            } else {
                self.insert(start, replacement, *summary)
            };

            *summary = new_summary;

            None
        } else {
            let (new_summary, extras) =
                self.replace_overflowing(start..end, replacement);

            *summary = new_summary;

            if cfg!(feature = "small_chunks") {
                (!extras.is_empty()).then_some(extras.into_iter())
            } else {
                Some(extras.into_iter())
            }
        }
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
        let remaining = self.s.len() - self.yielded;

        let chunk = if remaining == 0 {
            return None;
        } else if remaining > MAX_BYTES {
            let min = GapBuffer::<MAX_BYTES>::min_bytes();

            let chunk_len = if remaining - MAX_BYTES >= min {
                MAX_BYTES
            } else {
                // Take `chunk_len` such that `remaining - chunk_len = min`.
                remaining - min
            };

            let mut adjusted_len = adjust_split_point::<false>(
                &self.s[self.yielded..],
                chunk_len,
            );

            if adjusted_len == 0 {
                adjusted_len = adjust_split_point::<true>(
                    &self.s[self.yielded..],
                    chunk_len,
                );
            }

            &self.s[self.yielded..(self.yielded + adjusted_len)]
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
    chunks: [&'a str; CHUNKS],
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
        Self { total, chunks: segments, yielded: 0, start: 0 }
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

            for (idx, &chunk) in self.chunks[self.start..].iter().enumerate() {
                let new_bytes_in_next = bytes_in_next + chunk.len();

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

            let (mut left, mut right) =
                split_adjusted::<false>(self.chunks[idx_last], last_chunk_len);

            // This can happen with e.g. ["🌎", "!"] and MAX_BYTES = 4.
            if (self.chunks[self.start..idx_last]
                .iter()
                .map(|s| s.len())
                .sum::<usize>()
                + left.len())
                == 0
            {
                (left, right) = split_adjusted::<true>(
                    self.chunks[idx_last],
                    last_chunk_len,
                );

                self.chunks[idx_last] = left;
            } else {
                self.chunks[idx_last] = left;
            }

            let next = GapBuffer::<MAX_BYTES>::from_chunks(
                &self.chunks[self.start..=idx_last],
            );

            self.chunks[idx_last] = right;

            self.start = idx_last;

            next
        } else {
            debug_assert!(remaining >= GapBuffer::<MAX_BYTES>::chunk_min());
            GapBuffer::<MAX_BYTES>::from_chunks(&self.chunks[self.start..])
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
                && rhs.left_chunk() == &self[..rhs.len_left()]
                && rhs.right_chunk() == &self[rhs.len_left()..]
        }
    }

    // We only need this to compare `Option<GapBuffer>` with `None`.
    impl<const N: usize> PartialEq<GapBuffer<N>> for GapBuffer<N> {
        fn eq(&self, _rhs: &GapBuffer<N>) -> bool {
            unimplemented!();
        }
    }

    #[test]
    fn remove_up_to_0() {
        let mut buffer = GapBuffer::<10>::from("aaabbb");
        buffer.move_gap(2, 0);
        buffer.remove_up_to(4, 0);
        assert_eq!("bb", buffer);
    }

    #[test]
    fn chunk_segmenter_0() {
        let chunk = "Hello Earth 🌎!";
        let mut segmenter = GapBuffer::<4>::chunk_segmenter(chunk);

        assert_eq!("Hell", segmenter.next().unwrap());
        assert_eq!("o Ea", segmenter.next().unwrap());
        assert_eq!("rth ", segmenter.next().unwrap());
        assert_eq!("🌎", segmenter.next().unwrap());
        assert_eq!("!", segmenter.next().unwrap());
        assert_eq!(None, segmenter.next());
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

    #[test]
    fn chunk_resegmenter_6() {
        let chunks = [" 🌎", "!"];
        let mut resegmenter = ChunkResegmenter::<2, 4>::new(chunks);

        assert_eq!(" ", resegmenter.next().unwrap());
        assert_eq!("🌎", resegmenter.next().unwrap());
        assert_eq!("!", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }
}
