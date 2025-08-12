//! This module exports the [`GapBuffer`] struct and a few of its methods.
//!
//! It also implements several traits exported by the [tree](crate::tree)
//! module on it to be able to use it as the leaf of our [`Rope`](crate::Rope).

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::ops::{Range, RangeBounds};

use super::gap_slice::GapSlice;
use super::metrics::{ByteMetric, ChunkSummary};
use super::utils::{panic_messages as panic, *};
use crate::range_bounds_to_start_end;
use crate::tree::{
    AsSlice,
    BalancedLeaf,
    BaseMeasured,
    ReplaceableLeaf,
    Summarize,
};

/// A [gap buffer] with a max capacity of `2^16 - 1` bytes.
///
/// Unlike a regular `String` where the extra capacity is stored at the end of
/// the string, a `GapBuffer` stores the extra capacity in the middle of the
/// heap-allocated buffer.
///
/// This allows us to efficiently perform consecutive insertions and deletions
/// at the same cursor position in O(1) time in the size of the buffer, unlike
/// a regular `String` where we would have to shift the contents to the right
/// or left, respectively, resulting in O(n) time.
///
/// Only the first `len_left` and the last `len_right` bytes of the buffer are
/// valid. The gap is located between the two chunks and has a length of
/// `len_gap() = MAX_BYTES - len_left - len_right`.
///
/// [gap buffer]: https://en.wikipedia.org/wiki/Gap_buffer
#[derive(Clone)]
pub struct GapBuffer<const MAX_BYTES: usize> {
    pub(super) bytes: Box<[u8; MAX_BYTES]>,
    pub(super) left_summary: ChunkSummary,
    pub(super) right_summary: ChunkSummary,
}

impl<const MAX_BYTES: usize> core::fmt::Debug for GapBuffer<MAX_BYTES> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
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
            left_summary: ChunkSummary::default(),
            right_summary: ChunkSummary::default(),
        }
    }
}

// We only need this to compare `GapBuffer`s with `&str`s in (doc)tests.
impl<const N: usize> PartialEq<GapBuffer<N>> for &str {
    fn eq(&self, rhs: &GapBuffer<N>) -> bool {
        *self == rhs.as_slice()
    }
}

impl<const N: usize> PartialEq<&str> for GapBuffer<N> {
    fn eq(&self, rhs: &&str) -> bool {
        rhs == self
    }
}

// We only need this to compare `Option<GapBuffer>` with `None` in (doc)tests.
impl<const N: usize> PartialEq<GapBuffer<N>> for GapBuffer<N> {
    fn eq(&self, _rhs: &GapBuffer<N>) -> bool {
        unimplemented!();
    }
}

impl<const MAX_BYTES: usize> From<&str> for GapBuffer<MAX_BYTES> {
    /// # Panics
    ///
    /// Panics if the string's byte length is greater than `MAX_BYTES`.
    #[inline]
    fn from(s: &str) -> Self {
        debug_assert!(s.len() <= MAX_BYTES);
        Self::from_chunks(&[s])
    }
}

impl<const MAX_BYTES: usize> GapBuffer<MAX_BYTES> {
    /// Moves `bytes_to_add` bytes from the start of the right buffer to the
    /// end of this buffer, returning the summary of what's been added to this
    /// buffer.
    ///
    /// Note that it can move fewer bytes if that offset is not a char boundary
    /// of the right buffer.
    ///
    /// # Panics
    ///
    /// Panics if `bytes_to_add` is out of bounds in the right buffer or if the
    /// resulting left buffer would have a length greater than `MAX_BYTES`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// let mut left = GapBuffer::<10>::from("Hello");
    /// let mut right = GapBuffer::<10>::from(", World!");
    ///
    /// left.add_from_right(2, &mut right);
    /// assert_eq!(left, "Hello, ");
    /// assert_eq!(right, "World!");
    /// ```
    #[inline]
    pub fn add_from_right(
        &mut self,
        bytes_to_add: usize,
        right: &mut Self,
    ) -> ChunkSummary {
        debug_assert!(right.len() >= bytes_to_add);
        debug_assert!(self.len() + bytes_to_add <= MAX_BYTES);

        if bytes_to_add <= right.len_left() {
            let (move_left, _) =
                split_adjusted::<false>(right.left_chunk(), bytes_to_add);

            let summary = right.summarize_left_chunk_up_to(move_left.len());

            self.append_str(move_left, summary);

            right.remove_up_to(move_left.len(), summary);

            summary
        } else {
            let (move_left, _) = split_adjusted::<false>(
                right.right_chunk(),
                bytes_to_add - right.len_left(),
            );

            let summary = right.left_summary + ChunkSummary::from(move_left);

            self.append_two(right.left_chunk(), move_left, summary);

            right.remove_up_to(summary.bytes(), summary);

            summary
        }
    }

    /// Moves all the bytes from the right buffer to the end of this buffer,
    /// leaving the right buffer empty.
    ///
    /// # Panics
    ///
    /// Panics if the resulting left buffer would have a length greater than
    /// `MAX_BYTES`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// # use crop::tree::Summarize;
    /// let mut left = GapBuffer::<15>::from("Hello");
    ///
    /// let mut right = GapBuffer::<15>::from(", World!");
    ///
    /// left.append_other(&mut right);
    ///
    /// assert_eq!(left, "Hello, World!");
    ///
    /// assert_eq!(right, "");
    /// ```
    #[inline]
    pub fn append_other(&mut self, other: &mut Self) {
        let len_left = self.len_left();
        let len_right = self.len_right();

        // Move this buffer's right chunk after its left chunk.
        self.bytes.copy_within(MAX_BYTES - len_right..MAX_BYTES, len_left);

        // Move the other buffer's left chunk to this buffer's right chunk.
        let end = MAX_BYTES - other.len_right();
        self.bytes[end - other.len_left()..end]
            .copy_from_slice(other.left_chunk().as_bytes());

        // Move the other buffer's right chunk to this buffer's right chunk.
        self.bytes[end..].copy_from_slice(other.right_chunk().as_bytes());

        self.left_summary += self.right_summary;
        self.right_summary = other.left_summary + other.right_summary;

        other.left_summary = ChunkSummary::new();
        other.right_summary = ChunkSummary::new();
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
    /// # use crop::{GapBuffer, ChunkSummary};
    ///
    /// let mut buffer = GapBuffer::<10>::from("aabb");
    /// assert_eq!(buffer.left_chunk(), "aa");
    /// assert_eq!(buffer.right_chunk(), "bb");
    ///
    /// buffer.append_str("cc", ChunkSummary::from("cc"));
    /// assert_eq!(buffer.left_chunk(), "aa");
    /// assert_eq!(buffer.right_chunk(), "bbcc");
    /// ```
    #[inline]
    pub fn append_str(&mut self, str: &str, str_summary: ChunkSummary) {
        debug_assert!(str.len() <= self.len_gap());
        debug_assert_eq!(str_summary, ChunkSummary::from(str));

        let start = MAX_BYTES - self.len_right();

        // Shift the right chunk to the left.
        self.bytes.copy_within(start.., start - str.len());

        // Append the string.
        self.bytes[MAX_BYTES - str.len()..].copy_from_slice(str.as_bytes());

        self.right_summary += str_summary;
    }

    /// Exactly the same as [`append_str()`](Self::append_str()), except it
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
    /// # use crop::{GapBuffer, ChunkSummary};
    /// let mut buffer = GapBuffer::<10>::from("aabb");
    ///
    /// buffer.append_two("cc", "dd", ChunkSummary::from("ccdd"));
    /// assert_eq!(buffer.left_chunk(), "aa");
    /// assert_eq!(buffer.right_chunk(), "bbccdd");
    /// ```
    #[inline]
    pub fn append_two(&mut self, a: &str, b: &str, a_b_summary: ChunkSummary) {
        debug_assert!(a.len() + b.len() <= self.len_gap());
        debug_assert_eq!(
            a_b_summary,
            ChunkSummary::from(a) + ChunkSummary::from(b)
        );

        // Shift the right chunk to the left.
        let start = MAX_BYTES - self.len_right();
        self.bytes.copy_within(start.., start - a.len() - b.len());

        // Append the first string.
        let end = MAX_BYTES - b.len();
        self.bytes[end - a.len()..end].copy_from_slice(a.as_bytes());

        // Append the second string.
        let range = MAX_BYTES - b.len()..MAX_BYTES;
        self.bytes[range].copy_from_slice(b.as_bytes());

        self.right_summary += a_b_summary;
    }

    /// Panics with a nicely formatted error message if the given byte offset
    /// is not a character boundary.
    #[track_caller]
    #[inline]
    fn assert_char_boundary(&self, byte_offset: usize) {
        debug_assert!(byte_offset <= self.len());

        if !self.is_char_boundary(byte_offset) {
            if byte_offset < self.len_left() {
                panic::byte_offset_not_char_boundary(
                    self.left_chunk(),
                    byte_offset,
                )
            } else {
                panic::byte_offset_not_char_boundary(
                    self.right_chunk(),
                    byte_offset - self.len_left(),
                )
            }
        }
    }

    /// The number of bytes `RopeChunk`s must always stay over.
    pub(super) const fn chunk_min() -> usize {
        // The buffer can be underfilled by 3 bytes at most, which can happen
        // when a byte offset lands inside a 4 byte codepoint.
        Self::min_bytes().saturating_sub(3)
    }

    /// Creates a new `GapBuffer` from a slice of `&str`s.
    ///
    /// # Panics
    ///
    /// Panics if the combined byte length of all the chunks is greater than
    /// `MAX_BYTES`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// let buffer = GapBuffer::<10>::from_chunks(&["a", "abb", "cc", "dd"]);
    /// assert_eq!(buffer.left_chunk(), "aabb");
    /// assert_eq!(buffer.right_chunk(), "ccdd");
    /// ```
    #[inline]
    pub fn from_chunks(chunks: &[&str]) -> Self {
        let total_len = chunks.iter().map(|s| s.len()).sum::<usize>();

        if total_len == 0 {
            return Self::default();
        }

        debug_assert!(total_len <= MAX_BYTES);

        let to_left = total_len / 2;

        let mut bytes = Box::new([0u8; MAX_BYTES]);

        let mut left_summary = ChunkSummary::new();

        let mut chunks = chunks.iter();

        for &chunk in chunks.by_ref() {
            if left_summary.bytes() + chunk.len() <= to_left {
                let range = {
                    let start = left_summary.bytes();
                    let end = start + chunk.len();
                    start..end
                };

                bytes[range].copy_from_slice(chunk.as_bytes());

                left_summary += ChunkSummary::from(chunk);
            } else {
                let (to_first, to_second) = split_adjusted::<true>(
                    chunk,
                    to_left - left_summary.bytes(),
                );

                let range = {
                    let start = left_summary.bytes();
                    let end = start + to_first.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_first.as_bytes());

                left_summary += ChunkSummary::from(to_first);

                let mut start = MAX_BYTES - (total_len - left_summary.bytes());

                let range = {
                    let end = start + to_second.len();
                    start..end
                };

                bytes[range].copy_from_slice(to_second.as_bytes());

                start += to_second.len();

                let mut right_summary = ChunkSummary::from(to_second);

                for &segment in chunks {
                    let range = {
                        let end = start + segment.len();
                        start..end
                    };

                    bytes[range].copy_from_slice(segment.as_bytes());

                    start += segment.len();

                    right_summary += ChunkSummary::from(segment);
                }

                return Self { bytes, left_summary, right_summary };
            }
        }

        unreachable!("This can only be reached if the total length is zero");
    }

    /// Returns `true` if the buffer ends with a newline ('\n') character.
    #[inline]
    pub(super) fn has_trailing_newline(&self) -> bool {
        self.last_chunk().ends_with('\n')
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

        self.move_gap(insert_at);

        debug_assert_eq!(insert_at, self.len_left());

        let insert_range = {
            let start = self.len_left();
            let end = start + s.len();
            start..end
        };

        self.bytes[insert_range].copy_from_slice(s.as_bytes());

        let inserted_summary = ChunkSummary::from(s);

        self.left_summary += inserted_summary;
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

    /// Returns `true` if the buffer is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The right chunk if it's not empty, or the left one otherwise.
    #[inline]
    pub(super) fn last_chunk(&self) -> &str {
        if self.len_right() == 0 {
            self.left_chunk()
        } else {
            self.right_chunk()
        }
    }

    /// Returns the left chunk of this buffer as a string slice.
    #[inline]
    pub fn left_chunk(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the first
        // `len_left()` bytes valid UTF-8.
        unsafe {
            core::str::from_utf8_unchecked(&self.bytes[..self.len_left()])
        }
    }

    /// Returns the combined byte length of the buffer's left and right chunks.
    #[inline]
    pub fn len(&self) -> usize {
        self.len_left() + self.len_right()
    }

    #[inline]
    pub(super) fn len_left(&self) -> usize {
        self.left_summary.bytes()
    }

    #[inline]
    fn len_gap(&self) -> usize {
        MAX_BYTES - self.len_left() - self.len_right()
    }

    #[inline]
    pub(super) fn len_right(&self) -> usize {
        self.right_summary.bytes()
    }

    /// The minimum number of bytes this buffer should have to not be
    /// considered underfilled.
    pub(super) const fn min_bytes() -> usize {
        MAX_BYTES / 4
    }

    /// Moves the gap to the given byte offset.
    ///
    /// # Panics
    ///
    /// Panics if the byte offset is out of bounds or if it's not a char
    /// boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// # use crop::tree::Summarize;
    /// let mut buffer = GapBuffer::<10>::from("aaaabbbb");
    ///
    /// buffer.move_gap(2);
    /// assert_eq!(buffer.left_chunk(), "aa");
    /// assert_eq!(buffer.right_chunk(), "aabbbb");
    ///
    /// buffer.move_gap(6);
    /// assert_eq!(buffer.left_chunk(), "aaaabb");
    /// assert_eq!(buffer.right_chunk(), "bb");
    /// ```
    #[inline]
    pub fn move_gap(&mut self, byte_offset: usize) {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));

        let offset = byte_offset;

        #[allow(clippy::comparison_chain)]
        // The offset splits the first segment => move all the text after the
        // offset to the start of the second segment.
        //
        // aa|bb~~~ccc => aa~~~bbccc
        if offset < self.len_left() {
            let orig_left_summary = self.left_summary;
            self.left_summary = self.summarize_left_chunk_up_to(offset);
            self.right_summary += orig_left_summary - self.left_summary;

            let len_right = self.len_right();
            self.bytes.copy_within(
                offset..orig_left_summary.bytes(),
                MAX_BYTES - len_right,
            );
        }
        // The offset splits the second segment => move all the text before the
        // offset to the end of the first segment.
        //
        // aaa~~~bb|cc => aaabb~~~cc
        else if offset > self.len_left() {
            let len_moved = offset - self.len_left();

            let moved_summary = self.summarize_right_chunk_up_to(len_moved);

            let move_range = {
                let start = MAX_BYTES - self.len_right();
                let end = start + len_moved;
                start..end
            };

            let len_left = self.len_left();
            self.bytes.copy_within(move_range, len_left);

            self.left_summary += moved_summary;
            self.right_summary -= moved_summary;
        }

        debug_assert_eq!(offset, self.len_left());
    }

    /// Moves the last `bytes_to_move` bytes of this buffer to the right
    /// buffer.
    ///
    /// Note that it can move less than `bytes_to_move` bytes if that offset is
    /// not a char boundary of this buffer.
    ///
    /// # Panics
    ///
    /// Panics if `bytes_to_move` is out of bounds or if the resulting right
    /// buffer would have a length greater than `MAX_BYTES`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// # use crop::tree::Summarize;
    /// let mut left = GapBuffer::<10>::from("Hello, ");
    ///
    /// let mut right = GapBuffer::<10>::from("World!");
    ///
    /// left.move_to_right(2, &mut right);
    ///
    /// assert_eq!(left, "Hello");
    ///
    /// assert_eq!(right, ", World!");
    /// ```
    #[inline]
    pub fn move_to_right(&mut self, bytes_to_move: usize, right: &mut Self) {
        debug_assert!(bytes_to_move <= self.len());
        debug_assert!(right.len() + bytes_to_move <= MAX_BYTES);

        if bytes_to_move <= self.len_right() {
            let (_, move_right) = split_adjusted::<true>(
                self.right_chunk(),
                self.len_right() - bytes_to_move,
            );

            let moved_summary = ChunkSummary::from(move_right);

            right.prepend(move_right, moved_summary);

            self.truncate_from(self.len() - move_right.len());
        } else {
            let (_, move_right) = split_adjusted::<true>(
                self.left_chunk(),
                self.len_left() - (bytes_to_move - self.len_right()),
            );

            let move_right_summary = ChunkSummary::from(move_right);

            let moved_summary = move_right_summary + self.right_summary;

            right.prepend_two(move_right, self.right_chunk(), moved_summary);

            self.truncate_from(self.len_left() - move_right.len());
        }
    }

    /// Prepends a string to this buffer.
    ///
    /// # Panics
    ///
    /// Panics if the resulting buffer would have a length greater than
    /// `MAX_BYTES`, or if the given summary differs from the string's
    /// `ChunkSummary`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::{ChunkSummary, GapBuffer};
    /// let mut buf = GapBuffer::<15>::from("World!");
    ///
    /// let prepend = "Hello, ";
    ///
    /// let prepended_summary = ChunkSummary::from(prepend);
    ///
    /// buf.prepend(prepend, prepended_summary);
    ///
    /// assert_eq!(buf, "Hello, World!");
    /// ```
    #[inline]
    pub fn prepend(&mut self, str: &str, str_summary: ChunkSummary) {
        debug_assert!(str.len() <= self.len_gap());
        debug_assert_eq!(str_summary, ChunkSummary::from(str));

        // Shift the left chunk over.
        let len_left = self.len_left();
        self.bytes.copy_within(..len_left, str.len());

        // Prepend the string.
        self.bytes[..str.len()].copy_from_slice(str.as_bytes());

        self.left_summary += str_summary;
    }

    /// Exactly the same as [`prepend`](Self::prepend()), except it
    /// prepends two strings instead of one.
    ///
    /// # Panics
    ///
    /// Panics if the combined byte length of the two strings is greater that
    /// the length of the gap.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::{ChunkSummary, GapBuffer};
    /// let mut buf = GapBuffer::<15>::from("!");
    ///
    /// let hello = "Hello, ";
    ///
    /// let world = "World";
    ///
    /// let prepended_summary =
    ///     ChunkSummary::from(hello) + ChunkSummary::from(world);
    ///
    /// buf.prepend_two(hello, world, prepended_summary);
    ///
    /// assert_eq!(buf, "Hello, World!");
    /// ```
    #[inline]
    pub fn prepend_two(
        &mut self,
        a: &str,
        b: &str,
        prepended_summary: ChunkSummary,
    ) {
        debug_assert!(a.len() + b.len() <= self.len_gap());

        debug_assert_eq!(
            prepended_summary,
            ChunkSummary::from(a) + ChunkSummary::from(b)
        );

        // Shift the first segment to the right.
        let len_first = self.len_left();
        self.bytes.copy_within(..len_first, a.len() + b.len());

        // Prepend the first string.
        self.bytes[..a.len()].copy_from_slice(a.as_bytes());

        // Prepend the second string.
        self.bytes[a.len()..a.len() + b.len()].copy_from_slice(b.as_bytes());

        self.left_summary += prepended_summary;
    }

    /// Removes the first `byte_offset` bytes from this buffer.
    ///
    /// # Panics
    ///
    /// Panics if `byte_offset` is out of bounds, if it's not a char boundary
    /// or if the number of line breaks in the range `0..byte_offset` is not
    /// equal to `removed_line_breaks`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::{ChunkSummary, GapBuffer};
    /// let mut buffer = GapBuffer::<10>::from("foo\nbar");
    ///
    /// let removed_summary = ChunkSummary::from("foo\n");
    ///
    /// buffer.remove_up_to(4, removed_summary);
    ///
    /// assert_eq!(buffer, "bar");
    /// ```
    #[inline]
    pub fn remove_up_to(
        &mut self,
        byte_offset: usize,
        removed_summary: ChunkSummary,
    ) {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));
        debug_assert_eq!(
            self.summarize_range(0..byte_offset),
            removed_summary
        );

        if byte_offset <= self.len_left() {
            let len_kept = self.len_left() - byte_offset;

            let range = {
                let len_left = self.len_left();
                len_left - len_kept..len_left
            };

            self.bytes.copy_within(range, 0);

            self.left_summary -= removed_summary;
        } else {
            self.right_summary -= removed_summary - self.left_summary;
            self.left_summary = ChunkSummary::new();
        }
    }

    /// Replaces the text in `byte_range` with the string `s`, where the
    /// replaced range is big enough (and the replacement string is small
    /// enough) such that the buffer doesn't go over `MAX_BYTES`.
    ///
    /// # Panics
    ///
    /// Panics if the end of the byte range is out of bounds, if either the
    /// start or the end of the byte range is not a char boundary, if the
    /// length of the buffer after the replacement would be greater than
    /// `MAX_BYTES` or if `summary` is not equal to this buffer's summary.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// # use crop::tree::Summarize;
    /// let mut buffer = GapBuffer::<10>::from("foo\nbar");
    /// buffer.replace_non_overflowing(4..7, "baz\r\n");
    /// assert_eq!(buffer, "foo\nbaz\r\n");
    /// ```
    #[inline]
    pub fn replace_non_overflowing(
        &mut self,
        Range { start, end }: Range<usize>,
        s: &str,
    ) {
        debug_assert!(start <= end);
        debug_assert!(end <= self.len());
        debug_assert!(self.is_char_boundary(start));
        debug_assert!(self.is_char_boundary(end));
        debug_assert!(self.len() - (end - start) + s.len() <= MAX_BYTES);

        self.move_gap(end);

        let removed_summary = self.summarize_range(start..end);

        let added_summary = ChunkSummary::from(s);

        self.bytes[start..start + s.len()].copy_from_slice(s.as_bytes());

        self.left_summary -= removed_summary;

        self.left_summary += added_summary;
    }

    /// Replaces the text in `byte_range` with the string `s`, where the
    /// replaced range is small enough (and the replacement string is big
    /// enough) such that the buffer goes over `MAX_BYTES`.
    ///
    /// It returns a vector of buffers containing the overflowed contents, all
    /// of which are guaranteed to not be underfilled.
    ///
    /// # Panics
    ///
    /// Panics if the end of the byte range is out of bounds, if either the
    /// start or the end of the byte range is not a char boundary, or if the
    /// length of the buffer after the replacement would be less than or equal
    /// to `MAX_BYTES`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// # use crop::tree::Summarize;
    /// let mut buffer = GapBuffer::<10>::from("foo\nbar");
    ///
    /// // Replace the newline with a string that's too long to fit in the
    /// // buffer.
    /// let extras = buffer.replace_overflowing(3..4, "foo\nbar\r\nbaz");
    ///
    /// assert_eq!(buffer, "foo");
    ///
    /// let mut extras = extras.into_iter();
    /// assert_eq!("foo\nbar\r\nb", extras.next().unwrap());
    /// assert_eq!("azbar", extras.next().unwrap());
    /// assert_eq!(None, extras.next());
    /// ```
    #[inline]
    pub fn replace_overflowing(
        &mut self,
        byte_range: Range<usize>,
        s: &str,
    ) -> Vec<Self> {
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

                Resegmenter::new([right, extra_left, extra_right]).collect()
            } else if s.len() + extra_left.len() >= missing {
                let missing = missing - s.len();

                let (left, right) =
                    split_adjusted::<true>(extra_left, missing);

                truncate_from += left.len();

                Resegmenter::new([right, extra_right]).collect()
            } else {
                let missing = missing - s.len() - extra_left.len();

                let (left, right) =
                    split_adjusted::<true>(extra_right, missing);

                truncate_from += extra_left.len() + left.len();

                Resegmenter::new([right]).collect()
            };

            self.truncate_from(truncate_from);

            self.replace_non_overflowing(start..end, replacement);

            extras
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

            let extras = Resegmenter::new([
                add_to_extras_1,
                add_to_extras_2,
                s,
                extra_left,
                extra_right,
            ])
            .collect();

            self.truncate_from(truncate_from);

            extras
        } else {
            let extras =
                Resegmenter::new([s, extra_left, extra_right]).collect();

            self.truncate_from(start);

            extras
        }
    }

    /// Returns the right chunk of this buffer as a string slice.
    #[inline]
    pub fn right_chunk(&self) -> &str {
        // SAFETY: all the methods are guaranteed to always keep the last
        // `len_right()` bytes valid UTF-8.
        unsafe {
            core::str::from_utf8_unchecked(
                &self.bytes[MAX_BYTES - self.len_right()..],
            )
        }
    }

    #[inline]
    pub(super) fn segmenter(s: &str) -> Segmenter<'_, MAX_BYTES> {
        Segmenter { s, yielded: 0 }
    }

    /// Returns the summary of the left chunk up to the given byte offset.
    #[inline]
    fn summarize_left_chunk_up_to(&self, byte_offset: usize) -> ChunkSummary {
        debug_assert!(byte_offset <= self.len_left());
        debug_assert!(self.left_chunk().is_char_boundary(byte_offset));

        if byte_offset <= self.len_left() / 2 {
            ChunkSummary::from(&self.left_chunk()[..byte_offset])
        } else {
            self.left_summary
                - ChunkSummary::from(&self.left_chunk()[byte_offset..])
        }
    }

    /// Returns the summary obtained by summarizing only the text in the given
    /// byte range.
    ///
    /// # Panics
    ///
    /// Panics if either the start or the end of the byte range don't lie on a
    /// char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::GapBuffer;
    /// # use crop::tree::Summarize;
    /// let mut buffer = GapBuffer::<10>::from("foo\nbar\r\n");
    /// assert_eq!(buffer.summarize_range(0..buffer.len()), buffer.summarize());
    ///
    /// let s = buffer.summarize_range(0..4);
    /// assert_eq!(s.bytes(), 4);
    /// assert_eq!(s.line_breaks(), 1);
    ///
    /// let s = buffer.summarize_range(2..buffer.len());
    /// assert_eq!(s.bytes(), 7);
    /// assert_eq!(s.line_breaks(), 2);
    /// ```
    #[inline]
    pub fn summarize_range(
        &self,
        Range { start, end }: Range<usize>,
    ) -> ChunkSummary {
        debug_assert!(start <= end);
        debug_assert!(end <= self.len());
        debug_assert!(self.is_char_boundary(start));
        debug_assert!(self.is_char_boundary(end));

        #[inline(always)]
        fn summarize_range<const MAX_BYTES: usize>(
            buffer: &GapBuffer<MAX_BYTES>,
            mut start: usize,
            mut end: usize,
        ) -> ChunkSummary {
            // The whole range is inside the left chunk.
            if end <= buffer.len_left() {
                let chunk = &buffer.left_chunk()[start..end];
                ChunkSummary::from(chunk)
            }
            // The start is on the left chunk and the end is on the right.
            else if start <= buffer.len_left() {
                let left_chunk = &buffer.left_chunk()[start..];

                ChunkSummary::from(left_chunk)
                    + buffer
                        .summarize_right_chunk_up_to(end - buffer.len_left())
            }
            // The whole range is inside the right chunk.
            else {
                start -= buffer.len_left();
                end -= buffer.len_left();
                let chunk = &buffer.right_chunk()[start..end];
                ChunkSummary::from(chunk)
            }
        }

        // Get the summary by directly summarizing the byte range.
        if end - start <= self.len() / 2 {
            summarize_range(self, start, end)
        }
        // Get the summary by subtracting the remaining byte ranges from the
        // total.
        else {
            self.left_summary + self.right_summary
                - summarize_range(self, 0, start)
                - summarize_range(self, end, self.len())
        }
    }

    /// Computes and returns the summary of the right chunk.
    #[inline]
    fn summarize_right_chunk(&self) -> ChunkSummary {
        ChunkSummary::from(self.right_chunk())
    }

    /// Returns the summary of the right chunk up to the given byte offset.
    ///
    /// Note that the offset is only relative to the right chunk, not to the
    /// whole gap buffer.
    #[inline]
    fn summarize_right_chunk_up_to(&self, byte_offset: usize) -> ChunkSummary {
        debug_assert!(byte_offset <= self.len_right());
        debug_assert!(self.right_chunk().is_char_boundary(byte_offset));

        if byte_offset <= self.len_right() / 2 {
            ChunkSummary::from(&self.right_chunk()[..byte_offset])
        } else {
            self.right_summary
                - ChunkSummary::from(&self.right_chunk()[byte_offset..])
        }
    }

    /// # Panics
    ///
    /// Panics if `byte_offset` is greater than the length of this buffer or if
    /// it doesn't lie on a char boundary.
    #[inline]
    pub fn truncate_from(&mut self, byte_offset: usize) {
        debug_assert!(byte_offset <= self.len());
        debug_assert!(self.is_char_boundary(byte_offset));

        if byte_offset <= self.len_left() {
            self.left_summary = self.summarize_left_chunk_up_to(byte_offset);
            self.right_summary = ChunkSummary::new();
        } else {
            let offset = byte_offset - self.len_left();

            let new_right_summary = self.summarize_right_chunk_up_to(offset);

            let range = {
                let start = MAX_BYTES - self.len_right();
                let end = start + offset;
                start..end
            };

            self.bytes.copy_within(range, MAX_BYTES - offset);

            self.right_summary = new_right_summary;
        }
    }
}

impl<const MAX_BYTES: usize> Summarize for GapBuffer<MAX_BYTES> {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        self.left_summary + self.summarize_right_chunk()
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
            .copy_from_slice(slice.right_chunk().as_bytes());

        Self {
            bytes,
            left_summary: slice.left_summary,
            right_summary: slice.right_summary,
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
            left_summary: self.left_summary,
            right_summary: self.right_summary,
        }
    }
}

impl<const MAX_BYTES: usize> BalancedLeaf for GapBuffer<MAX_BYTES> {
    #[inline]
    fn is_underfilled(&self, summary: &ChunkSummary) -> bool {
        summary.bytes() < Self::min_bytes()
    }

    #[inline]
    fn balance_leaves(
        (left, left_summary): (&mut Self, &mut ChunkSummary),
        (right, right_summary): (&mut Self, &mut ChunkSummary),
    ) {
        // The two leaves can be combined in a single chunk.
        if left.len() + right.len() <= MAX_BYTES {
            left.append_other(right);
            debug_assert!(right.is_empty());
        }
        // The left side is underfilled => take text from the right side.
        else if left.len() < Self::min_bytes() {
            debug_assert!(right.len() > Self::min_bytes());
            let missing_left = Self::min_bytes() - left.len();
            left.add_from_right(missing_left, right);
            debug_assert!(left.len() >= Self::chunk_min());
            debug_assert!(right.len() >= Self::chunk_min());
        }
        // The right side is underfilled => take text from the left side.
        else if right.len() < Self::min_bytes() {
            debug_assert!(left.len() > Self::min_bytes());
            let missing_right = Self::min_bytes() - right.len();
            left.move_to_right(missing_right, right);
            debug_assert!(left.len() >= Self::chunk_min());
            debug_assert!(right.len() >= Self::chunk_min());
        }

        *left_summary = left.summarize();
        *right_summary = right.summarize();
    }
}

impl<const MAX_BYTES: usize> ReplaceableLeaf<ByteMetric>
    for GapBuffer<MAX_BYTES>
{
    type Replacement<'a> = &'a str;

    type ExtraLeaves = alloc::vec::IntoIter<Self>;

    #[track_caller]
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

        let extras =
            if self.len() - (end - start) + replacement.len() <= MAX_BYTES {
                if end > start {
                    self.replace_non_overflowing(start..end, replacement)
                } else {
                    self.insert(start, replacement)
                };

                None
            } else {
                let extras = self.replace_overflowing(start..end, replacement);

                if cfg!(feature = "small_chunks") {
                    (!extras.is_empty()).then_some(extras.into_iter())
                } else {
                    Some(extras.into_iter())
                }
            };

        *summary = self.summarize();

        extras
    }

    #[track_caller]
    #[inline]
    fn remove_up_to(&mut self, summary: &mut ChunkSummary, up_to: ByteMetric) {
        self.replace(summary, ..up_to, "");
    }
}

/// Segments a string into [`GapBuffer`]s with at least
/// [`GapBuffer::chunk_min()`] bytes.
///
/// The only exception is if the string is shorter than
/// [`GapBuffer::chunk_min()`], in which case this will only yield a single gap
/// buffer with the entire string.
pub(super) struct Segmenter<'a, const MAX_BYTES: usize> {
    s: &'a str,
    yielded: usize,
}

impl<'a, const MAX_BYTES: usize> Iterator for Segmenter<'a, MAX_BYTES> {
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

/// Resegments a bunch of strings.
///
/// The yielded [`GapBuffer`]s should be equal to the ones yielded by the
/// [`Segmenter`] iterator initialized with a string that is the concatenation
/// of the strings passed to this iterator.
pub(super) struct Resegmenter<'a, const CHUNKS: usize, const MAX_BYTES: usize>
{
    segments: [&'a str; CHUNKS],
    start: usize,
    yielded: usize,
    total: usize,
}

impl<'a, const CHUNKS: usize, const MAX_BYTES: usize>
    Resegmenter<'a, CHUNKS, MAX_BYTES>
{
    #[inline]
    fn new(segments: [&'a str; CHUNKS]) -> Self {
        let total = segments.iter().map(|s| s.len()).sum::<usize>();
        debug_assert!(total >= GapBuffer::<MAX_BYTES>::chunk_min());
        Self { total, segments, yielded: 0, start: 0 }
    }
}

impl<const CHUNKS: usize, const MAX_BYTES: usize> Iterator
    for Resegmenter<'_, CHUNKS, MAX_BYTES>
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

            let mut last_segment_len = MAX_BYTES - bytes_in_next;

            // new remaining = remaining - bytes_in_next - last_chunk_len
            if remaining - bytes_in_next < last_segment_len + min_bytes {
                last_segment_len = remaining - bytes_in_next - min_bytes
            }

            let (mut left, mut right) = split_adjusted::<false>(
                self.segments[idx_last],
                last_segment_len,
            );

            // This can happen with e.g. ["🌎", "!"], MAX_BYTES = 4 and
            // `min = max / 2`.
            if (self.segments[self.start..idx_last]
                .iter()
                .map(|s| s.len())
                .sum::<usize>()
                + left.len())
                == 0
            {
                (left, right) = split_adjusted::<true>(
                    self.segments[idx_last],
                    last_segment_len,
                );

                self.segments[idx_last] = left;
            } else {
                self.segments[idx_last] = left;
            }

            let next = GapBuffer::<MAX_BYTES>::from_chunks(
                &self.segments[self.start..=idx_last],
            );

            self.segments[idx_last] = right;

            self.start = idx_last;

            next
        } else {
            debug_assert!(remaining >= GapBuffer::<MAX_BYTES>::chunk_min());
            GapBuffer::<MAX_BYTES>::from_chunks(&self.segments[self.start..])
        };

        debug_assert!(next.len() >= GapBuffer::<MAX_BYTES>::chunk_min());

        self.yielded += next.len();

        Some(next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remove_up_to_0() {
        let s = "aaabbb";
        let mut buffer = GapBuffer::<10>::from(s);

        buffer.move_gap(2);

        let offset = 4;
        buffer.remove_up_to(offset, ChunkSummary::from(&s[..offset]));

        assert_eq!("bb", buffer);
    }

    #[test]
    fn segmenter_0() {
        let chunk = "Hello Earth 🌎!";
        let mut segmenter = GapBuffer::<4>::segmenter(chunk);

        assert_eq!("Hell", segmenter.next().unwrap());
        assert_eq!("o Ea", segmenter.next().unwrap());
        assert_eq!("rth ", segmenter.next().unwrap());
        assert_eq!("🌎", segmenter.next().unwrap());
        assert_eq!("!", segmenter.next().unwrap());
        assert_eq!(None, segmenter.next());
    }

    #[test]
    fn resegmenter_0() {
        let segments = ["aaaa", "b"];
        let mut resegmenter = Resegmenter::<2, 4>::new(segments);

        assert_eq!("aaaa", resegmenter.next().unwrap());
        assert_eq!("b", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn resegmenter_1() {
        let segments = ["a", "a", "bcdefgh"];
        let mut resegmenter = Resegmenter::<3, 4>::new(segments);

        assert_eq!("aabc", resegmenter.next().unwrap());
        assert_eq!("defg", resegmenter.next().unwrap());
        assert_eq!("h", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn resegmenter_2() {
        let segments = ["a", "abcdefgh", "b"];
        let mut resegmenter = Resegmenter::<3, 4>::new(segments);

        assert_eq!("aabc", resegmenter.next().unwrap());
        assert_eq!("defg", resegmenter.next().unwrap());
        assert_eq!("hb", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn resegmenter_3() {
        let segments = ["a", "b"];
        let mut resegmenter = Resegmenter::<2, 4>::new(segments);

        assert_eq!("ab", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn resegmenter_4() {
        let segments = ["a", "b", ""];
        let mut resegmenter = Resegmenter::<3, 4>::new(segments);

        assert_eq!("ab", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn resegmenter_5() {
        let segments = ["こんい"];
        let mut resegmenter = Resegmenter::<1, 4>::new(segments);

        assert_eq!("こ", resegmenter.next().unwrap());
        assert_eq!("ん", resegmenter.next().unwrap());
        assert_eq!("い", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }

    #[test]
    fn resegmenter_6() {
        let segments = [" 🌎", "!"];
        let mut resegmenter = Resegmenter::<2, 4>::new(segments);

        assert_eq!(" ", resegmenter.next().unwrap());
        assert_eq!("🌎", resegmenter.next().unwrap());
        assert_eq!("!", resegmenter.next().unwrap());
        assert_eq!(None, resegmenter.next());
    }
}
