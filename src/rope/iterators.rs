use super::metrics::{LineMetric, RawLineMetric};
use super::rope_chunk::RopeChunk;
use super::{Rope, RopeSlice};
use crate::tree::{Leaves, Units};

/// An iterator over the `&str` chunks of `Rope`s and `RopeSlice`s.
///
/// This struct is created by the `chunks` method on [`Rope`](Rope::chunks())
/// and [`RopeSlice`](RopeSlice::chunks()). See their documentation for more.
#[derive(Clone)]
pub struct Chunks<'a> {
    leaves: Leaves<'a, { Rope::fanout() }, RopeChunk>,
}

impl<'a> From<&'a Rope> for Chunks<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        let mut leaves = rope.tree.leaves();
        if rope.byte_len() == 0 {
            let _ = leaves.next();
        }
        Self { leaves }
    }
}

impl<'a> From<&RopeSlice<'a>> for Chunks<'a> {
    #[inline]
    fn from(slice: &RopeSlice<'a>) -> Self {
        let mut leaves = slice.tree_slice.leaves();
        if slice.byte_len() == 0 {
            let _ = leaves.next();
        }
        Self { leaves }
    }
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.leaves.next().map(std::ops::Deref::deref)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for Chunks<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.leaves.next_back().map(std::ops::Deref::deref)
    }
}

impl ExactSizeIterator for Chunks<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.leaves.len()
    }
}

impl std::iter::FusedIterator for Chunks<'_> {}

/// An iterator over the bytes of `Rope`s and `RopeSlice`s.
///
/// This struct is created by the `bytes` method on [`Rope`](Rope::bytes())
/// and [`RopeSlice`](RopeSlice::bytes()). See their documentation for more.
#[derive(Clone)]
pub struct Bytes<'a> {
    chunks: Chunks<'a>,

    /// The chunk used when calling [`Bytes::next()`].
    forward_chunk: &'a [u8],

    /// The number of bytes of `forward_chunk` that have already been yielded.
    forward_byte_idx: usize,

    /// The chunk used when calling [`Bytes::next_back()`].
    backward_chunk: &'a [u8],

    /// The number of bytes of `backward_chunk` which
    /// are yet to be yielded.
    backward_byte_idx: usize,

    /// The number of bytes that have been yielded so far.
    bytes_yielded: usize,

    /// The total number of bytes this iterator will yield.
    bytes_total: usize,
}

impl<'a> From<&'a Rope> for Bytes<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            forward_chunk: &[],
            forward_byte_idx: 0,
            backward_chunk: &[],
            backward_byte_idx: 0,
            bytes_yielded: 0,
            bytes_total: rope.byte_len(),
        }
    }
}

impl<'a> From<&RopeSlice<'a>> for Bytes<'a> {
    #[inline]
    fn from(slice: &RopeSlice<'a>) -> Self {
        Self {
            chunks: slice.chunks(),
            forward_chunk: &[],
            forward_byte_idx: 0,
            backward_chunk: &[],
            backward_byte_idx: 0,
            bytes_yielded: 0,
            bytes_total: slice.byte_len(),
        }
    }
}

impl Iterator for Bytes<'_> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.forward_byte_idx == self.forward_chunk.len() {
            if let Some(chunk) = self.chunks.next() {
                self.forward_chunk = chunk.as_bytes();
                self.forward_byte_idx = 0;
            } else if self.backward_byte_idx == 0 {
                return None;
            } else {
                let byte = self.backward_chunk[0];
                self.backward_chunk = &self.backward_chunk[1..];
                self.backward_byte_idx -= 1;
                self.bytes_yielded += 1;
                return Some(byte);
            }
        }

        let byte = self.forward_chunk[self.forward_byte_idx];
        self.forward_byte_idx += 1;
        self.bytes_yielded += 1;
        Some(byte)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for Bytes<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.backward_byte_idx == 0 {
            if let Some(chunk) = self.chunks.next_back() {
                self.backward_chunk = chunk.as_bytes();
                self.backward_byte_idx = chunk.len();
            } else if self.forward_byte_idx == self.forward_chunk.len() {
                return None;
            } else {
                let byte_idx = self.forward_chunk.len() - 1;
                let byte = self.forward_chunk[byte_idx];
                self.forward_chunk = &self.forward_chunk[..byte_idx];
                self.bytes_yielded += 1;
                return Some(byte);
            }
        }

        self.backward_byte_idx -= 1;
        let byte = self.backward_chunk[self.backward_byte_idx];
        self.bytes_yielded += 1;
        Some(byte)
    }
}

impl ExactSizeIterator for Bytes<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.bytes_total - self.bytes_yielded
    }
}

impl std::iter::FusedIterator for Bytes<'_> {}

/// An iterator over the code points (i.e. [`char`]s) of `Rope`s and
/// `RopeSlice`s.
///
/// This struct is created by the `chars` method on [`Rope`](Rope::chars())
/// and [`RopeSlice`](RopeSlice::chars()). See their documentation for more.
#[derive(Clone)]
pub struct Chars<'a> {
    chunks: Chunks<'a>,

    /// The chunk used when calling [`Chars::next()`].
    forward_chunk: &'a str,

    /// The number of bytes of `forward_chunk` that have already been
    /// yielded.
    forward_byte_idx: usize,

    /// The chunk used when calling [`Chars::next_back()`].
    backward_chunk: &'a str,

    /// The number of bytes of `backward_chunk` which are yet to be yielded.
    backward_byte_idx: usize,
}

impl<'a> From<&'a Rope> for Chars<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            forward_chunk: "",
            forward_byte_idx: 0,
            backward_chunk: "",
            backward_byte_idx: 0,
        }
    }
}

impl<'a> From<&RopeSlice<'a>> for Chars<'a> {
    #[inline]
    fn from(slice: &RopeSlice<'a>) -> Self {
        Self {
            chunks: slice.chunks(),
            forward_chunk: "",
            forward_byte_idx: 0,
            backward_chunk: "",
            backward_byte_idx: 0,
        }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.forward_byte_idx == self.forward_chunk.len() {
            if let Some(chunk) = self.chunks.next() {
                self.forward_chunk = chunk;
                self.forward_byte_idx = 0;
            } else if self.backward_byte_idx == 0 {
                return None;
            } else {
                let ch = self.backward_chunk.chars().next();

                debug_assert!(ch.is_some());

                // SAFETY: `backward_byte_idx` is greater than zero so there
                // are still chars to yield in that chunk.
                let ch = unsafe { ch.unwrap_unchecked() };

                let len = ch.len_utf8();
                self.backward_chunk = &self.backward_chunk[len..];
                self.backward_byte_idx -= len;
                return Some(ch);
            }
        }

        let ch = self.forward_chunk[self.forward_byte_idx..].chars().next();

        debug_assert!(ch.is_some());

        // SAFETY: `forward_byte_idx` is less than the byte length of
        // `chunk_front`, so there are still chars to yield in this chunk.
        let ch = unsafe { ch.unwrap_unchecked() };

        self.forward_byte_idx += ch.len_utf8();

        Some(ch)
    }
}

impl DoubleEndedIterator for Chars<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.backward_byte_idx == 0 {
            if let Some(chunk) = self.chunks.next_back() {
                self.backward_chunk = chunk;
                self.backward_byte_idx = self.backward_chunk.len();
            } else if self.forward_byte_idx == self.forward_chunk.len() {
                return None;
            } else {
                let ch = self.forward_chunk.chars().next_back();

                debug_assert!(ch.is_some());

                // SAFETY: `forward_byte_idx` is less than the byte length
                // of `chunk_front`, so there are still chars to yield in
                // that chunk.
                let ch = unsafe { ch.unwrap_unchecked() };

                self.forward_chunk = &self.forward_chunk
                    [..self.forward_chunk.len() - ch.len_utf8()];

                return Some(ch);
            }
        }

        let ch =
            self.backward_chunk[..self.backward_byte_idx].chars().next_back();

        debug_assert!(ch.is_some());

        // SAFETY: `backward_byte_idx` is greater than zero so there
        // are still chars to yield in this chunk.
        let ch = unsafe { ch.unwrap_unchecked() };

        self.backward_byte_idx -= ch.len_utf8();

        Some(ch)
    }
}

impl std::iter::FusedIterator for Chars<'_> {}

/// An iterator over the lines of `Rope`s and `RopeSlice`s, including the line
/// terminators (`\n` or `\r\n`).
///
/// This struct is created by the `raw_lines` method on
/// [`Rope`](Rope::raw_lines()) and [`RopeSlice`](RopeSlice::raw_lines()). See
/// their documentation for more.
#[derive(Clone)]
pub struct RawLines<'a> {
    units: Units<'a, { Rope::fanout() }, RopeChunk, RawLineMetric>,

    /// The number of lines that have been yielded so far.
    lines_yielded: usize,

    /// The total number of bytes this iterator will yield.
    lines_total: usize,
}

impl<'a> From<&'a Rope> for RawLines<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            units: rope.tree.units::<RawLineMetric>(),
            lines_yielded: 0,
            lines_total: rope.line_len(),
        }
    }
}

impl<'a> From<&RopeSlice<'a>> for RawLines<'a> {
    #[inline]
    fn from(slice: &RopeSlice<'a>) -> Self {
        Self {
            units: slice.tree_slice.units::<RawLineMetric>(),
            lines_yielded: 0,
            lines_total: slice.line_len(),
        }
    }
}

impl<'a> Iterator for RawLines<'a> {
    type Item = RopeSlice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next()?;
        self.lines_yielded += 1;
        Some(RopeSlice::from(tree_slice))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for RawLines<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next_back()?;
        self.lines_yielded += 1;
        Some(RopeSlice::from(tree_slice))
    }
}

impl ExactSizeIterator for RawLines<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.lines_total - self.lines_yielded
    }
}

impl std::iter::FusedIterator for RawLines<'_> {}

/// An iterator over the lines of `Rope`s and `RopeSlice`s, not including the
/// line terminators (`\n` or `\r\n`).
///
/// This struct is created by the `lines` method on [`Rope`](Rope::lines()) and
/// [`RopeSlice`](RopeSlice::lines()). See their documentation for more.
#[derive(Clone)]
pub struct Lines<'a> {
    units: Units<'a, { Rope::fanout() }, RopeChunk, LineMetric>,

    /// The number of lines that have been yielded so far.
    lines_yielded: usize,

    /// The total number of bytes this iterator will yield.
    lines_total: usize,
}

impl<'a> From<&'a Rope> for Lines<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            units: rope.tree.units::<LineMetric>(),
            lines_yielded: 0,
            lines_total: rope.line_len(),
        }
    }
}

impl<'a> From<&RopeSlice<'a>> for Lines<'a> {
    #[inline]
    fn from(slice: &RopeSlice<'a>) -> Self {
        Self {
            units: slice.tree_slice.units::<LineMetric>(),
            lines_yielded: 0,
            lines_total: slice.line_len(),
        }
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = RopeSlice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next()?;
        self.lines_yielded += 1;
        Some(RopeSlice { tree_slice, has_trailing_newline: false })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for Lines<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next_back()?;
        self.lines_yielded += 1;
        Some(RopeSlice { tree_slice, has_trailing_newline: false })
    }
}

impl ExactSizeIterator for Lines<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.lines_total - self.lines_yielded
    }
}

impl std::iter::FusedIterator for Lines<'_> {}

#[cfg_attr(docsrs, doc(cfg(feature = "graphemes")))]
#[cfg(feature = "graphemes")]
pub use graphemes::Graphemes;

#[cfg(feature = "graphemes")]
mod graphemes {
    use std::borrow::Cow;

    use unicode_segmentation::{GraphemeCursor, GraphemeIncomplete};

    use super::*;

    /// An iterator over the extended grapheme clusters of `Rope`s and
    /// `RopeSlice`s.
    ///
    /// This struct is created by the `graphemes` method on
    /// [`Rope`](Rope::graphemes()) and [`RopeSlice`](RopeSlice::graphemes()).
    /// See their documentation for more.
    #[derive(Clone)]
    pub struct Graphemes<'a> {
        chunks: Chunks<'a>,

        /// The slice we're iterating over, used to provide precontext to the
        /// `GraphemeCursor`s.
        slice: RopeSlice<'a>,

        /// The cursor used when calling [`Graphemes::next()`].
        forward_cursor: GraphemeCursor,

        /// The chunk used when calling [`Graphemes::next()`].
        forward_chunk: &'a str,

        /// The byte offset of the start of
        /// [`forward_chunk`](Self::forward_chunk) from the beginning of the
        /// iterating range, which is also the sum of the bytes of all the
        /// graphemes that have been yielded by [`Self::next()`].
        forward_offset: usize,

        /// The cursor used when calling [`Graphemes::next_back()`].
        backward_cursor: GraphemeCursor,

        /// The chunk used when calling [`Graphemes::next_back()`].
        backward_chunk: &'a str,

        /// The byte offset of the end of
        /// [`backward_chunk`](Self::backward_chunk) from the end of the
        /// iterating range, which is also the sum of the bytes of all the
        /// graphemes that have been yielded by [`Self::next_back()`].
        backward_offset: usize,
    }

    impl<'a> From<&'a Rope> for Graphemes<'a> {
        #[inline]
        fn from(rope: &'a Rope) -> Self {
            let len = rope.byte_len();

            Self {
                chunks: rope.chunks(),
                slice: rope.byte_slice(..),
                forward_cursor: GraphemeCursor::new(0, len, true),
                forward_offset: 0,
                forward_chunk: "",
                backward_cursor: GraphemeCursor::new(len, len, true),
                backward_chunk: "",
                backward_offset: len,
            }
        }
    }

    impl<'a> From<&RopeSlice<'a>> for Graphemes<'a> {
        #[inline]
        fn from(slice: &RopeSlice<'a>) -> Self {
            let len = slice.byte_len();

            Self {
                chunks: slice.chunks(),
                slice: *slice,
                forward_cursor: GraphemeCursor::new(0, len, true),
                forward_offset: 0,
                forward_chunk: "",
                backward_cursor: GraphemeCursor::new(len, len, true),
                backward_chunk: "",
                backward_offset: len,
            }
        }
    }

    impl<'a> Iterator for Graphemes<'a> {
        type Item = Cow<'a, str>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            debug_assert_eq!(
                self.forward_offset,
                self.forward_cursor.cur_cursor()
            );

            let mut using_backward_chunk = false;

            if self.forward_chunk.is_empty() {
                self.forward_chunk = if let Some(next) = self.chunks.next() {
                    next
                } else if !self.backward_chunk.is_empty() {
                    debug_assert!(
                        self.backward_cursor.cur_cursor()
                            > self.forward_cursor.cur_cursor()
                    );
                    using_backward_chunk = true;
                    self.backward_chunk
                } else {
                    return None;
                }
            }

            let mut grapheme = Cow::Borrowed("");

            loop {
                // NOTE: the chunk passed to `GraphemeCursor::next_boundary()`
                // can't be empty or it'll panic.

                match self
                    .forward_cursor
                    .next_boundary(self.forward_chunk, self.forward_offset)
                {
                    Ok(Some(byte_end)) => {
                        if byte_end == self.forward_offset {
                            debug_assert!(!grapheme.is_empty());
                            return Some(grapheme);
                        }

                        debug_assert!(byte_end > self.forward_offset);

                        let grapheme_end = &self.forward_chunk
                            [..byte_end - self.forward_offset];

                        match &mut grapheme {
                            Cow::Borrowed(gr) if gr.is_empty() => {
                                *gr = grapheme_end;
                            },

                            Cow::Borrowed(gr) => {
                                let mut gr = gr.to_owned();
                                gr.push_str(grapheme_end);
                                grapheme = Cow::Owned(gr);
                            },

                            Cow::Owned(gr) => {
                                gr.push_str(grapheme_end);
                            },
                        }

                        self.forward_offset += grapheme_end.len();

                        self.forward_chunk =
                            &self.forward_chunk[grapheme_end.len()..];

                        if using_backward_chunk {
                            self.backward_chunk = self.forward_chunk;
                        }

                        return Some(grapheme);
                    },

                    Ok(None) => return None,

                    Err(GraphemeIncomplete::NextChunk) => {
                        match &mut grapheme {
                            Cow::Borrowed(gr) if gr.is_empty() => {
                                *gr = self.forward_chunk;
                            },

                            Cow::Borrowed(gr) => {
                                let mut gr = gr.to_owned();
                                gr.push_str(self.forward_chunk);
                                grapheme = Cow::Owned(gr);
                            },

                            Cow::Owned(gr) => gr.push_str(self.forward_chunk),
                        }

                        self.forward_offset += self.forward_chunk.len();

                        self.forward_chunk =
                            if let Some(next) = self.chunks.next() {
                                next
                            } else if !self.backward_chunk.is_empty() {
                                debug_assert!(
                                    self.backward_cursor.cur_cursor()
                                        > self.forward_cursor.cur_cursor()
                                );
                                using_backward_chunk = true;
                                self.backward_chunk
                            } else {
                                return None;
                            }
                    },

                    // Why does it ask for precontext if we've been feeding it
                    // stuff from the beginning of the range?
                    Err(GraphemeIncomplete::PreContext(byte_idx)) => {
                        let slice = self.slice.byte_slice(..byte_idx);
                        let chunk = slice.chunks().next_back().unwrap();
                        self.forward_cursor
                            .provide_context(chunk, byte_idx - chunk.len());
                    },

                    Err(_) => {
                        unreachable!();
                    },
                }
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            let hi = self.backward_offset - self.forward_offset;
            let lo = (hi != 0) as usize;
            (lo, Some(hi))
        }
    }

    impl DoubleEndedIterator for Graphemes<'_> {
        #[inline]
        fn next_back(&mut self) -> Option<Self::Item> {
            debug_assert_eq!(
                self.backward_offset,
                self.backward_cursor.cur_cursor()
            );

            let mut using_forward_chunk = false;

            if self.backward_chunk.is_empty() {
                self.backward_chunk =
                    if let Some(prev) = self.chunks.next_back() {
                        prev
                    } else if !self.forward_chunk.is_empty() {
                        debug_assert!(
                            self.backward_cursor.cur_cursor()
                                > self.forward_cursor.cur_cursor()
                        );
                        using_forward_chunk = true;
                        self.forward_chunk
                    } else {
                        return None;
                    }
            }

            let mut grapheme = Cow::Borrowed("");

            loop {
                // NOTE: the chunk passed to `GraphemeCursor::prev_boundary()`
                // can't be empty or it'll panic.

                match self.backward_cursor.prev_boundary(
                    self.backward_chunk,
                    self.backward_cursor.cur_cursor()
                        - self.backward_chunk.len(),
                ) {
                    Ok(Some(byte_start)) => {
                        if byte_start == self.backward_offset {
                            debug_assert!(!grapheme.is_empty());
                            return Some(grapheme);
                        }

                        debug_assert!(byte_start < self.backward_offset);

                        let grapheme_start = {
                            let start_len = self.backward_offset - byte_start;
                            let chunk_len = self.backward_chunk.len();
                            &self.backward_chunk[(chunk_len - start_len)..]
                        };

                        match &mut grapheme {
                            Cow::Borrowed(gr) if gr.is_empty() => {
                                *gr = grapheme_start;
                            },

                            Cow::Borrowed(gr) => {
                                let mut new = String::with_capacity(
                                    grapheme_start.len() + gr.len(),
                                );
                                new.push_str(grapheme_start);
                                new.push_str(gr);
                                grapheme = Cow::Owned(new);
                            },

                            Cow::Owned(gr) => {
                                let mut new = String::with_capacity(
                                    grapheme_start.len() + gr.len(),
                                );
                                new.push_str(grapheme_start);
                                new.push_str(&*gr);
                                *gr = new;
                            },
                        }

                        self.backward_offset -= grapheme_start.len();

                        self.backward_chunk =
                            &self.backward_chunk[..self.backward_chunk.len()
                                - grapheme_start.len()];

                        if using_forward_chunk {
                            self.forward_chunk = self.backward_chunk;
                        }

                        return Some(grapheme);
                    },

                    Ok(None) => return None,

                    Err(GraphemeIncomplete::PrevChunk) => {
                        match &mut grapheme {
                            Cow::Borrowed(gr) if gr.is_empty() => {
                                *gr = self.backward_chunk;
                            },

                            Cow::Borrowed(gr) => {
                                let mut new = String::with_capacity(
                                    self.backward_chunk.len() + gr.len(),
                                );
                                new.push_str(self.backward_chunk);
                                new.push_str(gr);
                                grapheme = Cow::Owned(new);
                            },

                            Cow::Owned(gr) => {
                                let mut new = String::with_capacity(
                                    self.backward_chunk.len() + gr.len(),
                                );
                                new.push_str(self.backward_chunk);
                                new.push_str(gr);
                                *gr = new;
                            },
                        }

                        self.backward_offset -= self.backward_chunk.len();

                        self.backward_chunk =
                            if let Some(prev) = self.chunks.next_back() {
                                prev
                            } else if !self.forward_chunk.is_empty() {
                                debug_assert!(
                                    self.backward_cursor.cur_cursor()
                                        > self.forward_cursor.cur_cursor()
                                );
                                using_forward_chunk = true;
                                self.forward_chunk
                            } else {
                                return None;
                            }
                    },

                    // Why does it ask for precontext if we're iterating
                    // backward? Shouldn't it always just ask for the previous
                    // chunk?
                    Err(GraphemeIncomplete::PreContext(byte_idx)) => {
                        let slice = self.slice.byte_slice(..byte_idx);
                        let chunk = slice.chunks().next_back().unwrap();
                        self.backward_cursor
                            .provide_context(chunk, byte_idx - chunk.len());
                    },

                    Err(_) => {
                        unreachable!();
                    },
                }
            }
        }
    }

    impl std::iter::FusedIterator for Graphemes<'_> {}
}
