use super::metrics::{LineMetric, RawLineMetric};
use super::{Rope, RopeChunk, RopeSlice};
use crate::tree::{Leaves, Units};

/// An iterator over the chunks of `Rope`s and `RopeSlice`s.
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

impl<'a> From<&'a RopeSlice<'a>> for Chunks<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'a>) -> Self {
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
        use std::ops::Deref;
        self.leaves.next().map(|(slice, _)| slice.deref())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.leaves.len();
        (exact, Some(exact))
    }
}

impl DoubleEndedIterator for Chunks<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        use std::ops::Deref;
        self.leaves.next_back().map(|(slice, _)| slice.deref())
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

impl<'a> From<&'a RopeSlice<'a>> for Bytes<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'a>) -> Self {
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
            // We've exhausted the current chunk.
            if let Some(chunk) = self.chunks.next() {
                self.forward_chunk = chunk.as_bytes();
                self.forward_byte_idx = 0;
            } else {
                // There are no more chunks but there may still be some
                // un-yielded bytes on the backward chunk.
                if self.backward_byte_idx == 0 {
                    return None;
                } else {
                    // We return the first byte of the backward chunk, remove
                    // that byte from the chunk and update the backward byte
                    // index.
                    let byte = self.backward_chunk[0];
                    self.backward_chunk = &self.backward_chunk[1..];
                    self.backward_byte_idx -= 1;
                    self.bytes_yielded += 1;
                    return Some(byte);
                }
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
            // We've exhausted the current chunk.
            if let Some(chunk) = self.chunks.next_back() {
                self.backward_chunk = chunk.as_bytes();
                self.backward_byte_idx = chunk.len();
            } else {
                // There are no more chunks but there may still be some
                // un-yielded bytes on the forward chunk.
                if self.forward_byte_idx == self.forward_chunk.len() {
                    return None;
                } else {
                    // We return the last byte of the forward chunk and remove
                    // that byte from the chunk.
                    let byte_idx = self.forward_chunk.len() - 1;
                    let byte = self.forward_chunk[byte_idx];
                    self.forward_chunk = &self.forward_chunk[..byte_idx];
                    self.bytes_yielded += 1;
                    return Some(byte);
                }
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

/// An iterator over the [`char`]s of `Rope`s and `RopeSlice`s.
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

impl<'a> From<&'a RopeSlice<'a>> for Chars<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'a>) -> Self {
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
            } else {
                // Note: see `Bytes::next` for some relevant comments.
                if self.backward_byte_idx == 0 {
                    return None;
                } else {
                    let ch = self.backward_chunk.chars().next();

                    debug_assert!(ch.is_some());

                    // Safety: `backward_byte_idx` is greater than zero so there
                    // are still chars to yield in that chunk.
                    let ch = unsafe { ch.unwrap_unchecked() };

                    let len = ch.len_utf8();
                    self.backward_chunk = &self.backward_chunk[len..];
                    self.backward_byte_idx -= len;
                    return Some(ch);
                }
            }
        }

        let ch = self.forward_chunk[self.forward_byte_idx..].chars().next();

        debug_assert!(ch.is_some());

        // Safety: `forward_byte_idx` is less than the byte length of
        // `chunk_front`, so there are still chars to yield in this chunk.
        let ch = unsafe { ch.unwrap_unchecked() };

        self.forward_byte_idx += ch.len_utf8();

        Some(ch)
    }
}

impl<'a> DoubleEndedIterator for Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.backward_byte_idx == 0 {
            if let Some(chunk) = self.chunks.next_back() {
                self.backward_chunk = chunk;
                self.backward_byte_idx = self.backward_chunk.len();
            } else {
                // Note: see `Bytes::next_back` for some relevant comments.
                if self.forward_byte_idx == self.forward_chunk.len() {
                    return None;
                } else {
                    let ch = self.forward_chunk.chars().next_back();

                    debug_assert!(ch.is_some());

                    // Safety: `forward_byte_idx` is less than the byte length
                    // of `chunk_front`, so there are still chars to yield in
                    // that chunk.
                    let ch = unsafe { ch.unwrap_unchecked() };

                    self.forward_chunk = &self.forward_chunk
                        [..self.forward_chunk.len() - ch.len_utf8()];

                    return Some(ch);
                }
            }
        }

        let ch =
            self.backward_chunk[..self.backward_byte_idx].chars().next_back();

        debug_assert!(ch.is_some());

        // Safety: `backward_byte_idx` is greater than zero so there
        // are still chars to yield in this chunk.
        let ch = unsafe { ch.unwrap_unchecked() };

        self.backward_byte_idx -= ch.len_utf8();

        Some(ch)
    }
}

impl<'a> std::iter::FusedIterator for Chars<'a> {}

/// An iterator over the raw lines of `Rope`s and `RopeSlice`s.
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

impl<'a> From<&'a RopeSlice<'a>> for RawLines<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'a>) -> Self {
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

impl<'a> DoubleEndedIterator for RawLines<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next_back()?;
        self.lines_yielded += 1;
        Some(RopeSlice::from(tree_slice))
    }
}

impl<'a> ExactSizeIterator for RawLines<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.lines_total - self.lines_yielded
    }
}

impl<'a> std::iter::FusedIterator for RawLines<'a> {}

/// An iterator over the lines of `Rope`s and `RopeSlice`s.
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

impl<'a> From<&'a RopeSlice<'a>> for Lines<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'a>) -> Self {
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
        Some(RopeSlice { tree_slice, last_byte_is_newline: false })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for Lines<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next_back()?;
        self.lines_yielded += 1;
        Some(RopeSlice { tree_slice, last_byte_is_newline: false })
    }
}

impl<'a> ExactSizeIterator for Lines<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.lines_total - self.lines_yielded
    }
}

impl<'a> std::iter::FusedIterator for Lines<'a> {}

#[cfg(feature = "graphemes")]
pub use graphemes::Graphemes;

#[cfg(feature = "graphemes")]
mod graphemes {
    use std::borrow::Cow;

    use unicode_segmentation::{GraphemeCursor, GraphemeIncomplete};

    use super::*;

    /// TODO: docs
    #[derive(Clone)]
    pub struct Graphemes<'a> {
        /// TODO: docs
        chunks: Chunks<'a>,

        /// TODO: docs
        forward_chunk: &'a str,

        /// TODO: docs
        offset_of_forward_chunk: usize,

        /// TODO: docs
        yielded_in_forward_chunk: usize,

        /// TODO: docs
        _backward_chunk: &'a str,

        /// TODO: docs
        _to_be_yielded_in_backward_chunk: usize,

        /// TODO: docs
        yielded_forward: usize,

        /// TODO: docs
        yielded_backward: usize,

        /// TODO: docs
        total_bytes: usize,

        /// TODO: docs
        cursor: GraphemeCursor,
    }

    impl<'a> From<&'a Rope> for Graphemes<'a> {
        #[inline]
        fn from(rope: &'a Rope) -> Self {
            Self {
                chunks: rope.chunks(),
                forward_chunk: "",
                yielded_in_forward_chunk: 0,
                offset_of_forward_chunk: 0,
                _backward_chunk: "",
                _to_be_yielded_in_backward_chunk: 0,
                yielded_forward: 0,
                yielded_backward: 0,
                total_bytes: rope.byte_len(),
                cursor: GraphemeCursor::new(0, rope.byte_len(), true),
            }
        }
    }

    impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Graphemes<'a> {
        #[inline]
        fn from(slice: &'a RopeSlice<'b>) -> Self {
            Self {
                chunks: slice.chunks(),
                forward_chunk: "",
                yielded_in_forward_chunk: 0,
                offset_of_forward_chunk: 0,
                _backward_chunk: "",
                _to_be_yielded_in_backward_chunk: 0,
                yielded_forward: 0,
                yielded_backward: 0,
                total_bytes: slice.byte_len(),
                cursor: GraphemeCursor::new(0, slice.byte_len(), true),
            }
        }
    }

    impl<'a> Iterator for Graphemes<'a> {
        type Item = Cow<'a, str>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            if self.yielded_forward + self.yielded_backward == self.total_bytes
            {
                return None;
            }

            if self.yielded_in_forward_chunk == self.forward_chunk.len() {
                self.forward_chunk = match self.chunks.next() {
                    Some(chunk) => {
                        // NOTE: make sure  there are never empty chunks or
                        // this will make the byte indexing below fail.
                        chunk
                    },

                    None => {
                        todo!()
                    },
                }
            };

            let start = self.cursor.cur_cursor();

            let end = match self.cursor.next_boundary(
                self.forward_chunk,
                self.offset_of_forward_chunk,
            ) {
                Ok(None) => return None,

                Ok(Some(n)) => n,

                Err(GraphemeIncomplete::NextChunk) => {
                    let mut grapheme = String::from(
                        &self.forward_chunk[self.yielded_in_forward_chunk..],
                    );

                    self.offset_of_forward_chunk += self.forward_chunk.len();

                    self.forward_chunk = match self.chunks.next() {
                        Some(chunk) => chunk,
                        None => todo!(),
                    };

                    println!("grapheme: {grapheme}");
                    println!("forward_chunk: {}", self.forward_chunk);
                    println!(
                        "offset_forward_chunk: {}",
                        self.offset_of_forward_chunk
                    );

                    loop {
                        let grapheme = match self.cursor.next_boundary(
                            self.forward_chunk,
                            self.offset_of_forward_chunk,
                        ) {
                            Ok(None) => grapheme,

                            Ok(Some(n)) => {
                                println!("bb");
                                let end = n - self.offset_of_forward_chunk;
                                grapheme.push_str(&self.forward_chunk[..end]);
                                grapheme
                            },

                            Err(GraphemeIncomplete::NextChunk) => {
                                println!("aa");
                                self.offset_of_forward_chunk +=
                                    self.forward_chunk.len();

                                self.forward_chunk = match self.chunks.next() {
                                    Some(chunk) => chunk,
                                    None => todo!(),
                                };

                                continue;
                            },

                            Err(GraphemeIncomplete::PreContext(_)) => todo!(),

                            _ => unreachable!(),
                        };

                        println!(
                            "returning {grapheme} which is {} long",
                            grapheme.len()
                        );

                        self.yielded_in_forward_chunk += grapheme.len();
                        self.yielded_forward += grapheme.len();
                        return Some(Cow::Owned(grapheme));
                    }
                },

                Err(GraphemeIncomplete::PreContext(_)) => todo!(),

                _ => unreachable!(),
            };

            let grapheme = &self.forward_chunk[start..end];
            self.yielded_in_forward_chunk += grapheme.len();
            self.yielded_forward += grapheme.len();
            Some(Cow::Borrowed(grapheme))
        }
    }

    impl<'a> DoubleEndedIterator for Graphemes<'a> {
        #[inline]
        fn next_back(&mut self) -> Option<Self::Item> {
            todo!()
        }
    }

    impl<'a> std::iter::FusedIterator for Graphemes<'a> {}
}
