use super::metrics::LineMetric;
use super::{Rope, RopeChunk, RopeSlice};
use crate::tree::{Leaves, Units};

/// TODO: docs
#[derive(Clone)]
pub struct Chunks<'a> {
    leaves: Leaves<'a, { Rope::fanout() }, RopeChunk>,
}

impl<'a> From<&'a Rope> for Chunks<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        let mut leaves = rope.tree().leaves();
        if rope.byte_len() == 0 {
            let _ = leaves.next();
        }
        Self { leaves }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chunks<'a> {
    #[inline]
    fn from(rope_slice: &'a RopeSlice<'b>) -> Self {
        let mut leaves = rope_slice.tree_slice.leaves();
        if rope_slice.byte_len() == 0 {
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

impl<'a> DoubleEndedIterator for Chunks<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        use std::ops::Deref;
        self.leaves.next_back().map(|(slice, _)| slice.deref())
    }
}

impl<'a> ExactSizeIterator for Chunks<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.leaves.len()
    }
}

impl<'a> std::iter::FusedIterator for Chunks<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Bytes<'a> {
    /// TODO: docs
    chunks: Chunks<'a>,

    /// TODO: docs
    chunk_front: &'a [u8],

    /// TODO: docs
    byte_idx_front: usize,

    /// TODO: docs
    chunk_back: &'a [u8],

    /// TODO: docs
    byte_idx_back: usize,

    /// TODO: docs
    yielded: usize,

    /// TODO: docs
    total: usize,
}

impl<'a> From<&'a Rope> for Bytes<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            chunk_front: &[],
            byte_idx_front: 0,
            chunk_back: &[],
            byte_idx_back: 0,
            yielded: 0,
            total: rope.byte_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Bytes<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self {
            chunks: slice.chunks(),
            chunk_front: &[],
            byte_idx_front: 0,
            chunk_back: &[],
            byte_idx_back: 0,
            yielded: 0,
            total: slice.byte_len(),
        }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.byte_idx_front == self.chunk_front.len() {
            // We've exhausted the current chunk.
            if let Some(chunk) = self.chunks.next() {
                self.chunk_front = chunk.as_bytes();
                self.byte_idx_front = 0;
            } else {
                // There are no more chunks but there may still be some
                // un-yielded bytes on the backward chunk.
                if self.byte_idx_back == 0 {
                    return None;
                } else {
                    // We return the first byte of the backward chunk, remove
                    // that byte from the chunk and update the backward byte
                    // index.
                    let byte = self.chunk_back[0];
                    self.chunk_back = &self.chunk_back[1..];
                    self.byte_idx_back -= 1;
                    self.yielded += 1;
                    return Some(byte);
                }
            }
        }

        let byte = self.chunk_front[self.byte_idx_front];
        self.byte_idx_front += 1;
        self.yielded += 1;
        Some(byte)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.total - self.yielded;
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for Bytes<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.byte_idx_back == 0 {
            // We've exhausted the current chunk.
            if let Some(chunk) = self.chunks.next_back() {
                self.chunk_back = chunk.as_bytes();
                self.byte_idx_back = chunk.len();
            } else {
                // There are no more chunks but there may still be some
                // un-yielded bytes on the forward chunk.
                if self.byte_idx_front == self.chunk_front.len() {
                    return None;
                } else {
                    // We return the last byte of the forward chunk and remove
                    // that byte from the chunk.
                    let byte_idx = self.chunk_front.len() - 1;
                    let byte = self.chunk_front[byte_idx];
                    self.chunk_front = &self.chunk_front[..byte_idx];
                    self.yielded += 1;
                    return Some(byte);
                }
            }
        }

        self.byte_idx_back -= 1;
        let byte = self.chunk_back[self.byte_idx_back];
        self.yielded += 1;
        Some(byte)
    }
}

impl<'a> ExactSizeIterator for Bytes<'a> {}

impl<'a> std::iter::FusedIterator for Bytes<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Chars<'a> {
    /// TODO: docs
    chunks: Chunks<'a>,

    /// TODO: docs
    chunk_front: &'a str,

    /// TODO: docs
    byte_idx_front: usize,

    /// TODO: docs
    chunk_back: &'a str,

    /// TODO: docs
    byte_idx_back: usize,
}

impl<'a> From<&'a Rope> for Chars<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            chunk_front: "",
            byte_idx_front: 0,
            chunk_back: "",
            byte_idx_back: 0,
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chars<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self {
            chunks: slice.chunks(),
            chunk_front: "",
            byte_idx_front: 0,
            chunk_back: "",
            byte_idx_back: 0,
        }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.byte_idx_front == self.chunk_front.len() {
            if let Some(chunk) = self.chunks.next() {
                self.chunk_front = chunk;
                self.byte_idx_front = 0;
            } else {
                // Note: see `Bytes::next` for some relevant comments.
                if self.byte_idx_back == 0 {
                    return None;
                } else {
                    let ch = self.chunk_back.chars().next();

                    debug_assert!(ch.is_some());

                    // Safety: `byte_idx_back` is greater than zero so there
                    // are still chars to yield in that chunk.
                    let ch = unsafe { ch.unwrap_unchecked() };

                    let len = ch.len_utf8();
                    self.chunk_back = &self.chunk_back[len..];
                    self.byte_idx_back -= len;
                    return Some(ch);
                }
            }
        }

        let ch = self.chunk_front[self.byte_idx_front..].chars().next();

        debug_assert!(ch.is_some());

        // Safety: `byte_idx_front` is less than the byte length of
        // `chunk_front`, so there are still chars to yield in this chunk.
        let ch = unsafe { ch.unwrap_unchecked() };

        self.byte_idx_front += ch.len_utf8();

        Some(ch)
    }
}

impl<'a> DoubleEndedIterator for Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.byte_idx_back == 0 {
            if let Some(chunk) = self.chunks.next_back() {
                self.chunk_back = chunk;
                self.byte_idx_back = self.chunk_back.len();
            } else {
                // Note: see `Bytes::next_back` for some relevant comments.
                if self.byte_idx_front == self.chunk_front.len() {
                    return None;
                } else {
                    let ch = self.chunk_front.chars().next_back();

                    debug_assert!(ch.is_some());

                    // Safety: `byte_idx_front` is less than the byte length of
                    // `chunk_front`, so there are still chars to yield in that
                    // chunk.
                    let ch = unsafe { ch.unwrap_unchecked() };

                    self.chunk_front = &self.chunk_front
                        [..self.chunk_front.len() - ch.len_utf8()];

                    return Some(ch);
                }
            }
        }

        let ch = self.chunk_back[..self.byte_idx_back].chars().next_back();

        debug_assert!(ch.is_some());

        // Safety: `byte_idx_back` is greater than zero so there
        // are still chars to yield in this chunk.
        let ch = unsafe { ch.unwrap_unchecked() };

        self.byte_idx_back -= ch.len_utf8();

        Some(ch)
    }
}

impl<'a> std::iter::FusedIterator for Chars<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct LinesRaw<'a> {
    units: Units<'a, { Rope::fanout() }, RopeChunk, LineMetric>,
    yielded: usize,
    total: usize,
}

impl<'a> From<&'a Rope> for LinesRaw<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            units: rope.tree().units::<LineMetric>(),
            yielded: 0,
            total: rope.line_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for LinesRaw<'a> {
    #[inline]
    fn from(rope_slice: &'a RopeSlice<'b>) -> Self {
        Self {
            units: rope_slice.tree_slice.units::<LineMetric>(),
            yielded: 0,
            total: rope_slice.line_len(),
        }
    }
}

impl<'a> Iterator for LinesRaw<'a> {
    type Item = RopeSlice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next()?;
        self.yielded += 1;
        Some(RopeSlice::from(tree_slice))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.total - self.yielded;
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for LinesRaw<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next_back()?;
        self.yielded += 1;
        Some(RopeSlice::from(tree_slice))
    }
}

impl<'a> ExactSizeIterator for LinesRaw<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.total - self.yielded
    }
}

impl<'a> std::iter::FusedIterator for LinesRaw<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Lines<'a> {
    units: Units<'a, { Rope::fanout() }, RopeChunk, LineMetric>,
    yielded: usize,
    total: usize,
}

impl<'a> From<&'a Rope> for Lines<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            units: rope.tree().units::<LineMetric>(),
            yielded: 0,
            total: rope.line_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Lines<'a> {
    #[inline]
    fn from(rope_slice: &'a RopeSlice<'b>) -> Self {
        Self {
            units: rope_slice.tree_slice.units::<LineMetric>(),
            yielded: 0,
            total: rope_slice.line_len(),
        }
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = RopeSlice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next()?;
        self.yielded += 1;
        Some(RopeSlice::from(tree_slice))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.total - self.yielded;
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for Lines<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let tree_slice = self.units.next_back()?;
        self.yielded += 1;
        Some(RopeSlice::from(tree_slice))
    }
}

impl<'a> ExactSizeIterator for Lines<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.total - self.yielded
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
