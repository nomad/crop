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
        Self { leaves: rope.root().leaves() }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chunks<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self { leaves: slice.tree_slice.leaves() }
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
        let exact = self.leaves.len();
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for Chunks<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.leaves.next_back().map(std::ops::Deref::deref)
    }
}

impl<'a> ExactSizeIterator for Chunks<'a> {}

impl<'a> std::iter::FusedIterator for Chunks<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Bytes<'a> {
    /// TODO: docs
    chunks: Chunks<'a>,

    /// TODO: docs
    current_forward: &'a [u8],

    /// TODO: docs
    forward_byte_idx: usize,

    /// TODO: docs
    current_backward: &'a [u8],

    /// TODO: docs
    backward_byte_idx: usize,

    /// TODO: docs
    yielded_forward: usize,

    /// TODO: docs
    yielded_backward: usize,

    /// TODO: docs
    total_bytes: usize,
}

impl<'a> From<&'a Rope> for Bytes<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            current_forward: &[],
            forward_byte_idx: 0,
            yielded_forward: 0,
            current_backward: &[],
            backward_byte_idx: 0,
            yielded_backward: 0,
            total_bytes: rope.byte_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Bytes<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self {
            chunks: slice.chunks(),
            current_forward: &[],
            forward_byte_idx: 0,
            yielded_forward: 0,
            current_backward: &[],
            backward_byte_idx: 0,
            yielded_backward: 0,
            total_bytes: slice.byte_len(),
        }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.forward_byte_idx == self.current_forward.len() {
            self.current_forward = match self.chunks.next() {
                Some(chunk) => {
                    // NOTE: make sure  there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk.as_bytes()
                },

                None => {
                    // There are no more chunks to get but there may be some
                    // bytes yet to yielded on the backward chunk.
                    if self.backward_byte_idx == 0 {
                        return None;
                    } else {
                        // Return the first byte of the backward chunk, make
                        // it one byte smaller and return.

                        let byte = self.current_backward[0];
                        self.current_backward = &self.current_backward[1..];

                        // After making the backward chunk 1 byte smaller we
                        // have to decrease the backward byte idx by one to
                        // keep those in sync.
                        self.backward_byte_idx -= 1;

                        self.yielded_forward += 1;
                        return Some(byte);
                    }
                },
            };
            self.forward_byte_idx = 0;
        }

        let byte = self.current_forward[self.forward_byte_idx];
        self.forward_byte_idx += 1;
        self.yielded_forward += 1;
        Some(byte)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact =
            self.total_bytes - self.yielded_forward - self.yielded_backward;
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for Bytes<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.backward_byte_idx == 0 {
            self.current_backward = match self.chunks.next_back() {
                Some(chunk) => {
                    // NOTE: make sure  there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk.as_bytes()
                },

                None => {
                    // There are no more chunks to get but there may be some
                    // bytes yet to yielded on the forward chunk.
                    if self.forward_byte_idx == self.current_forward.len() {
                        return None;
                    } else {
                        // Return the last byte of the forward chunk, make
                        // it one byte smaller and return.
                        let byte = self.current_forward
                            [self.current_forward.len() - 1];

                        self.current_forward = &self.current_forward
                            [..self.current_forward.len() - 1];

                        self.yielded_backward += 1;

                        return Some(byte);
                    }
                },
            };
            self.backward_byte_idx = self.current_backward.len();
        }

        let byte = self.current_backward[self.backward_byte_idx - 1];
        self.backward_byte_idx -= 1;
        self.yielded_backward += 1;
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
    current_forward: &'a str,

    /// Note: this is the number of *bytes* already yielded in `current`, not
    /// chars.
    forward_byte_idx: usize,

    /// TODO: docs
    current_backward: &'a str,

    /// TODO: docs
    backward_byte_idx: usize,

    /// TODO: docs
    yielded_forward: usize,

    /// TODO: docs
    yielded_backward: usize,

    /// TODO: docs
    total_bytes: usize,
}

impl<'a> From<&'a Rope> for Chars<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            current_forward: "",
            forward_byte_idx: 0,
            current_backward: "",
            backward_byte_idx: 0,
            yielded_forward: 0,
            yielded_backward: 0,
            total_bytes: rope.byte_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chars<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self {
            chunks: slice.chunks(),
            current_forward: "",
            forward_byte_idx: 0,
            current_backward: "",
            backward_byte_idx: 0,
            yielded_forward: 0,
            yielded_backward: 0,
            total_bytes: slice.byte_len(),
        }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.forward_byte_idx == self.current_forward.len() {
            self.current_forward = match self.chunks.next() {
                Some(chunk) => {
                    // NOTE: make sure there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk
                },

                None => {
                    // NOTE: see `Bytes::next` for relevant comments.

                    if self.backward_byte_idx == 0 {
                        return None;
                    } else {
                        debug_assert!(self
                            .current_backward
                            .chars()
                            .next()
                            .is_some());

                        let char = unsafe {
                            self.current_backward
                                .chars()
                                .next()
                                // Safety: `backward_byte_idx > 0`, so
                                // there are still chars to yield in this
                                // chunk.
                                .unwrap_unchecked()
                        };

                        let len = char.len_utf8();

                        self.current_backward = &self.current_backward[len..];
                        self.backward_byte_idx -= len;
                        self.yielded_forward += len;
                        return Some(char);
                    }
                },
            };
            self.forward_byte_idx = 0;
        }

        debug_assert!(self.current_forward[self.forward_byte_idx..]
            .chars()
            .next()
            .is_some());

        let char = unsafe {
            self.current_forward[self.forward_byte_idx..]
                .chars()
                .next()
                // Safety: `forward_byte_idx < current_forward.len()`, so there
                // are still chars to yield in this chunk.
                .unwrap_unchecked()
        };

        let len = char.len_utf8();
        self.forward_byte_idx += len;
        self.yielded_forward += len;

        Some(char)
    }
}

impl<'a> DoubleEndedIterator for Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.backward_byte_idx == 0 {
            self.current_backward = match self.chunks.next_back() {
                Some(chunk) => {
                    // NOTE: make sure there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk
                },

                None => {
                    // NOTE: see `Bytes::next_back` for relevant comments.

                    if self.forward_byte_idx == self.current_forward.len() {
                        return None;
                    } else {
                        debug_assert!(self
                            .current_forward
                            .chars()
                            .next_back()
                            .is_some());

                        let char = unsafe {
                            self.current_forward
                                .chars()
                                .next_back()
                                // Safety: `forward_byte_idx <
                                // current_forward.len()`, so there are still
                                // chars to yield in this chunk.
                                .unwrap_unchecked()
                        };

                        let len = char.len_utf8();

                        self.current_forward = &self.current_forward
                            [..self.current_forward.len() - len];

                        self.yielded_backward += len;

                        return Some(char);
                    }
                },
            };
            self.backward_byte_idx = self.current_backward.len();
        }

        debug_assert!(self.current_backward[..self.backward_byte_idx]
            .chars()
            .next_back()
            .is_some());

        let char = unsafe {
            self.current_backward[..self.backward_byte_idx]
                .chars()
                .next_back()
                // Safety: `backward_byte_idx > 0`, so there are still chars to
                // yield in this chunk.
                .unwrap_unchecked()
        };

        let len = char.len_utf8();
        self.backward_byte_idx -= len;
        self.yielded_backward += len;

        Some(char)
    }
}

impl<'a> std::iter::FusedIterator for Chars<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Lines<'a> {
    units: Units<'a, { Rope::fanout() }, RopeChunk, LineMetric>,
}

impl<'a> From<&'a Rope> for Lines<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self { units: rope.root().units::<LineMetric>() }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Lines<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self { units: slice.tree_slice.units::<LineMetric>() }
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = RopeSlice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.units.next().map(RopeSlice::from)
    }
}

#[doc(hidden)]
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

impl<'a> std::iter::FusedIterator for Lines<'a> {}
