use super::metrics::LineMetric;
use super::{Rope, RopeSlice, TextChunk};
use crate::tree::{Chops, Leaves};

/// TODO: docs
#[derive(Clone)]
pub(super) struct Chunks<'a> {
    pub(super) chunks: Leaves<'a, TextChunk>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().map(std::ops::Deref::deref)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.chunks.len();
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for Chunks<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Bytes<'a> {
    chunks: Chunks<'a>,
    current: &'a [u8],
    yielded_in_current: usize,
    total_yielded: usize,
    total_bytes: usize,
}

impl<'a> From<&'a Rope> for Bytes<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        let mut chunks = rope.chunks();
        let current = chunks.next().unwrap_or_default().as_bytes();
        Self {
            chunks,
            current,
            yielded_in_current: 0,
            total_yielded: 0,
            total_bytes: rope.byte_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Bytes<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        let mut chunks = slice.chunks();
        let current = chunks.next().unwrap_or_default().as_bytes();
        Self {
            chunks,
            current,
            yielded_in_current: 0,
            total_yielded: 0,
            total_bytes: slice.byte_len(),
        }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_in_current == self.current.len() {
            // NOTE: make sure there are never empty chunks or this will make
            // the byte indexing below fail.
            self.current = self.chunks.next()?.as_bytes();
            self.yielded_in_current = 0;
        }

        let byte = self.current[self.yielded_in_current];
        self.yielded_in_current += 1;
        self.total_yielded += 1;
        Some(byte)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.total_bytes - self.total_yielded;
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for Bytes<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Chars<'a> {
    chunks: Chunks<'a>,
    current: &'a str,
    /// Note: this is the number of *bytes* already yielded in `current`, not
    /// chars.
    yielded_in_current: usize,
}

impl<'a> From<&'a Rope> for Chars<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        let mut chunks = rope.chunks();
        let current = chunks.next().unwrap_or_default();
        Self { chunks, current, yielded_in_current: 0 }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chars<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        let mut chunks = slice.chunks();
        let current = chunks.next().unwrap_or_default();
        Self { chunks, current, yielded_in_current: 0 }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_in_current == self.current.len() {
            // NOTE: make sure there are never empty chunks or this will make
            // the byte indexing below fail.
            self.current = self.chunks.next()?;
            self.yielded_in_current = 0;
        }

        let char = unsafe {
            self.current[self.yielded_in_current..]
                .chars()
                .next()
                // Safety: `yielded_in_current < current.len()`, so there are
                // still chars to yield in this chunk.
                .unwrap_unchecked()
        };
        self.yielded_in_current += char.len_utf8();
        Some(char)
    }
}

#[derive(Clone)]
pub struct Lines<'a> {
    chops: Chops<'a, { Rope::fanout() }, TextChunk, LineMetric>,
}

impl<'a> From<&'a Rope> for Lines<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        todo!()
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Lines<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        todo!()
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = RopeSlice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.chops.next().map(RopeSlice::new)
    }
}

#[cfg(test)]
mod tests {
    use crate::Rope;

    #[test]
    fn bytes_1() {
        let r = Rope::from("Hello world this is my dog -> 🐕‍🦺");
        assert_eq!(41, r.bytes().count());
        assert_eq!(33, r.chars().count());
    }
}
