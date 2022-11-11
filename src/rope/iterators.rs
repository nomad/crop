use super::{Rope, TextChunk};
use crate::tree::Leaves;

#[derive(Clone)]
pub(super) struct Chunks<'a> {
    pub(super) chunks: Leaves<'a, TextChunk>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().map(|s| &*s.text)
    }

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

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_in_current == self.current.len() {
            // NOTE: make sure there are never empty chunks or this will fail.
            self.current = self.chunks.next()?.as_bytes();
            self.yielded_in_current = 0;
        }

        let byte = self.current[self.yielded_in_current];
        self.yielded_in_current += 1;
        self.total_yielded += 1;
        Some(byte)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.total_bytes - self.total_yielded;
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for Bytes<'a> {}

#[cfg(test)]
mod tests {
    use crate::Rope;

    #[test]
    fn bytes_1() {
        let r = Rope::from("Hello world this is my dog -> 🐕‍🦺");
        assert_eq!(41, r.bytes().count());
    }
}
