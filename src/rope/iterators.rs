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
}

/// TODO: docs
#[derive(Clone)]
pub struct Bytes<'a> {
    chunks: Chunks<'a>,
    current: &'a str,
    yielded: usize,
    total_bytes: usize,
}

impl<'a> From<&'a Rope> for Bytes<'a> {
    fn from(rope: &'a Rope) -> Self {
        let mut chunks = rope.chunks();
        let current = chunks.next().unwrap_or_default();
        Self { chunks, current, yielded: 0, total_bytes: rope.byte_len() }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        while self.current.is_empty() || self.yielded == self.current.len() {
            self.current = self.chunks.next()?;
            self.yielded = 0;
        }

        let byte = self.current.as_bytes()[self.yielded];
        self.yielded += 1;
        Some(byte)
    }
}

#[cfg(test)]
mod tests {
    use crate::Rope;

    #[test]
    fn bytes_1() {
        let r = Rope::from("Hello world this is my dog -> 🐕‍🦺");
        assert_eq!(41, r.bytes().count());
    }
}
