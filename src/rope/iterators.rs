use super::TextChunk;
use crate::tree::Leaves;

pub(super) struct Chunks<'a> {
    pub(super) chunks: Leaves<'a, TextChunk>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().map(|s| &*s.text)
    }
}
