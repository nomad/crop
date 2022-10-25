use std::fmt;

use super::Summarize;

pub(super) struct Leaf<Chunk: Summarize> {
    pub(super) chunk: Chunk,
    pub(super) summary: Chunk::Summary,
}

impl<Chunk: Summarize> fmt::Debug for Leaf<Chunk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !f.alternate() {
            f.debug_struct("Leaf")
                .field("chunk", &self.chunk)
                .field("summary", &self.summary)
                .finish()
        } else {
            write!(f, "{:?} — {:?}", self.chunk, self.summary)
        }
    }
}

impl<Chunk: Summarize> Leaf<Chunk> {
    pub fn from_chunk(chunk: Chunk) -> Self {
        Self { summary: chunk.summarize(), chunk }
    }
}
