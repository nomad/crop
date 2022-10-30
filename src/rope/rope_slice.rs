use super::{TextChunk, ROPE_FANOUT};
use crate::tree::TreeSlice;

pub struct RopeSlice<'a> {
    pub(super) tree_slice: TreeSlice<'a, ROPE_FANOUT, TextChunk>,
}

impl<'a> RopeSlice<'a> {
    pub fn byte_len(&self) -> usize {
        self.tree_slice.summary().bytes
    }
}
