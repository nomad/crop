use super::utils::*;
use super::{Rope, RopeChunk};
use crate::tree::TreeBuilder;

/// TODO: docs
#[derive(Clone, Default)]
pub struct RopeBuilder {
    tree_builder: TreeBuilder<{ Rope::fanout() }, RopeChunk>,
    buffer: RopeChunk,
    last_byte_is_newline: bool,
}

impl RopeBuilder {
    /// TODO: docs
    #[inline]
    pub fn append<T>(mut self, text: T) -> Self
    where
        T: AsRef<str>,
    {
        let mut text = text.as_ref();

        loop {
            let (to_add, rest) = rope_chunk_append(&self.buffer, text);
            self.buffer.push_str(to_add);
            if rest.is_empty() {
                // TODO: this panics if `to_add` is empty.
                self.last_byte_is_newline = last_byte_is_newline(to_add);
                break;
            } else {
                text = rest;
                self.tree_builder.append(std::mem::take(&mut self.buffer));
            }
        }

        self
    }

    /// TODO: docs
    #[inline]
    pub fn build(mut self) -> Rope {
        if !self.buffer.is_empty() {
            self.last_byte_is_newline = last_byte_is_newline(&self.buffer);
            self.tree_builder.append(self.buffer);
        }

        Rope {
            tree: self.tree_builder.build(),
            last_byte_is_newline: self.last_byte_is_newline,
        }
    }

    /// TODO: docs
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
