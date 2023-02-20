use super::rope_chunk::RopeChunk;
use super::utils::*;
use super::Rope;
use crate::tree::TreeBuilder;

/// An incremental [`Rope`](crate::Rope) builder.
#[derive(Clone, Default)]
pub struct RopeBuilder {
    tree_builder: TreeBuilder<{ Rope::fanout() }, RopeChunk>,
    buffer: RopeChunk,
    last_byte_is_newline: bool,
}

impl RopeBuilder {
    /// TODO: docs
    #[inline]
    pub fn append<T>(&mut self, text: T) -> &mut Self
    where
        T: AsRef<str>,
    {
        let mut text = text.as_ref();

        loop {
            let rest = self.buffer.push_with_remainder(text.into());
            if rest.is_empty() {
                self.last_byte_is_newline = last_byte_is_newline(&self.buffer);
                break;
            } else {
                self.tree_builder.append(std::mem::take(&mut self.buffer));
                text = rest;
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

    /// Creates a new `RopeBuilder`.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
