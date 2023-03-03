use super::rope::RopeChunk;
use super::Rope;
use crate::tree::TreeBuilder;

/// An incremental [`Rope`](crate::Rope) builder.
#[derive(Clone, Default)]
pub struct RopeBuilder {
    tree_builder: TreeBuilder<{ Rope::fanout() }, RopeChunk>,
    buffer: RopeChunk,
    rope_has_trailing_newline: bool,
}

impl RopeBuilder {
    /// Appends `text` to the end of the `Rope` being built.
    #[inline]
    pub fn append<T>(&mut self, text: T) -> &mut Self
    where
        T: AsRef<str>,
    {
        let mut text = text.as_ref();

        while let Some(rest) = self.buffer.push_with_remainder(text) {
            debug_assert!(!rest.is_empty());
            self.tree_builder.append(std::mem::take(&mut self.buffer));
            text = rest;
        }

        self.rope_has_trailing_newline = self.buffer.has_trailing_newline();

        self
    }

    /// Completes the build, consuming the `RopeBuilder` and returning the
    /// `Rope`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use crop::{Rope, RopeBuilder};
    /// #
    /// let mut builder = RopeBuilder::new();
    ///
    /// builder.append("ƒoo\n").append("bär\r\n").append("baz");
    ///
    /// let rope: Rope = builder.build();
    ///
    /// assert_eq!(rope, "ƒoo\nbär\r\nbaz");
    /// ```
    #[inline]
    pub fn build(mut self) -> Rope {
        if !self.buffer.is_empty() {
            self.rope_has_trailing_newline =
                self.buffer.has_trailing_newline();

            self.tree_builder.append(self.buffer);
        }

        Rope {
            tree: self.tree_builder.build(),
            has_trailing_newline: self.rope_has_trailing_newline,
        }
    }

    /// Creates a new `RopeBuilder`.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
