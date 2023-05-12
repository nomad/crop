use super::gap_buffer::GapBuffer;
use super::rope::RopeChunk;
use super::utils::{count_line_breaks, split_adjusted};
use super::Rope;
use crate::tree::TreeBuilder;

/// An incremental [`Rope`](crate::Rope) builder.
#[derive(Clone, Default)]
pub struct RopeBuilder {
    tree_builder: TreeBuilder<{ Rope::arity() }, RopeChunk>,
    buffer: RopeChunk,
    rope_has_trailing_newline: bool,
}

/// Pushes as mush of the slice as possible onto the left chunk of the gap
/// buffer, returning the rest (if any).
///
/// Note that this doesn't update the `line_breaks_left` field of the gap
/// buffer because it's faster to do it only once before passing the buffer to
/// the `TreeBuilder`.
#[inline]
fn gap_buffer_push_with_remainder<'a, const MAX_BYTES: usize>(
    buffer: &mut GapBuffer<MAX_BYTES>,
    s: &'a str,
) -> Option<&'a str> {
    debug_assert_eq!(buffer.len_right(), 0);

    let space_left = MAX_BYTES - buffer.len_left();
    let (push, rest) = split_adjusted::<false>(s, space_left);

    debug_assert!(push.len() <= space_left);

    let len_left = buffer.len_left();

    buffer.bytes[len_left..len_left + push.len()]
        .copy_from_slice(push.as_bytes());

    buffer.len_left += push.len() as u16;

    (!rest.is_empty()).then_some(rest)
}

impl RopeBuilder {
    /// Appends `text` to the end of the `Rope` being built.
    #[inline]
    pub fn append<T>(&mut self, text: T) -> &mut Self
    where
        T: AsRef<str>,
    {
        let mut text = text.as_ref();

        while let Some(rest) =
            gap_buffer_push_with_remainder(&mut self.buffer, text)
        {
            // `gap_buffer_push_with_remainder` doesn't update
            // `line_breaks_left`, so we do it here.
            self.buffer.line_breaks_left =
                count_line_breaks(self.buffer.left_chunk()) as u16;

            self.tree_builder.append(core::mem::take(&mut self.buffer));

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

            self.buffer.line_breaks_left =
                count_line_breaks(self.buffer.left_chunk()) as u16;

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
