//! A utf-8 text rope built on top of a [`Tree`](crate::Tree).

mod rope;
mod rope_slice;
mod text_chunk;

pub use rope::Rope;
pub use rope_slice::RopeSlice;
use text_chunk::{TextChunk, TextChunkIter};
