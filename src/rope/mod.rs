//! A utf-8 text rope built on top of a [`Tree`](crate::tree::Tree).

pub(crate) mod iterators;
mod metrics;
mod rope;
mod rope_slice;
mod text_chunk;
mod utils;

pub use rope::Rope;
pub use rope_slice::RopeSlice;
use text_chunk::{TextChunk, TextChunkIter, TextSummary};
