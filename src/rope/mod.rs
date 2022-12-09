//! A utf-8 text rope built on top of a [`Tree`](crate::tree::Tree).

pub(crate) mod iterators;
mod metrics;
mod rope;
mod rope_builder;
mod rope_chunk;
mod rope_slice;
mod utils;

pub use rope::Rope;
pub use rope_builder::RopeBuilder;
use rope_chunk::{ChunkSlice, ChunkSummary, RopeChunk, RopeChunkIter};
pub use rope_slice::RopeSlice;
