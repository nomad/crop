//! A utf-8 text rope built on top of a [`Tree`](crate::Tree).

mod iterators;
mod metrics;
mod rope;
mod rope_slice;
mod text_chunk;

use iterators::Chunks;
use metrics::ByteMetric;
pub use rope::Rope;
use rope::ROPE_FANOUT;
pub use rope_slice::RopeSlice;
use text_chunk::{TextChunk, TextChunkIter, TextSummary};
