//! A utf-8 text rope built on top of a [`Tree`](crate::Tree).

mod metrics;
mod rope;
mod rope_slice;
mod text_chunk;

use metrics::ByteMetric;
pub use rope::Rope;
pub use rope_slice::RopeSlice;
use text_chunk::{TextChunk, TextChunkIter, TextSummary};

const ROPE_FANOUT: usize = 8;
