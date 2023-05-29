pub(crate) mod gap_buffer;
pub(crate) mod gap_slice;
pub(crate) mod iterators;
pub mod metrics;
mod rope;
mod rope_builder;
mod rope_slice;
mod utils;

pub use rope::Rope;
pub use rope_builder::RopeBuilder;
pub use rope_slice::RopeSlice;
