#![feature(int_roundings)]
#![feature(iter_array_chunks)]
#![feature(iter_next_chunk)]

mod rope;
mod tree;

pub use rope::Rope;
pub use tree::{Summarize, Tree};
