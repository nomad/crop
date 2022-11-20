//! A B-tree implementation.

mod iterators;
mod metric;
mod node;
mod node_internal;
mod node_leaf;
mod tree;
mod tree_slice;

pub use iterators::{Leaves, Units};
pub use metric::Metric;
use node::Node;
use node_internal::Inode;
pub use tree::{Leaf, Summarize, Tree};
pub use tree_slice::TreeSlice;
