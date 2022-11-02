//! A B-tree implementation.

mod iterators;
mod metric;
mod node;
mod node_internal;
mod node_leaf;
mod tree;
mod tree_slice;

pub use iterators::Leaves;
pub use metric::Metric;
use node::Node;
use node_internal::{Inode, LeafCoordinates};
use node_leaf::Leaf;
pub use tree::{Summarize, Tree};
pub use tree_slice::TreeSlice;
