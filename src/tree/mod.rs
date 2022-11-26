//! A self-balancing tree with metadata stored in each node.

mod iterators;
mod node;
mod node_internal;
mod node_leaf;
mod traits;
mod tree;
mod tree_slice;

pub use iterators::{Leaves, Units};
use node::Node;
use node_internal::Inode;
pub use traits::{Leaf, Metric, Summarize};
pub use tree::Tree;
pub use tree_slice::TreeSlice;
