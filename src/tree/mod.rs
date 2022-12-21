//! A self-balancing tree with metadata stored in each node.

mod leaves;
mod node;
mod node_internal;
mod node_leaf;
mod traits;
mod tree;
mod tree_builder;
mod tree_slice;
mod units;

pub use leaves::Leaves;
use node::Node;
use node_internal::Inode;
pub use traits::{Leaf, Metric, Summarize};
pub use tree::Tree;
pub use tree_builder::TreeBuilder;
pub use tree_slice::TreeSlice;
pub use units::Units;
