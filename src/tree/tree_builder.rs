use super::{Leaf, Tree};

#[derive(Clone)]
pub struct TreeBuilder<const FANOUT: usize, L: Leaf> {
    nodes: Vec<Vec<Tree<FANOUT, L>>>,
}

impl<const FANOUT: usize, L: Leaf> Default for TreeBuilder<FANOUT, L> {
    #[inline]
    fn default() -> Self {
        Self { nodes: Vec::new() }
    }
}

impl<const FANOUT: usize, L: Leaf> TreeBuilder<FANOUT, L> {
    /// TODO: docs
    #[inline]
    pub fn append(&mut self, leaf: L) {
        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn build(self) -> Tree<FANOUT, L> {
        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
