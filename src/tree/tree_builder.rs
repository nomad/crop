use std::sync::Arc;

use super::{Inode, Leaf, Lnode, Node, Tree};

#[derive(Clone)]
pub struct TreeBuilder<const FANOUT: usize, L: Leaf> {
    /// A stack of internal nodes.
    ///
    /// # Invariants
    ///
    /// - all the inodes within a stack level have the same depth. That is, for
    /// every `i` in `0..stack.len()`, `j,k` in  `0..stack[i].len()`, it holds
    /// `stack[i][j].depth() = stack[i][k].depth()`;
    ///
    /// - all the vectors at every stack level have a length `<=` than `FANOUT`
    /// (but it could also be zero, i.e. all levels except the first one can be
    /// empty);
    ///
    /// - the inodes are grouped in order of descending depth, with each stack
    /// level containing inodes of height one less than the previous level.
    /// That is, for every `i` in `0..stack.len() - 1`, it holds
    /// `stack[i][0].depth() = 1 + stack[i + 1][0].depth()` (assuming that both
    /// `stack[i]` and `stack[i + 1]` are not empty);
    ///
    /// - every inode at every stack level is completely full, that is...
    stack: Vec<Vec<Inode<FANOUT, L>>>,

    /// A bunch of leaves waiting to be grouped into an internal node.
    ///
    /// # Invariants
    ///
    /// - `leaves.len() <= FANOUT`.
    leaves: Vec<Lnode<L>>,
}

impl<const FANOUT: usize, L: Leaf> Default for TreeBuilder<FANOUT, L> {
    #[inline]
    fn default() -> Self {
        Self { stack: Vec::new(), leaves: Vec::with_capacity(FANOUT) }
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
    pub fn build(mut self) -> Tree<FANOUT, L>
    where
        L: Default,
    {
        let mut root = match self.leaves.len() {
            0 => return Tree::default(),

            1 if self.stack.is_empty() => {
                let root = Node::Leaf(Lnode::from(
                    self.leaves.into_iter().next().unwrap(),
                ));

                return Tree { root: Arc::new(root) };
            },

            _ => Node::Internal(Inode::from_children(
                self.leaves.into_iter().map(|l| Arc::new(Node::Leaf(l))),
            )),
        };

        while let Some(inodes) = self.stack.pop() {
            if inodes.len() == FANOUT {
                todo!();
            } else {
                root = Node::Internal(Inode::from_children(
                    inodes
                        .into_iter()
                        .map(Node::Internal)
                        .chain(std::iter::once(root))
                        .map(Arc::new),
                ));
            }
        }

        Tree { root: Arc::new(root) }
    }

    /// TODO: docs
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
