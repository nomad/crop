use std::sync::Arc;

use smallvec::SmallVec;

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
    /// - all the vectors at every stack level have a length strictly less
    /// than `FANOUT` (but it could also be zero, i.e. all levels except the
    /// first one can be empty);
    ///
    /// - the inodes are grouped in order of descending depth, with each stack
    /// level containing inodes of height one less than the previous level.
    /// That is, for every `i` in `0..stack.len() - 1`, it holds
    /// `stack[i][0].depth() = 1 + stack[i + 1][0].depth()` (assuming that both
    /// `stack[i]` and `stack[i + 1]` are not empty);
    ///
    /// - every inode at every stack level is completely full, that is...
    ///
    /// - the inodes in the last stack level (assuming there are any) always
    /// have a depth of 1.
    stack: Vec<SmallVec<[Arc<Node<FANOUT, L>>; FANOUT]>>,

    /// A bunch of leaves waiting to be grouped into an internal node.
    ///
    /// # Invariants
    ///
    /// - `leaves.len() < FANOUT`.
    leaves: SmallVec<[Arc<Node<FANOUT, L>>; FANOUT]>,
}

impl<const FANOUT: usize, L: Leaf> Default for TreeBuilder<FANOUT, L> {
    #[inline]
    fn default() -> Self {
        Self { stack: Vec::new(), leaves: SmallVec::with_capacity(FANOUT) }
    }
}

impl<const FANOUT: usize, L: Leaf> TreeBuilder<FANOUT, L> {
    /// TODO: docs
    #[inline]
    pub fn append(&mut self, leaf: L) {
        debug_assert!(self.leaves.len() < FANOUT);

        self.leaves.push(Arc::new(Node::Leaf(Lnode::from(leaf))));

        if self.leaves.len() < FANOUT {
            return;
        }

        let mut inode = Arc::new(Node::Internal(Inode::from_children(
            self.leaves.drain(..),
        )));

        let mut stack_idx = match self.stack.len() {
            0 => {
                let mut first_level = SmallVec::with_capacity(FANOUT);
                first_level.push(inode);
                self.stack.push(first_level);
                return;
            },

            n => n - 1,
        };

        loop {
            let stack_level = &mut self.stack[stack_idx];

            debug_assert!(
                stack_level.is_empty()
                    || stack_level[0].depth() == inode.depth()
            );

            debug_assert!(stack_level.len() < FANOUT);

            stack_level.push(inode);

            if stack_level.len() < FANOUT {
                return;
            }

            inode = Arc::new(Node::Internal(Inode::from_children(
                stack_level.drain(..),
            )));

            if stack_idx == 0 {
                stack_level.push(inode);
                self.stack.push(SmallVec::with_capacity(FANOUT));

                #[cfg(debug_assertions)]
                for level in &self.stack[1..] {
                    debug_assert!(level.is_empty());
                }

                return;
            } else {
                stack_idx -= 1;
            }
        }
    }

    /// TODO: docs
    #[inline]
    pub fn build(mut self) -> Tree<FANOUT, L>
    where
        L: Default,
    {
        if self.stack.is_empty() {
            if self.leaves.len() == 0 {
                // No internal nodes on the stack and no leaves, this means
                // that `append` has never been called and we're building an
                // empty Tree. This is why we need the `Default` bound on `L`.
                return Tree::default();
            } else if self.leaves.len() == 1 {
                return Tree { root: self.leaves.into_iter().next().unwrap() };
            }
        }

        let mut root = if !self.leaves.is_empty() {
            debug_assert!(self.leaves.len() < FANOUT);
            Arc::new(Node::Internal(Inode::from_children(self.leaves)))
        } else {
            loop {
                // TODO: explain why we can unwrap
                let stack_level = self.stack.pop().unwrap();

                match stack_level.len() {
                    0 => continue,

                    1 if self.stack.is_empty() => {
                        // TODO: explain this edge case
                        break stack_level.into_iter().next().unwrap();
                    },

                    _ => {
                        break Arc::new(Node::Internal(Inode::from_children(
                            stack_level,
                        )))
                    },
                }
            }
        };

        while let Some(mut stack_level) = self.stack.pop() {
            debug_assert!(
                stack_level.is_empty()
                    || stack_level[0].depth() == root.depth()
            );

            debug_assert!(stack_level.len() < FANOUT);

            stack_level.push(root);

            root = Arc::new(Node::Internal(Inode::from_children(stack_level)));
        }

        Tree { root }
    }

    #[allow(dead_code)]
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
