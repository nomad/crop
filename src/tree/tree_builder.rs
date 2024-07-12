use alloc::vec::Vec;

use super::traits::{BalancedLeaf, Leaf};
use super::{Arc, Inode, Lnode, Node, Tree};

/// An incremental [`Tree`] builder.
#[derive(Clone)]
pub struct TreeBuilder<const ARITY: usize, L: Leaf> {
    /// A stack of internal nodes.
    ///
    /// # Invariants
    ///
    /// - all the nodes at every stack level are internal nodes;
    ///
    /// - all the inodes within a stack level have the same depth;
    ///
    /// - all the vectors at every stack level have a length strictly less than
    ///   `ARITY` (but it could also be zero, i.e. all levels except the first
    ///   one can be empty);
    ///
    /// - the inodes are grouped in order of descending depth, with each stack
    ///   level containing inodes of depth one less than the previous level;
    ///
    /// - every inode at every stack level is completely full, i.e. for every
    ///   inode it holds `inode.leaf_count() == max_children ^ inode.depth()`;
    ///
    /// - all the inodes in the last stack level (assuming there are any) have
    ///   a depth of 1.
    stack: Vec<Vec<Arc<Node<ARITY, L>>>>,

    /// A bunch of leaves waiting to be grouped into an internal node.
    leaves: Vec<Arc<Node<ARITY, L>>>,
}

impl<const ARITY: usize, L: Leaf> Default for TreeBuilder<ARITY, L> {
    #[inline]
    fn default() -> Self {
        Self { stack: Vec::new(), leaves: Vec::with_capacity(ARITY) }
    }
}

impl<const ARITY: usize, L: Leaf> TreeBuilder<ARITY, L> {
    #[inline]
    pub fn append(&mut self, leaf: L) {
        debug_assert!(self.leaves.len() < ARITY);

        self.leaves.push(Arc::new(Node::Leaf(Lnode::from(leaf))));

        if self.leaves.len() < ARITY {
            return;
        }

        let mut inode = Arc::new(Node::Internal(Inode::from_children(
            self.leaves.drain(..),
        )));

        let mut stack_idx = match self.stack.len() {
            0 => {
                let mut first_level = Vec::with_capacity(ARITY);
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

            debug_assert!(stack_level.len() < ARITY);

            stack_level.push(inode);

            if stack_level.len() < ARITY {
                return;
            }

            inode = Arc::new(Node::Internal(Inode::from_children(
                stack_level.drain(..),
            )));

            if stack_idx == 0 {
                stack_level.push(inode);
                self.stack.push(Vec::with_capacity(ARITY));

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

    /// Completes the build and outputs the final `Tree`, consuming `self`.
    #[inline]
    pub fn build(mut self) -> Tree<ARITY, L>
    where
        L: Default + BalancedLeaf + Clone,
    {
        if self.stack.is_empty() {
            if self.leaves.is_empty() {
                // No internal nodes on the stack and no leaves, this means
                // that `append` has never been called and we're building an
                // empty Tree. This is why we need the `Default` bound on `L`.
                return Tree::default();
            } else if self.leaves.len() == 1 {
                return Tree { root: self.leaves.into_iter().next().unwrap() };
            }
        }

        let mut root = if !self.leaves.is_empty() {
            debug_assert!(self.leaves.len() < ARITY);
            Arc::new(Node::Internal(Inode::from_children(self.leaves)))
        } else {
            loop {
                let stack_level = self.stack.pop().unwrap();

                match stack_level.len() {
                    0 => continue,

                    1 if self.stack.is_empty() => {
                        // The stack is now empty and there was a single node
                        // in its first level. That node is the root.
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

            debug_assert!(stack_level.len() < ARITY);

            stack_level.push(root);

            root = Arc::new(Node::Internal(Inode::from_children(stack_level)));
        }

        {
            // The only way the root can be a leaf node is if the stack is
            // empty and `self.leaves` contains a single leaf, and that case
            // was handled at the start of this function.
            let root = Arc::get_mut(&mut root).unwrap().get_internal_mut();

            root.balance_right_side();
        }

        Node::replace_with_single_child(&mut root);

        Tree { root }
    }

    #[allow(dead_code)]
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
