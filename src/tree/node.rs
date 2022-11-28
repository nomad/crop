use super::{Inode, Leaf};

pub(super) enum Node<const N: usize, L: Leaf> {
    Internal(Inode<N, L>),
    Leaf(super::node_leaf::Leaf<L>),
}

impl<const N: usize, L: Leaf + Default> Default for Node<N, L> {
    #[inline]
    fn default() -> Self {
        Node::Leaf(super::node_leaf::Leaf::default())
    }
}

impl<const N: usize, L: Leaf> std::fmt::Debug for Node<N, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            match self {
                Self::Internal(inode) => {
                    f.debug_tuple("Internal").field(&inode).finish()
                },
                Self::Leaf(leaf) => {
                    f.debug_tuple("Leaf").field(&leaf).finish()
                },
            }
        } else {
            match self {
                Self::Internal(inode) => write!(f, "{:#?}", inode),
                Self::Leaf(leaf) => write!(f, "{:#?}", leaf),
            }
        }
    }
}

impl<const N: usize, L: Leaf> Node<N, L> {
    pub(super) unsafe fn as_internal_unchecked(&self) -> &Inode<N, L> {
        debug_assert!(
            self.is_internal(),
            "A node was expected to be an internal node but it's a leaf. This \
            is a logic bug in crop. Please file an issue at \
            https://github.com/noib3/crop."
        );

        match self {
            Node::Leaf(_) => std::hint::unreachable_unchecked(),
            Node::Internal(inode) => inode,
        }
    }

    pub(super) unsafe fn as_leaf_unchecked(
        &self,
    ) -> &super::node_leaf::Leaf<L> {
        debug_assert!(
            self.is_leaf(),
            "A node was expected to be a leaf but it's an internal node. This \
            is a logic bug in crop. Please file an issue at \
            https://github.com/noib3/crop."
        );

        match self {
            Node::Leaf(leaf) => leaf,
            Node::Internal(_) => std::hint::unreachable_unchecked(),
        }
    }

    pub(super) fn depth(&self) -> usize {
        match self {
            Node::Internal(inode) => inode.depth(),
            Node::Leaf(_) => 0,
        }
    }

    pub(super) fn leaves(&self) -> usize {
        match self {
            Node::Internal(inode) => inode.leaves(),
            Node::Leaf(_) => 1,
        }
    }

    pub(super) fn is_internal(&self) -> bool {
        matches!(self, Node::Internal(_))
    }

    pub(super) fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }

    pub(super) fn summary(&self) -> &L::Summary {
        match self {
            Node::Internal(inode) => inode.summary(),
            Node::Leaf(leaf) => leaf.summary(),
        }
    }
}
