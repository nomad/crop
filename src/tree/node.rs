use std::fmt::{self, Debug};

use super::{Inode, Leaf};

pub(super) enum Node<const N: usize, L: Leaf> {
    Internal(Inode<N, L>),
    Leaf(super::node_leaf::Leaf<L>),
}

impl<const N: usize, L: Leaf> Debug for Node<N, L> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
    // pub(super) fn as_inode(&self) -> Option<&Inode<N, Leaf>> {
    //     match self {
    //         Node::Internal(inode) => Some(inode),
    //         Node::Leaf(_) => None,
    //     }
    // }

    // pub(super) fn as_leaf(&self) -> Option<&super::Leaf<Leaf>> {
    //     match self {
    //         Node::Internal(_) => None,
    //         Node::Leaf(leaf) => Some(leaf),
    //     }
    // }

    pub(super) fn depth(&self) -> usize {
        match self {
            Node::Internal(inode) => inode.depth(),
            Node::Leaf(_) => 0,
        }
    }

    pub(super) fn is_internal(&self) -> bool {
        matches!(self, Node::Internal(_))
    }

    pub(super) fn _is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }

    /// TODO: docs
    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        match self {
            Node::Internal(inode) => inode.summary(),
            Node::Leaf(leaf) => leaf.summary(),
        }
    }

    pub(super) unsafe fn as_leaf_unchecked(
        &self,
    ) -> &super::node_leaf::Leaf<L> {
        match self {
            Node::Leaf(leaf) => leaf,
            Node::Internal(_) => std::hint::unreachable_unchecked(),
        }
    }
}
