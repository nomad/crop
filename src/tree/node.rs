use std::fmt::{self, Debug};

use super::{Inode, Summarize};

pub(super) enum Node<const N: usize, Leaf: Summarize> {
    Internal(Inode<N, Leaf>),
    Leaf(super::Leaf<Leaf>),
}

impl<const N: usize, Leaf: Summarize> Debug for Node<N, Leaf> {
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

impl<const N: usize, Leaf: Summarize> Node<N, Leaf> {
    pub(super) fn as_inode(&self) -> Option<&Inode<N, Leaf>> {
        match self {
            Node::Internal(inode) => Some(inode),
            Node::Leaf(_) => None,
        }
    }

    pub(super) fn as_leaf(&self) -> Option<&super::Leaf<Leaf>> {
        match self {
            Node::Internal(_) => None,
            Node::Leaf(leaf) => Some(leaf),
        }
    }

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
    pub(super) fn summary(&self) -> &Leaf::Summary {
        match self {
            Node::Internal(inode) => inode.summary(),
            Node::Leaf(leaf) => leaf.summary(),
        }
    }
}
