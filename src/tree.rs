//! A B-tree implementation.

use std::borrow::Cow;
use std::fmt;
use std::mem::MaybeUninit;
use std::ops::AddAssign;
use std::sync::Arc;

const INODE_MAX_CHILDREN: usize = 4;

pub trait Summarize: fmt::Debug {
    type Summary: for<'a> AddAssign<&'a Self::Summary> + Clone + Default;

    fn summarize(&self) -> Self::Summary;
}

pub struct Tree<Chunk: Summarize> {
    root: Arc<Node<Chunk>>,
}

enum Node<Chunk: Summarize> {
    Internal(Inode<Chunk>),
    Leaf(Leaf<Chunk>),
}

struct Inode<Chunk: Summarize> {
    summary: Chunk::Summary,
    children: [MaybeUninit<Arc<Node<Chunk>>>; INODE_MAX_CHILDREN],
    initialized: usize,
}

struct Leaf<Chunk: Summarize> {
    summary: Chunk::Summary,
    chunk: Chunk,
}

impl<Chunk: Summarize> Tree<Chunk> {
    pub fn summarize(&self) -> Cow<'_, Chunk::Summary> {
        self.root.summarize()
    }
}

impl<Chunk: Summarize> Node<Chunk> {
    fn summarize(&self) -> Cow<'_, Chunk::Summary> {
        match self {
            Node::Internal(inode) => {
                let mut nodes = inode.initialized();

                match (nodes.next(), nodes.next()) {
                    (Some(first), Some(second)) => {
                        let mut summary = first.summarize().into_owned();
                        summary += &*second.summarize();
                        for node in nodes {
                            summary += &*node.summarize();
                        }
                        Cow::Owned(summary)
                    },

                    (Some(first), None) => first.summarize(),

                    (None, Some(_)) => unreachable!(),

                    (None, None) => Cow::Owned(Chunk::Summary::default()),
                }
            },

            Node::Leaf(leaf) => Cow::Borrowed(&leaf.summary),
        }
    }
}

impl<Chunk: Summarize> Inode<Chunk> {
    /// Returns an iterator over the initialized children nodes.
    pub fn initialized(
        &self,
    ) -> impl ExactSizeIterator<Item = &'_ Node<Chunk>> + '_ {
        self.children[..self.initialized]
            .iter()
            .map(|node| &**unsafe { node.assume_init_ref() })
    }
}
