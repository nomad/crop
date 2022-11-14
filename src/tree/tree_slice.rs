use std::borrow::Cow;
use std::ops::Range;

use super::{Chops, Leaf, Leaves, Metric, Node, Summarize};

/// TODO: docs
#[derive(Debug, Copy)]
pub(super) enum NodeOrSlicedLeaf<'a, const N: usize, L: Leaf> {
    /// No slicing was needed so we can reuse a reference to the original node.
    Whole(&'a Node<N, L>),

    /// We had to slice a leaf, getting an owned value.
    Sliced(&'a L::Slice, L::Summary),
}

// FIXME: Why can't I derive this?
impl<'a, const N: usize, L: Leaf> Clone for NodeOrSlicedLeaf<'a, N, L> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Self::Whole(node) => Self::Whole(*node),

            Self::Sliced(slice, summary) => {
                Self::Sliced(*slice, summary.clone())
            },
        }
    }
}

impl<'a, const N: usize, L: Leaf> NodeOrSlicedLeaf<'a, N, L> {
    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        match self {
            Self::Whole(node) => node.summary(),
            Self::Sliced(_slice, summary) => &summary,
        }
    }
}

/// TODO: docs
#[derive(Debug)]
pub struct TreeSlice<'a, const FANOUT: usize, L: Leaf> {
    nodes: Vec<NodeOrSlicedLeaf<'a, FANOUT, L>>,
    summary: L::Summary,
}

// FIXME: Why can't I derive this?
impl<'a, const FANOUT: usize, L: Leaf> Clone for TreeSlice<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self { nodes: self.nodes.clone(), summary: self.summary.clone() }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> TreeSlice<'a, FANOUT, L> {
    /// TODO: docs
    #[inline]
    pub fn chops<M>(&'a self) -> Chops<'a, FANOUT, L, M>
    where
        M: Metric<L>,
    {
        Chops::from_stack(self.nodes.iter().map(Clone::clone))
    }

    /// TODO: docs
    pub(super) fn empty() -> Self {
        Self { nodes: Vec::new(), summary: L::Summary::default() }
    }

    /// TODO: docs
    pub(super) fn from_single_node(node: &'a Node<FANOUT, L>) -> Self {
        let nodes = match node {
            Node::Leaf(leaf) => {
                // TODO: this shouldn't work like this.
                vec![NodeOrSlicedLeaf::Sliced(
                    leaf.value().borrow(),
                    leaf.summary().clone(),
                )]
            },

            Node::Internal(inode) => inode
                .children()
                .into_iter()
                .map(|n| NodeOrSlicedLeaf::Whole(&**n))
                .collect(),
        };

        Self { summary: node.summary().clone(), nodes }
    }

    /// TODO: docs
    pub(super) fn from_range_in_node<M>(
        node: &'a Node<FANOUT, L>,
        range: Range<M>,
    ) -> Self
    where
        M: Metric<L>,
    {
        let (nodes, summary) = sumzing(node, range);
        Self { nodes, summary }
    }

    /// TODO: docs
    pub fn leaves(&'a self) -> Leaves<'a, L> {
        let mut leaves = Leaves::new();
        for node_or_leaf in &self.nodes {
            match node_or_leaf {
                NodeOrSlicedLeaf::Whole(node) => {
                    leaves.push_node_subtree(node)
                },
                NodeOrSlicedLeaf::Sliced(slice, _summary) => {
                    leaves.push_leaf(slice)
                },
            }
        }
        leaves
    }

    /// Creates a [`TreeSlice`] from the final vector of nodes and their total
    /// summary. Used in the implementation of [`Chops::next`].
    #[inline]
    pub(super) fn new(
        nodes: Vec<NodeOrSlicedLeaf<'a, FANOUT, L>>,
        summary: L::Summary,
    ) -> Self {
        Self { nodes, summary }
    }

    /// TODO: docs
    #[inline]
    pub fn slice<M>(&'a self, range: Range<M>) -> TreeSlice<'a, FANOUT, L>
    where
        M: Metric<L>,
    {
        assert!(M::zero() <= range.start);
        assert!(range.start <= range.end);
        assert!(range.end <= M::measure(self.summary()));

        if range.start == range.end {
            Self::empty()
        } else if M::measure(self.summary()) == range.end - range.start {
            self.clone()
        } else {
            let (nodes, summary) =
                sumzong(self.nodes.iter().map(Cow::Borrowed), range);
            Self { nodes, summary }
        }
    }

    /// TODO: docs
    pub fn summary(&self) -> &L::Summary {
        &self.summary
    }
}

/// TODO: docs
fn sumzing<'a, const N: usize, L, M>(
    mut node: &'a Node<N, L>,
    mut range: Range<M>,
) -> (Vec<NodeOrSlicedLeaf<'a, N, L>>, L::Summary)
where
    L: Leaf,
    M: Metric<L>,
{
    'outer: loop {
        match node {
            Node::Internal(inode) => {
                let mut measured = M::zero();
                for child in inode.children() {
                    let size = M::measure(child.summary());
                    if range.start >= measured && range.end <= measured + size
                    {
                        range.start -= measured;
                        range.end -= measured;
                        node = &*child;
                        continue 'outer;
                    } else {
                        measured += size;
                    }
                }
                // If none of the inode's children fully contained the range
                // then the inode itself must be the deepest node that fully
                // contains the range, so we're done.
                let nodes = inode
                    .children()
                    .iter()
                    .map(|n| Cow::Owned(NodeOrSlicedLeaf::Whole(&**n)));

                return sumzong(nodes, range);
            },

            Node::Leaf(leaf) => {
                // If the leaf's size is perfectly equal to the width of the
                // range we return the leaf's value. If not then the range is
                // strictly smaller than the leaf and the latter *must* be
                // sliceable by `M`.

                // TODO: this should be handled in the previous iteration.
                if M::measure(leaf.summary()) == range.end - range.start {
                    return (
                        vec![NodeOrSlicedLeaf::Whole(node)],
                        leaf.summary().clone(),
                    );
                } else {
                    let slice = M::slice(leaf.value().borrow(), range);
                    let summary = slice.summarize();
                    return (
                        vec![NodeOrSlicedLeaf::Sliced(slice, summary.clone())],
                        summary,
                    );
                }
            },
        }
    }
}

/// TODO: docs (nodes should be > 1)
fn sumzong<'a, const N: usize, I, L, M>(
    nodes: I,
    range: Range<M>,
) -> (Vec<NodeOrSlicedLeaf<'a, N, L>>, L::Summary)
where
    L: Leaf,
    M: Metric<L>,
    I: IntoIterator<Item = Cow<'a, NodeOrSlicedLeaf<'a, N, L>>>,
{
    let mut iter = nodes.into_iter();
    let mut measured = M::zero();

    let mut nodes = Vec::new();
    let mut summary = L::Summary::default();

    while let Some(node) = iter.next() {
        let size = M::measure(node.summary());
        if measured + size > range.start {
            nodes_from_start(
                node.into_owned(),
                range.start - measured,
                &mut nodes,
                &mut summary,
                &mut M::zero(),
                &mut false,
            );
            measured += size;
            break;
        } else {
            measured += size;
        }
    }

    while let Some(node) = iter.next() {
        let size = M::measure(node.summary());
        if measured + size >= range.end {
            nodes_to_end(
                node.into_owned(),
                range.end - measured,
                &mut nodes,
                &mut summary,
                &mut M::zero(),
                &mut false,
            );
            break;
        } else {
            summary += node.summary();
            nodes.push(node.into_owned());
            measured += size;
        }
    }

    (nodes, summary)
}

/// TODO: docs
fn nodes_from_start<'a, const N: usize, L, M>(
    node: NodeOrSlicedLeaf<'a, N, L>,
    start: M,
    vec: &mut Vec<NodeOrSlicedLeaf<'a, N, L>>,
    summary: &mut L::Summary,
    measured: &mut M,
    found_start: &mut bool,
) where
    L: Leaf,
    M: Metric<L>,
{
    let slice = match node {
        NodeOrSlicedLeaf::Whole(Node::Internal(inode)) => {
            for child in
                inode.children().iter().map(|n| NodeOrSlicedLeaf::Whole(&**n))
            {
                if *found_start {
                    *summary += child.summary();
                    vec.push(child);
                    continue;
                }
                if start == *measured {
                    *summary += child.summary();
                    vec.push(child);
                    *found_start = true;
                    continue;
                }
                let size = M::measure(child.summary());
                if *measured + size > start {
                    nodes_from_start(
                        child,
                        start,
                        vec,
                        summary,
                        measured,
                        found_start,
                    );
                } else {
                    *measured += size;
                }
            }
            return;
        },

        NodeOrSlicedLeaf::Whole(Node::Leaf(leaf)) => leaf.value().borrow(),

        NodeOrSlicedLeaf::Sliced(slice, _summary) => slice,
    };

    let (_, slice) = M::split_right(slice, start - *measured);
    let summ = slice.summarize();
    *summary += &summ;
    vec.push(NodeOrSlicedLeaf::Sliced(slice, summ));
    *found_start = true;
}

/// TODO: docs
fn nodes_to_end<'a, const N: usize, L, M>(
    node: NodeOrSlicedLeaf<'a, N, L>,
    end: M,
    vec: &mut Vec<NodeOrSlicedLeaf<'a, N, L>>,
    summary: &mut L::Summary,
    measured: &mut M,
    found_end: &mut bool,
) where
    L: Leaf,
    M: Metric<L>,
{
    let (slice, orig_summary) = match node {
        NodeOrSlicedLeaf::Whole(Node::Internal(inode)) => {
            for child in
                inode.children().iter().map(|n| NodeOrSlicedLeaf::Whole(&**n))
            {
                if *found_end {
                    return;
                }
                let size = M::measure(child.summary());
                if end == *measured + size {
                    *summary += child.summary();
                    vec.push(child);
                    *found_end = true;
                    return;
                }
                if *measured + size >= end {
                    nodes_to_end(
                        child, end, vec, summary, measured, found_end,
                    );
                } else {
                    *summary += child.summary();
                    vec.push(child);
                    *measured += size;
                }
            }
            return;
        },

        NodeOrSlicedLeaf::Whole(Node::Leaf(leaf)) => {
            (leaf.value().borrow(), leaf.summary())
        },

        NodeOrSlicedLeaf::Sliced(slice, ref summary) => (slice, summary),
    };

    let (slice, summ, _, _) =
        M::split_left(slice, end - *measured, orig_summary);

    let summ = summ.unwrap_or(slice.summarize());
    *summary += &summ;
    vec.push(NodeOrSlicedLeaf::Sliced(slice, summ));

    *found_end = true;
}
