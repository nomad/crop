use std::borrow::Cow;
use std::ops::Range;

use super::{Leaf, Leaves, Metric, Node, Summarize};

/// TODO: docs
#[derive(Debug, Clone)]
enum NodeOrSlicedLeaf<'a, const N: usize, L: Summarize> {
    /// No slicing was needed so we can reuse a reference to the original node.
    Whole(&'a Node<N, L>),

    /// We had to slice a leaf, getting an owned value.
    Sliced(Leaf<L>),
}

impl<'a, const N: usize, L: Summarize> NodeOrSlicedLeaf<'a, N, L> {
    fn summary(&self) -> &L::Summary {
        match self {
            Self::Whole(node) => node.summary(),
            Self::Sliced(leaf) => leaf.summary(),
        }
    }
}

/// TODO: docs
#[derive(Debug, Clone)]
pub struct TreeSlice<'a, const FANOUT: usize, Leaf: Summarize> {
    nodes: Vec<NodeOrSlicedLeaf<'a, FANOUT, Leaf>>,
    summary: Leaf::Summary,
}

impl<'a, const FANOUT: usize, Leaf: Summarize> TreeSlice<'a, FANOUT, Leaf> {
    /// TODO: docs
    pub(super) fn empty() -> Self {
        Self { nodes: Vec::new(), summary: Leaf::Summary::default() }
    }

    /// TODO: docs
    pub(super) fn from_single_node(node: &'a Node<FANOUT, Leaf>) -> Self {
        Self {
            summary: node.summary().clone(),
            nodes: vec![NodeOrSlicedLeaf::Whole(node)],
        }
    }

    /// TODO: docs
    pub(super) fn from_range_in_node<M>(
        node: &'a Node<FANOUT, Leaf>,
        range: Range<M>,
    ) -> Self
    where
        M: Metric<Leaf>,
    {
        let (nodes, summary) = sumzing(node, range);
        Self { nodes, summary }
    }

    /// TODO: docs
    pub fn leaves(&self) -> Leaves<'_, Leaf> {
        todo!()
    }

    /// TODO: docs
    pub fn slice<M>(&'a self, range: Range<M>) -> TreeSlice<'a, FANOUT, Leaf>
    where
        M: Metric<Leaf>,
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
    pub fn summary(&self) -> &Leaf::Summary {
        &self.summary
    }
}

/// TODO: docs
fn sumzing<'a, const N: usize, L, M>(
    mut node: &'a Node<N, L>,
    mut range: Range<M>,
) -> (Vec<NodeOrSlicedLeaf<'a, N, L>>, L::Summary)
where
    L: Summarize,
    M: Metric<L>,
{
    'outer: loop {
        match node {
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
                    let sliced = M::slice(leaf.value(), range);
                    let summary = sliced.summarize();
                    let leaf = Leaf::new(sliced, summary.clone());
                    return (vec![NodeOrSlicedLeaf::Sliced(leaf)], summary);
                }
            },

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
        }
    }
}

/// TODO: docs (nodes should be > 1)
fn sumzong<'a, const N: usize, I, L, M>(
    nodes: I,
    range: Range<M>,
) -> (Vec<NodeOrSlicedLeaf<'a, N, L>>, L::Summary)
where
    M: Metric<L>,
    L: Summarize,
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
    L: Summarize,
    M: Metric<L>,
{
    match node {
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
        },

        NodeOrSlicedLeaf::Whole(Node::Leaf(ref leaf))
        | NodeOrSlicedLeaf::Sliced(ref leaf) => {
            let start = start - *measured;
            let end = M::measure(leaf.summary()); // TODO: remove this
            let sliced = M::slice(leaf.value(), start..end);
            let summ = sliced.summarize();
            *summary += &summ;
            let leaf = Leaf::new(sliced, summ);
            vec.push(NodeOrSlicedLeaf::Sliced(leaf));
            *found_start = true;
            return;
        },
    };
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
    L: Summarize,
    M: Metric<L>,
{
    match node {
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
        },

        NodeOrSlicedLeaf::Whole(Node::Leaf(ref leaf))
        | NodeOrSlicedLeaf::Sliced(ref leaf) => {
            let start = M::zero(); // TODO: remove this
            let end = end - *measured;
            let sliced = M::slice(leaf.value(), start..end);
            let summ = sliced.summarize();
            *summary += &summ;
            let leaf = Leaf::new(sliced, summ);
            vec.push(NodeOrSlicedLeaf::Sliced(leaf));
            *found_end = true;
            return;
        },
    }
}
