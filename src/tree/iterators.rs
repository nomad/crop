use std::collections::VecDeque;
use std::sync::Arc;

use super::tree_slice::{NodeOrSlicedLeaf, SliceSpan};
use super::{Inode, Leaf, Metric, Node, Tree, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
pub struct Leaves<'a, const FANOUT: usize, L: Leaf> {
    /// TODO: docs
    start: Option<&'a L::Slice>,

    /// TODO: docs
    start_been_yielded: bool,

    /// TODO: docs
    root_nodes: &'a [Arc<Node<FANOUT, L>>],

    /// TODO: docs
    root_forward_idx: isize,

    /// TODO: docs
    end: Option<&'a L::Slice>,

    /// TODO: docs
    end_been_yielded: bool,

    /// TODO: docs
    forward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// TODO: docs
    leaves_forward: &'a [Arc<Node<FANOUT, L>>],

    leaf_forward_idx: usize,

    /// TODO: docs
    backward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// TODO: docs
    current_leaves_backward: (&'a [Arc<Node<FANOUT, L>>], usize),
}

impl<'a, const FANOUT: usize, L: Leaf> Clone for Leaves<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            forward_path: self.forward_path.clone(),
            backward_path: self.backward_path.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a Tree<FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Leaves<'a, FANOUT, L> {
        match &*tree.root {
            Node::Leaf(leaf) => Leaves {
                start: Some(leaf.value().borrow()),
                start_been_yielded: false,
                root_nodes: &[],
                end: None,
                end_been_yielded: true,
                forward_path: Vec::new(),
                root_forward_idx: -1,
                leaves_forward: &[],
                leaf_forward_idx: 0,
                backward_path: Vec::new(),
                current_leaves_backward: (&[], 0),
            },

            Node::Internal(inode) => Leaves {
                start: None,
                start_been_yielded: true,
                root_nodes: inode.children(),
                end: None,
                end_been_yielded: true,
                forward_path: Vec::new(),
                root_forward_idx: -1,
                leaves_forward: &[],
                leaf_forward_idx: 0,
                backward_path: Vec::new(),
                current_leaves_backward: (&[], 0),
            },
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a TreeSlice<'a, FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Leaves<'a, FANOUT, L> {
        let (start, start_been_yielded, root_nodes, end, end_been_yielded) =
            match &tree_slice.span {
                SliceSpan::Empty => (None, true, &[][..], None, true),

                SliceSpan::Single(slice) => {
                    (Some(*slice), false, &[][..], None, true)
                },

                SliceSpan::Multi { start, internals, end } => {
                    (Some(start.0), false, &**internals, Some(end.0), false)
                },
            };

        Leaves {
            start,
            start_been_yielded,
            root_nodes,
            end,
            end_been_yielded,
            forward_path: Vec::new(),
            root_forward_idx: -1,
            leaves_forward: &[],
            leaf_forward_idx: 0,
            backward_path: Vec::new(),
            current_leaves_backward: (&[], 0),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Iterator for Leaves<'a, FANOUT, L> {
    type Item = &'a L::Slice;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.start_been_yielded {
            self.start_been_yielded = true;
            if self.start.is_some() {
                return self.start;
            }
        }

        if self.leaf_forward_idx == self.leaves_forward.len() {
            match next_leaves_forward(
                self.root_nodes,
                &mut self.root_forward_idx,
                &mut self.forward_path,
            ) {
                Some(leaves) => {
                    self.leaves_forward = leaves;
                    self.leaf_forward_idx = 0;
                },
                None => {
                    if !self.end_been_yielded {
                        self.end_been_yielded = true;
                        return self.end;
                    } else {
                        return None;
                    }
                },
            }
        }

        let leaf = unsafe {
            self.leaves_forward[self.leaf_forward_idx].as_leaf_unchecked()
        }
        .value()
        .borrow();

        self.leaf_forward_idx += 1;

        Some(leaf)
    }
}

impl<'a, const FANOUT: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'a, FANOUT, L>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if !self.end_been_yielded {
            self.end_been_yielded = true;
            if self.end.is_some() {
                return self.end;
            }
        }
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> std::iter::FusedIterator
    for Leaves<'a, FANOUT, L>
{
}

/// An iterator over consecutive units of a particular metric.
///
/// This iterator will chop down a tree or a tree slice by hacking at it using
/// a metric.
pub struct Chops<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    stack: VecDeque<NodeOrSlicedLeaf<'a, FANOUT, L>>,
    metric: std::marker::PhantomData<M>,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
    for Chops<'a, FANOUT, L, M>
{
    fn clone(&self) -> Self {
        Self { stack: self.stack.clone(), metric: std::marker::PhantomData }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Chops<'a, FANOUT, L, M> {
    #[inline]
    pub(super) fn from_stack<I>(slices: I) -> Self
    where
        I: IntoIterator<Item = NodeOrSlicedLeaf<'a, FANOUT, L>>,
    {
        Self {
            stack: slices.into_iter().collect(),
            metric: std::marker::PhantomData,
        }
    }

    pub(super) fn new() -> Self {
        Self { stack: VecDeque::new(), metric: std::marker::PhantomData }
    }

    pub(super) fn append(&mut self, node: NodeOrSlicedLeaf<'a, FANOUT, L>) {
        self.stack.push_back(node);
    }

    pub(super) fn extend<I>(&mut self, nodes: I)
    where
        I: IntoIterator<Item = NodeOrSlicedLeaf<'a, FANOUT, L>>,
    {
        self.stack.extend(nodes);
    }
}

impl<'a, const FANOUT: usize, L: Leaf + 'a, M: Metric<L>> Iterator
    for Chops<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            return None;
        }

        let mut nodes = Vec::new();
        let mut summary = L::Summary::default();

        while let Some(first) = self.stack.pop_front() {
            if M::measure(first.summary()) == M::zero() {
                summary += first.summary();
                nodes.push(first);
            } else {
                sumzang::<FANOUT, L, M>(
                    first,
                    &mut self.stack,
                    &mut nodes,
                    &mut summary,
                    &mut false,
                    &mut 0,
                );
                break;
            }
        }

        todo!()
        // if nodes.len() == 1 {
        //     let single = nodes.into_iter().next().unwrap();
        //     match single {
        //         NodeOrSlicedLeaf::Sliced(slice, summary) => todo!(),
        //         _ => unreachable!(),
        //     }
        // } else if nodes.len() == 2 {
        //     let mut nodes = nodes.into_iter();
        //     let start = nodes.next().unwrap();
        //     let end = nodes.next().unwrap();
        //     let (start, st_summ) = match start {
        //         NodeOrSlicedLeaf::Sliced(slice, summary) => (slice, summary),
        //         _ => unreachable!(),
        //     };
        //     let (end, end_summ) = match end {
        //         NodeOrSlicedLeaf::Sliced(slice, summary) => (slice, summary),
        //         _ => unreachable!(),
        //     };
        // }
        // Some(TreeSlice::new(nodes, summary))
    }
}

fn sumzang<'a, const N: usize, L, M>(
    node: NodeOrSlicedLeaf<'a, N, L>,
    stack: &mut VecDeque<NodeOrSlicedLeaf<'a, N, L>>,
    out: &mut Vec<NodeOrSlicedLeaf<'a, N, L>>,
    summary: &mut L::Summary,
    appended_last: &mut bool,
    insert_idx: &mut usize,
) where
    L: Leaf,
    M: Metric<L>,
{
    let (slice, slice_summary) = match node {
        NodeOrSlicedLeaf::Whole(Node::Internal(inode)) => {
            for child in inode.children() {
                if *appended_last {
                    stack.insert(
                        *insert_idx,
                        NodeOrSlicedLeaf::Whole(&**child),
                    );
                    *insert_idx += 1;
                    continue;
                }
                if M::measure(child.summary()) == M::zero() {
                    *summary += child.summary();
                    out.push(NodeOrSlicedLeaf::Whole(&**child));
                } else {
                    sumzang::<N, L, M>(
                        NodeOrSlicedLeaf::Whole(&**child),
                        stack,
                        out,
                        summary,
                        appended_last,
                        insert_idx,
                    );
                }
            }

            return;
        },

        NodeOrSlicedLeaf::Whole(Node::Leaf(leaf)) => {
            (leaf.value().borrow(), leaf.summary())
        },

        NodeOrSlicedLeaf::Sliced(slice, ref summary) => (slice, summary),
    };

    let (left, left_summary, right) =
        M::split_left(slice, M::one(), slice_summary);

    *summary += &left_summary;
    out.push(NodeOrSlicedLeaf::Sliced(left, left_summary));

    if let Some((right, right_summary)) = right {
        stack.push_front(NodeOrSlicedLeaf::Sliced(right, right_summary));
        *insert_idx = 1;
    }

    *appended_last = true;
}

fn next_leaves_forward<'a, const N: usize, L: Leaf>(
    root_nodes: &'a [Arc<Node<N, L>>],
    root_idx: &mut isize,
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
) -> Option<&'a [Arc<Node<N, L>>]> {
    let mut inode = loop {
        match path.last_mut() {
            Some(&mut (inode, ref mut visited)) => {
                if inode.children().len() == *visited + 1 {
                    path.pop();
                    continue;
                } else {
                    *visited += 1;
                    match &*inode.children()[*visited] {
                        Node::Internal(inode) => {
                            break inode;
                        },
                        Node::Leaf(_) => {
                            unreachable!()
                        },
                    }
                }
            },

            None => {
                *root_idx += 1;
                if *root_idx as usize >= root_nodes.len() {
                    return None;
                } else {
                    match &*root_nodes[*root_idx as usize] {
                        Node::Internal(inode) => {
                            break inode;
                        },
                        Node::Leaf(_) => {
                            return Some(
                                &root_nodes[*root_idx as usize
                                    ..*root_idx as usize + 1],
                            );
                        },
                    }
                }
            },
        }
    };

    loop {
        match &*inode.children()[0] {
            Node::Internal(i) => {
                path.push((inode, 0));
                inode = i;
            },
            Node::Leaf(_) => {
                return Some(inode.children());
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaves_1() {
        for n in 1..100 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = 0;
            while let Some(leaf) = leaves.next() {
                assert_eq!(i, *leaf);
                i += 1;
            }
            assert_eq!(i, n);
            assert_eq!(None, leaves.next());
            assert_eq!(None, leaves.next());
        }
    }

    #[test]
    fn leaves_2() {
        let tree = Tree::<2, usize>::from_leaves(0..3);
        let mut leaves = tree.leaves();

        assert_eq!(Some(&2), leaves.next_back());
        assert_eq!(Some(&1), leaves.next_back());
        assert_eq!(Some(&0), leaves.next_back());
        assert_eq!(None, leaves.next_back());
        assert_eq!(None, leaves.next_back());
    }
}
