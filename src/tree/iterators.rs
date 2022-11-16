use std::collections::VecDeque;

use super::tree_slice::NodeOrSlicedLeaf;
use super::{Leaf, Metric, Node, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
pub struct Leaves<'a, const FANOUT: usize, L: Leaf> {
    stack: VecDeque<NodeOrSlicedLeaf<'a, FANOUT, L>>,
}

impl<'a, const FANOUT: usize, L: Leaf> Clone for Leaves<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self { stack: self.stack.clone() }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Leaves<'a, FANOUT, L> {
    #[inline]
    pub(super) fn from_stack<I>(slices: I) -> Self
    where
        I: IntoIterator<Item = NodeOrSlicedLeaf<'a, FANOUT, L>>,
    {
        Self { stack: slices.into_iter().collect() }
    }

    pub(super) fn new() -> Self {
        Self { stack: VecDeque::new() }
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

impl<'a, const FANOUT: usize, L: Leaf> Iterator for Leaves<'a, FANOUT, L> {
    type Item = &'a L::Slice;

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            return None;
        }

        loop {
            match self.stack.pop_front()? {
                NodeOrSlicedLeaf::Whole(Node::Leaf(leaf)) => {
                    return Some(leaf.value().borrow())
                },

                NodeOrSlicedLeaf::Sliced(slice, _) => return Some(slice),

                NodeOrSlicedLeaf::Whole(Node::Internal(inode)) => {
                    let mut idx = 0;
                    for child in inode.children() {
                        self.stack
                            .insert(idx, NodeOrSlicedLeaf::Whole(&**child));
                        idx += 1;
                    }
                },
            }
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'a, FANOUT, L>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
        // if self.start == self.end {
        //     None
        // } else {
        //     self.end -= 1;
        //     Some(&self.leaves[self.end])
        // }
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
