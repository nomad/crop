use std::collections::VecDeque;
use std::sync::Arc;

use super::tree_slice::SliceSpan;
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
        let (start, start_been_yielded, root_nodes) = match &*tree.root {
            Node::Leaf(leaf) => (Some(leaf.value().borrow()), false, &[][..]),
            Node::Internal(inode) => (None, true, inode.children()),
        };

        Leaves {
            start,
            start_been_yielded,
            root_nodes,
            end: None,
            end_been_yielded: true,
            forward_path: Vec::new(),
            root_forward_idx: -1,
            leaves_forward: &[],
            leaf_forward_idx: 0,
            backward_path: Vec::new(),
            current_leaves_backward: (&[], 0),
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

    #[inline]
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

///// TODO: docs
//#[derive(Debug, Copy)]
//enum NodeOrSlicedLeaf<'a, const N: usize, L: Leaf> {
//    /// No slicing was needed so we can reuse a reference to the original node.
//    Whole(&'a Arc<Node<N, L>>),

//    /// We had to slice a leaf, getting an owned value.
//    Sliced(&'a L::Slice, L::Summary),
//}

//impl<'a, const N: usize, L: Leaf> Clone for NodeOrSlicedLeaf<'a, N, L> {
//    #[inline]
//    fn clone(&self) -> Self {
//        match self {
//            Self::Whole(node) => Self::Whole(*node),

//            Self::Sliced(slice, summary) => {
//                Self::Sliced(*slice, summary.clone())
//            },
//        }
//    }
//}

//impl<'a, const N: usize, L: Leaf> NodeOrSlicedLeaf<'a, N, L> {
//    #[inline]
//    pub(super) fn summary(&self) -> &L::Summary {
//        match self {
//            Self::Whole(node) => node.summary(),
//            Self::Sliced(_slice, summary) => &summary,
//        }
//    }
//}
///// An iterator over consecutive units of a particular metric.
/////
///// This iterator will chop down a tree or a tree slice by hacking at it using
///// a metric.
//pub struct Unitas<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
//    stack: VecDeque<NodeOrSlicedLeaf<'a, FANOUT, L>>,
//    metric: std::marker::PhantomData<M>,
//}

//impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
//    for Unitas<'a, FANOUT, L, M>
//{
//    fn clone(&self) -> Self {
//        Self { stack: self.stack.clone(), metric: std::marker::PhantomData }
//    }
//}

//impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
//    for Unitas<'a, FANOUT, L, M>
//{
//    #[inline]
//    fn from(tree: &'a Tree<FANOUT, L>) -> Unitas<'a, FANOUT, L, M> {
//        let stack = match &*tree.root {
//            Node::Leaf(leaf) => {
//                let mut span = VecDeque::new();
//                span.push_back(NodeOrSlicedLeaf::Sliced(
//                    leaf.value().borrow(),
//                    leaf.summary().clone(),
//                ));
//                span
//            },

//            Node::Internal(inode) => {
//                inode.children().iter().map(NodeOrSlicedLeaf::Whole).collect()
//            },
//        };

//        Unitas { stack, metric: std::marker::PhantomData }
//    }
//}

//impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
//    From<&'a TreeSlice<'a, FANOUT, L>> for Unitas<'a, FANOUT, L, M>
//{
//    #[inline]
//    fn from(
//        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
//    ) -> Unitas<'a, FANOUT, L, M> {
//        let stack = match &tree_slice.span {
//            SliceSpan::Single(slice) => {
//                let mut span = VecDeque::new();
//                span.push_back(NodeOrSlicedLeaf::Sliced(
//                    *slice,
//                    tree_slice.summary().clone(),
//                ));
//                span
//            },

//            SliceSpan::Multi { start, internals, end } => {
//                let mut span = VecDeque::new();
//                span.push_back(NodeOrSlicedLeaf::Sliced(
//                    start.0,
//                    start.1.clone(),
//                ));
//                span.extend(internals.iter().map(NodeOrSlicedLeaf::Whole));
//                span.push_back(NodeOrSlicedLeaf::Sliced(end.0, end.1.clone()));
//                span
//            },

//            SliceSpan::Empty => VecDeque::new(),
//        };

//        Unitas { stack, metric: std::marker::PhantomData }
//    }
//}

//impl<'a, const FANOUT: usize, L: Leaf + 'a, M: Metric<L>> Iterator
//    for Unitas<'a, FANOUT, L, M>
//{
//    type Item = TreeSlice<'a, FANOUT, L>;

//    fn next(&mut self) -> Option<Self::Item> {
//        if self.stack.is_empty() {
//            return None;
//        }

//        let mut nodes = Vec::new();
//        let mut summary = L::Summary::default();

//        while let Some(first) = self.stack.pop_front() {
//            if M::measure(first.summary()) == M::zero() {
//                summary += first.summary();
//                nodes.push(first);
//            } else {
//                sumzang::<FANOUT, L, M>(
//                    first,
//                    &mut self.stack,
//                    &mut nodes,
//                    &mut summary,
//                    &mut false,
//                    &mut 0,
//                );
//                break;
//            }
//        }

//        todo!()
//        // if nodes.len() == 1 {
//        //     let single = nodes.into_iter().next().unwrap();
//        //     match single {
//        //         NodeOrSlicedLeaf::Sliced(slice, summary) => todo!(),
//        //         _ => unreachable!(),
//        //     }
//        // } else if nodes.len() == 2 {
//        //     let mut nodes = nodes.into_iter();
//        //     let start = nodes.next().unwrap();
//        //     let end = nodes.next().unwrap();
//        //     let (start, st_summ) = match start {
//        //         NodeOrSlicedLeaf::Sliced(slice, summary) => (slice, summary),
//        //         _ => unreachable!(),
//        //     };
//        //     let (end, end_summ) = match end {
//        //         NodeOrSlicedLeaf::Sliced(slice, summary) => (slice, summary),
//        //         _ => unreachable!(),
//        //     };
//        // }
//        // Some(TreeSlice::new(nodes, summary))
//    }
//}

// fn sumzang<'a, const N: usize, L, M>(
//     node: NodeOrSlicedLeaf<'a, N, L>,
//     stack: &mut VecDeque<NodeOrSlicedLeaf<'a, N, L>>,
//     out: &mut Vec<NodeOrSlicedLeaf<'a, N, L>>,
//     summary: &mut L::Summary,
//     appended_last: &mut bool,
//     insert_idx: &mut usize,
// ) where
//     L: Leaf,
//     M: Metric<L>,
// {
//     // let (slice, slice_summary) = match node {
//     //     NodeOrSlicedLeaf::Whole(Node::Internal(inode)) => {
//     //         for child in inode.children() {
//     //             if *appended_last {
//     //                 stack.insert(
//     //                     *insert_idx,
//     //                     NodeOrSlicedLeaf::Whole(&**child),
//     //                 );
//     //                 *insert_idx += 1;
//     //                 continue;
//     //             }
//     //             if M::measure(child.summary()) == M::zero() {
//     //                 *summary += child.summary();
//     //                 out.push(NodeOrSlicedLeaf::Whole(&**child));
//     //             } else {
//     //                 sumzang::<N, L, M>(
//     //                     NodeOrSlicedLeaf::Whole(&**child),
//     //                     stack,
//     //                     out,
//     //                     summary,
//     //                     appended_last,
//     //                     insert_idx,
//     //                 );
//     //             }
//     //         }

//     //         return;
//     //     },

//     //     NodeOrSlicedLeaf::Whole(Node::Leaf(leaf)) => {
//     //         (leaf.value().borrow(), leaf.summary())
//     //     },

//     //     NodeOrSlicedLeaf::Sliced(slice, ref summary) => (slice, summary),
//     // };

//     // let (left, left_summary, right) =
//     //     M::split_left(slice, M::one(), slice_summary);

//     // *summary += &left_summary;
//     // out.push(NodeOrSlicedLeaf::Sliced(left, left_summary));

//     // if let Some((right, right_summary)) = right {
//     //     stack.push_front(NodeOrSlicedLeaf::Sliced(right, right_summary));
//     //     *insert_idx = 1;
//     // }

//     // *appended_last = true;
// }

/// An iterator over consecutive units of a particular metric.
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    start: Option<(&'a L::Slice, L::Summary)>,

    /// TODO: docs
    stack: VecDeque<&'a Arc<Node<FANOUT, L>>>,

    /// TODO: docs
    end: Option<(&'a L::Slice, L::Summary)>,

    metric: std::marker::PhantomData<M>,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            start: self.start.clone(),
            stack: self.stack.clone(),
            end: self.end.clone(),
            metric: std::marker::PhantomData,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        let (start_slice, stack) = match &*tree.root {
            Node::Leaf(leaf) => (
                Some((leaf.value().borrow(), leaf.summary().clone())),
                VecDeque::new(),
            ),

            Node::Internal(inode) => (None, inode.children().iter().collect()),
        };

        Units {
            start: start_slice,
            stack,
            end: None,
            metric: std::marker::PhantomData,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
    From<&'a TreeSlice<'a, FANOUT, L>> for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Units<'a, FANOUT, L, M> {
        let (start, stack, end) = match &tree_slice.span {
            SliceSpan::Single(slice) => (
                Some((*slice, tree_slice.summary().clone())),
                VecDeque::new(),
                None,
            ),

            SliceSpan::Multi { start, internals, end } => (
                Some(start.clone()),
                internals.iter().collect(),
                Some(end.clone()),
            ),

            SliceSpan::Empty => (None, VecDeque::new(), None),
        };

        Units { start, stack, end, metric: std::marker::PhantomData }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Iterator
    for Units<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        println!("================");
        println!("{:#?}", self.start);
        println!("{:#?}", self.stack);
        println!("{:#?}", self.end);

        if self.start.is_none() && self.stack.is_empty() && self.end.is_none()
        {
            return None;
        }

        let (start, mut summary) = match self.start.take() {
            Some((slice, summary)) => {
                if M::measure(&summary) == M::zero() {
                    // The starting slice is set but it has zero measure. Set
                    // the initial summary to the slice's summary.
                    if !self.stack.is_empty() || self.end.is_some() {
                        (Some((slice, summary.clone())), summary)
                    } else {
                        return Some(TreeSlice {
                            span: SliceSpan::Single(slice),
                            summary,
                        });
                    }
                } else {
                    // The starting slice is sized wrt M. Split at the first
                    // unit, return the left part and set `self.start` to the
                    // right part for the next iteration.
                    let (left_slice, left_summary, right) =
                        M::split_left(slice, M::one(), &summary);
                    self.start = right;
                    return Some(TreeSlice {
                        span: SliceSpan::Single(left_slice),
                        summary: left_summary,
                    });
                }
            },

            None => (None, L::Summary::default()),
        };

        let mut internals = Vec::new();

        let mut end = None;

        while let Some(first) = self.stack.pop_front() {
            if M::measure(first.summary()) == M::zero() {
                summary += first.summary();
                internals.push(Arc::clone(first));
            } else {
                some_name_for_this_rec::<FANOUT, L, M>(
                    &**first,
                    &mut self.stack,
                    &mut self.start,
                    &mut internals,
                    &mut end,
                    &mut summary,
                    &mut false,
                    &mut 0,
                );
            }
        }

        // TODO: what about self.end?

        Some(TreeSlice {
            span: SliceSpan::Multi {
                start: start.unwrap(),
                internals,
                end: end.unwrap(),
            },
            summary,
        })
    }
}

fn some_name_for_this_rec<'a, const N: usize, L: Leaf, M: Metric<L>>(
    node: &'a Node<N, L>,
    stack: &mut VecDeque<&'a Arc<Node<N, L>>>,
    next_start: &mut Option<(&'a L::Slice, L::Summary)>,
    internals: &mut Vec<Arc<Node<N, L>>>,
    end: &mut Option<(&'a L::Slice, L::Summary)>,
    summary: &mut L::Summary,
    appended_last: &mut bool,
    insert_idx: &mut usize,
) {
    let leaf = match node {
        Node::Internal(inode) => {
            let mut children = inode.children().iter();

            while let Some(child) = children.next() {
                if *appended_last {
                    stack.insert(*insert_idx, child);
                    *insert_idx += 1;
                    for c in children {
                        stack.insert(*insert_idx, c);
                        *insert_idx += 1;
                    }
                    return;
                }

                if M::measure(child.summary()) == M::zero() {
                    *summary += child.summary();
                    internals.push(Arc::clone(child));
                } else {
                    some_name_for_this_rec::<N, L, M>(
                        &*child,
                        stack,
                        next_start,
                        internals,
                        end,
                        summary,
                        appended_last,
                        insert_idx,
                    );
                }
            }

            unreachable!("TODO: explain why");
        },

        Node::Leaf(leaf) => leaf,
    };

    let (left, left_summary, right) =
        M::split_left(leaf.value().borrow(), M::one(), leaf.summary());

    *summary += &left_summary;
    *end = Some((left, left_summary));
    *next_start = right;
    *appended_last = true;
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> DoubleEndedIterator
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> std::iter::FusedIterator
    for Units<'a, FANOUT, L, M>
{
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
