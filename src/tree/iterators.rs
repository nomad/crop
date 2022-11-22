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
        let (start, mut summary) = match self.start.take() {
            Some((slice, summary)) => {
                if M::measure(&summary) == M::zero() {
                    // println!("breaking here");
                    ((slice, summary.clone()), summary)
                } else {
                    // println!("got here?? {slice:?}");
                    let (left_slice, left_summary, right) =
                        M::split_left(slice, M::one(), &summary);

                    self.start = right;

                    return Some(TreeSlice {
                        span: SliceSpan::Single(left_slice),
                        summary: left_summary,
                    });
                }
            },

            // TODO: if start is none and the stack is empty here we're
            // returning none but end could me some
            None => match &**self.stack.pop_front()? {
                Node::Leaf(leaf) => {
                    if M::measure(leaf.summary()) == M::zero() {
                        (
                            (leaf.value().borrow(), leaf.summary().clone()),
                            leaf.summary().clone(),
                        )
                    } else {
                        let (left_slice, left_summary, right) = M::split_left(
                            leaf.value().borrow(),
                            M::one(),
                            leaf.summary(),
                        );
                        self.start = right;
                        return Some(TreeSlice {
                            span: SliceSpan::Single(left_slice),
                            summary: left_summary,
                        });
                    }
                },

                Node::Internal(inode) => {
                    let mut inode = inode;
                    loop {
                        let mut children = inode.children().iter();
                        match &**children.next().unwrap() {
                            Node::Leaf(leaf) => {
                                let (start, summary) =
                                    if M::measure(leaf.summary()) == M::zero()
                                    {
                                        (
                                            leaf.value().borrow(),
                                            leaf.summary().clone(),
                                        )
                                    } else {
                                        let (left_slice, left_summary, right) =
                                            M::split_left(
                                                leaf.value().borrow(),
                                                M::one(),
                                                leaf.summary(),
                                            );
                                        self.start = right;
                                        let mut idx = 0;
                                        for child in children {
                                            self.stack.insert(idx, child);
                                            idx += 1;
                                        }
                                        return Some(TreeSlice {
                                            span: SliceSpan::Single(
                                                left_slice,
                                            ),
                                            summary: left_summary,
                                        });
                                    };
                                let mut idx = 0;
                                for child in children {
                                    self.stack.insert(idx, child);
                                    idx += 1;
                                }
                                // println!("breaking here");
                                break ((start, summary.clone()), summary);
                            },

                            Node::Internal(i) => {
                                inode = i;
                                let mut idx = 0;
                                for child in children {
                                    self.stack.insert(idx, child);
                                    idx += 1;
                                }
                                continue;
                            },
                        }
                    }
                },
            },
        };

        // println!("got start: {start:?}");

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
                break;
            }
        }

        let end = match end {
            Some(end) => end,

            None => {
                let (end_slice, end_summary) = match self.end.take() {
                    Some((a, b)) => (a, b),

                    None => {
                        // TODO: if the end is not set and there's no self.end
                        // we either: a) return a single slice if internals is
                        // empty, or b) pop stuff off internals until we find
                        // the last leaf and set that as our end

                        match internals.pop() {
                            Some(last) => {
                                todo!()
                                // match last.try_unwrap().unwrap() {
                                //     Node::Leaf(leaf) => {
                                //         let (left, left_summary, right) =
                                //             M::split_left(
                                //                 leaf.value().borrow(),
                                //                 M::one(),
                                //                 leaf.summary(),
                                //             );
                                //         self.end = right;
                                //         (left, left_summary)
                                //     },

                                //     Node::Internal(inode) => {
                                //         let mut inode = inode;
                                //         todo!();
                                //         // loop {
                                //     let mut children =
                                //         inode.children().iter();
                                //     match &**children.next().unwrap() {
                                //         Node::Leaf(leaf) => {
                                //             let start =
                                //                 leaf.value().borrow();
                                //             let summary =
                                //                 leaf.summary().clone();
                                //             let mut idx = 0;
                                //             for child in children {
                                //                 self.stack.insert(
                                //                     idx, child,
                                //                 );
                                //                 idx += 1;
                                //             }
                                //             break (
                                //                 (
                                //                     start,
                                //                     summary.clone(),
                                //                 ),
                                //                 summary,
                                //             );
                                //         },

                                //         Node::Internal(i) => {
                                //             inode = i;
                                //             let mut idx = 0;
                                //             for child in children {
                                //                 self.stack.insert(
                                //                     idx, child,
                                //                 );
                                //                 idx += 1;
                                //             }
                                //             continue;
                                //         },
                                //     }
                                // }
                                // },
                                // }
                            },

                            None => {
                                return Some(TreeSlice {
                                    span: SliceSpan::Single(start.0),
                                    summary,
                                });
                            },
                        }
                    },
                };

                let (end_slice, end_summary, right) =
                    M::split_left(end_slice, M::one(), &end_summary);

                summary += &end_summary;

                self.end = right;

                (end_slice, end_summary)
            },
        };

        // println!("=====================================================");

        let span = SliceSpan::Multi { start, internals, end };

        // println!("returning {span:#?}");

        // println!("start: {:#?}", self.start);
        // println!("stack: {:#?}", self.stack);
        // println!("end: {:#?}", self.end);
        // println!("AAAAAAAAAAAAAND WE'RE DONE");

        Some(TreeSlice { span, summary })
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

            return;
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

// pub struct Unitos<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
//     start: Option<(&'a L::Slice, L::Summary)>,

//     root_nodes: &'a [Arc<Node<FANOUT, L>>],

//     root_forward_idx: usize,

//     forward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

//     metric: std::marker::PhantomData<M>,
// }

// impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Iterator
//     for Unitos<'a, FANOUT, L, M>
// {
//     type Item = TreeSlice<'a, FANOUT, L>;

//     fn next(&mut self) -> Option<Self::Item> {
//         // Let's assume forward path is [(32,0), (16,0),(8,0)] and that (8,0)
//         // is a leaf

//         let (leaf, summary) =
//             self.start.as_ref().map(|(sl, su)| (*sl, su)).unwrap_or({
//                 let &(inode, idx) = self.forward_path.last()?;
//                 let leaf =
//                     unsafe { inode.children()[idx].as_leaf_unchecked() };
//                 (leaf.value().borrow(), leaf.summary())
//             });

//         if M::measure(summary) == 0 {
//             start = (leaf, summary.clone())
//         } else {
//             let (left, left_summary, right) =
//         }

//         todo!()
//     }
// }

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
