use std::sync::Arc;

use crate::tree::{Leaf, Metric, Node, Tree, TreeSlice};

/// An iterator over consecutive units of a particular metric.
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    root: &'a Arc<Node<FANOUT, L>>,

    /// TODO: docs
    initialized_front: bool,

    /// TODO: docs
    stack_front: Vec<(&'a Arc<Node<FANOUT, L>>, usize, L::Summary)>,

    /// TODO: docs
    start_slice: &'a L::Slice,

    /// TODO: docs
    start_summary: L::Summary,

    /// TODO: docs
    initialized_back: bool,

    /// TODO: docs
    stack_back: Vec<(&'a Arc<Node<FANOUT, L>>, usize, L::Summary)>,

    /// TODO: docs
    end_slice: &'a L::Slice,

    /// TODO: docs
    end_summary: L::Summary,

    /// TODO: docs
    yielded: L::BaseMetric,

    /// TODO: docs
    total: L::BaseMetric,

    _pd: std::marker::PhantomData<M>,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack_front: self.stack_front.clone(),
            start_summary: self.start_summary.clone(),
            stack_back: self.stack_back.clone(),
            end_summary: self.end_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        println!("{tree:#?}");

        let stack_capacity = tree.root().depth();

        Self {
            root: tree.root(),

            initialized_front: false,
            stack_front: Vec::with_capacity(stack_capacity),
            start_slice: <&L::Slice>::default(),
            start_summary: L::Summary::default(),

            initialized_back: false,
            stack_back: Vec::with_capacity(stack_capacity),
            end_slice: <&L::Slice>::default(),
            end_summary: L::Summary::default(),

            yielded: L::BaseMetric::zero(),
            total: L::BaseMetric::measure(tree.summary()),
            _pd: std::marker::PhantomData,
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
        // TODO: this doesn't yet work.

        let stack_capacity = tree_slice.root().depth();

        Self {
            root: tree_slice.root(),

            initialized_front: false,
            stack_front: Vec::with_capacity(stack_capacity),
            start_slice: tree_slice.start_slice(),
            start_summary: tree_slice.start_summary().clone(),

            initialized_back: false,
            stack_back: Vec::with_capacity(stack_capacity),
            end_slice: tree_slice.end_slice(),
            end_summary: tree_slice.end_summary().clone(),

            yielded: L::BaseMetric::zero(),
            total: L::BaseMetric::measure(tree_slice.summary()),
            _pd: std::marker::PhantomData,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Units<'a, FANOUT, L, M> {
    /// TODO: docs
    #[inline]
    fn initialize_front(&mut self) {}

    /// TODO: docs
    #[inline]
    fn initialize_back(&mut self) {}

    /// TODO: docs
    #[inline]
    fn next(&mut self) -> TreeSlice<'a, FANOUT, L> {
        todo!();
    }

    /// TODO: docs
    #[inline]
    fn next_back(&mut self) -> TreeSlice<'a, FANOUT, L> {
        todo!();
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Iterator
    for Units<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded == self.total {
            return None;
        } else if !self.initialized_front {
            self.initialize_front();
        }

        let tree_slice = self.next();
        self.yielded += L::BaseMetric::measure(tree_slice.summary());
        Some(tree_slice)
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> DoubleEndedIterator
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.yielded == self.total {
            return None;
        } else if !self.initialized_back {
            self.initialize_back();
        }

        let tree_slice = self.next_back();
        self.yielded += L::BaseMetric::measure(tree_slice.summary());
        Some(tree_slice)
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> std::iter::FusedIterator
    for Units<'a, FANOUT, L, M>
{
}

// struct DirectionState<'a, const N: usize, L: Leaf> {
//     /// TODO: docs
//     root: &'a Arc<Node<N, L>>,

//     /// TODO: docs
//     path: Vec<(&'a Inode<N, L>, usize)>,

//     /// TODO: docs
//     first_been_yielded: bool,

//     /// TODO: docs
//     start_slice: Option<(&'a L::Slice, L::Summary)>,
// }

// impl<'a, const N: usize, L: Leaf> DirectionState<'a, N, L> {
//     #[inline]
//     fn new(
//         root: &'a Arc<Node<N, L>>,
//         start_slice: Option<(&'a L::Slice, L::Summary)>,
//     ) -> Self {
//         Self { root, start_slice, path: Vec::new(), first_been_yielded: false }
//     }
// }

// #[inline]
// fn first_unit_forward<'a, const N: usize, L: Leaf, M: Metric<L>>(
//     root: &'a Arc<Node<N, L>>,
//     path: &mut Vec<(&'a Inode<N, L>, usize)>,
//     first_slice: &mut Option<(&'a L::Slice, L::Summary)>,
// ) -> (TreeSlice<'a, N, L>, &'a Arc<Node<N, L>>)
// where
//     for<'d> &'d L::Slice: Default,
// {
//     let mut inode = match &**root {
//         Node::Internal(inode) => inode,

//         Node::Leaf(leaf) => {
//             let (slice, summary) = match first_slice.as_ref() {
//                 Some((slice, summary)) => (*slice, summary),

//                 None => (leaf.as_slice(), leaf.summary()),
//             };

//             let (slice, summary) = if M::measure(summary) == M::zero() {
//                 (slice, summary.clone())
//             } else {
//                 let (left, left_summary, right, right_summary) =
//                     M::split(slice, M::one(), summary);
//                 *first_slice = Some((right, right_summary));
//                 (left, left_summary)
//             };

//             let tree_slice = TreeSlice {
//                 root,
//                 before: L::Summary::default(),
//                 summary: summary.clone(),
//                 start_slice: slice,
//                 start_summary: summary,
//                 end_slice: Default::default(),
//                 end_summary: L::Summary::default(),
//                 num_leaves: 1,
//             };

//             return (tree_slice, root);
//         },
//     };

//     todo!()
// }

// #[inline]
// fn first_unit_backward<'a, const N: usize, L: Leaf, M: Metric<L>>(
//     root: &'a Arc<Node<N, L>>,
//     path: &mut Vec<(&'a Inode<N, L>, usize)>,
//     first_slice: &mut Option<(&'a L::Slice, L::Summary)>,
// ) -> (TreeSlice<'a, N, L>, &'a Arc<Node<N, L>>) {
//     todo!()
// }
