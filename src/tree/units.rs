use std::sync::Arc;

use crate::tree::{Inode, Leaf, Metric, Node, Tree, TreeSlice};

/// An iterator over consecutive units of a particular metric.
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    root: &'a Arc<Node<FANOUT, L>>,

    /// TODO: docs
    forward: DirectionState<'a, FANOUT, L>,

    /// TODO: docs
    backward: DirectionState<'a, FANOUT, L>,

    yielded: M,

    total: M,

    /// TODO: docs
    metric: std::marker::PhantomData<M>,
}

struct DirectionState<'a, const N: usize, L: Leaf> {
    /// TODO: docs
    root: &'a Arc<Node<N, L>>,

    /// TODO: docs
    path: Vec<(&'a Inode<N, L>, usize)>,

    /// TODO: docs
    first_been_yielded: bool,

    /// TODO: docs
    start_slice: Option<(&'a L::Slice, L::Summary)>,
}

impl<'a, const N: usize, L: Leaf> DirectionState<'a, N, L> {
    #[inline]
    fn new(
        root: &'a Arc<Node<N, L>>,
        start_slice: Option<(&'a L::Slice, L::Summary)>,
    ) -> Self {
        Self { root, start_slice, path: Vec::new(), first_been_yielded: false }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        println!("{tree:#?}");

        Self {
            root: &tree.root,
            forward: DirectionState::new(&tree.root, None),
            backward: DirectionState::new(&tree.root, None),
            yielded: M::zero(),
            total: M::measure(tree.summary()),
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
        Self {
            root: &tree_slice.root,
            forward: DirectionState::new(
                &tree_slice.root,
                Some((
                    &tree_slice.start_slice,
                    tree_slice.start_summary.clone(),
                )),
            ),
            backward: DirectionState::new(
                &tree_slice.root,
                Some((&tree_slice.end_slice, tree_slice.end_summary.clone())),
            ),
            yielded: M::zero(),
            total: M::measure(tree_slice.summary()),
            metric: std::marker::PhantomData,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Units<'a, FANOUT, L, M> {}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Iterator
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    type Item = TreeSlice<'a, FANOUT, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // TODO: explain this
        if self.yielded == self.total + M::one() {
            return None;
        }
        // TODO: explain this
        else if !self.forward.first_been_yielded {
            let (first, forward_root) = first_unit_forward::<FANOUT, L, M>(
                self.root,
                &mut self.forward.path,
                &mut self.forward.start_slice,
            );
            self.yielded += M::one();
            self.forward.root = forward_root;
            self.forward.first_been_yielded = true;
            return Some(first);
        }
        // TODO: explain this
        else if self.yielded == self.total {
            todo!()
        }

        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> DoubleEndedIterator
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // TODO: explain this
        if self.yielded == self.total + M::one() {
            return None;
        }
        // TODO: explain this
        else if !self.backward.first_been_yielded {
            let (last, backward_root) = first_unit_backward::<FANOUT, L, M>(
                self.root,
                &mut self.backward.path,
                &mut self.backward.start_slice,
            );
            self.yielded += M::one();
            self.backward.root = backward_root;
            self.backward.first_been_yielded = true;
            return Some(last);
        }
        // TODO: explain this
        else if self.yielded == self.total {
            todo!()
        }

        todo!()
    }
}

#[inline]
fn first_unit_forward<'a, const N: usize, L: Leaf, M: Metric<L>>(
    root: &'a Arc<Node<N, L>>,
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
    first_slice: &mut Option<(&'a L::Slice, L::Summary)>,
) -> (TreeSlice<'a, N, L>, &'a Arc<Node<N, L>>)
where
    for<'d> &'d L::Slice: Default,
{
    let mut inode = match &**root {
        Node::Internal(inode) => inode,

        Node::Leaf(leaf) => {
            let (slice, summary) = match first_slice.as_ref() {
                Some((slice, summary)) => (*slice, summary),

                None => (leaf.as_slice(), leaf.summary()),
            };

            let (slice, summary) = if M::measure(summary) == M::zero() {
                (slice, summary.clone())
            } else {
                let (left, left_summary, right, right_summary) =
                    M::split(slice, M::one(), summary);
                *first_slice = Some((right, right_summary));
                (left, left_summary)
            };

            let tree_slice = TreeSlice {
                root,
                before: L::Summary::default(),
                summary: summary.clone(),
                start_slice: slice,
                start_summary: summary,
                end_slice: Default::default(),
                end_summary: L::Summary::default(),
                num_leaves: 1,
            };

            return (tree_slice, root);
        },
    };

    todo!()
}

#[inline]
fn first_unit_backward<'a, const N: usize, L: Leaf, M: Metric<L>>(
    root: &'a Arc<Node<N, L>>,
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
    first_slice: &mut Option<(&'a L::Slice, L::Summary)>,
) -> (TreeSlice<'a, N, L>, &'a Arc<Node<N, L>>) {
    todo!()
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> std::iter::FusedIterator
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
}
