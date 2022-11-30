use std::ops::Range;
use std::sync::Arc;

use super::node_leaf;
use super::tree_slice::SliceSpan;
use super::{Inode, Leaf, Leaves, Metric, Node, TreeSlice, Units};

/// TODO: docs
#[derive(Default)]
pub struct Tree<const FANOUT: usize, L: Leaf> {
    pub(super) root: Arc<Node<FANOUT, L>>,
}

impl<const N: usize, L: Leaf> Clone for Tree<N, L> {
    #[inline]
    fn clone(&self) -> Self {
        Tree { root: Arc::clone(&self.root) }
    }
}

impl<const N: usize, L: Leaf> std::fmt::Debug for Tree<N, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            f.debug_struct("Tree").field("root", &self.root).finish()
        } else {
            write!(f, "{:#?}", self.root)
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<TreeSlice<'a, FANOUT, L>>
    for Tree<FANOUT, L>
{
    #[inline]
    fn from(tree_slice: TreeSlice<'a, FANOUT, L>) -> Tree<FANOUT, L> {
        match tree_slice.span {
            SliceSpan::Empty => todo!(),

            SliceSpan::Single(slice) => Self::new_leaf_with_summary(
                slice.to_owned(),
                tree_slice.summary,
            ),

            SliceSpan::Multi { start, internals, end } => {
                todo!()
            },
        }
    }
}

impl<const FANOUT: usize, L: Leaf> Tree<FANOUT, L> {
    /// # Panics
    ///
    /// This function will panic if the iterator is empty.
    #[inline]
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = L>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut leaves = leaves.into_iter();

        if leaves.len() == 0 {
            panic!(
                "Cannot construct a Tree<{}, {}> from an empty iterator",
                FANOUT,
                std::any::type_name::<L>(),
            )
        }

        if leaves.len() == 1 {
            return Self::new_leaf(leaves.next().unwrap());
        }

        Tree { root: Arc::new(Node::Internal(Inode::from_leaves(leaves))) }
    }

    /// Returns an iterator over the leaves of this tree.
    #[inline]
    pub fn leaves(&self) -> Leaves<'_, FANOUT, L> {
        Leaves::from(self)
    }

    #[inline]
    fn new_leaf(leaf: L) -> Self {
        Self {
            root: Arc::new(Node::Leaf(node_leaf::Leaf {
                summary: leaf.summarize(),
                value: leaf,
            })),
        }
    }

    #[inline]
    fn new_leaf_with_summary(leaf: L, summary: L::Summary) -> Self {
        Self {
            root: Arc::new(Node::Leaf(node_leaf::Leaf {
                value: leaf,
                summary,
            })),
        }
    }

    /// TODO: docs
    #[inline]
    pub fn slice<M>(&self, range: Range<M>) -> TreeSlice<'_, FANOUT, L>
    where
        M: Metric<L>,
    {
        assert!(M::zero() <= range.start);
        assert!(range.start <= range.end);
        assert!(range.end <= M::measure(self.summary()));

        if range.start == range.end {
            TreeSlice::empty()
        } else {
            TreeSlice::from_range_in_node(&*self.root, range)
        }
    }

    /// TODO: docs
    #[inline]
    pub fn summary(&self) -> &L::Summary {
        self.root.summary()
    }

    /// TODO: docs
    #[inline]
    pub fn units<M>(&self) -> Units<'_, FANOUT, L, M>
    where
        M: Metric<L>,
    {
        Units::from(self)
    }
}

#[cfg(test)]
mod tests {
    use std::ops::AddAssign;

    use super::*;
    use crate::tree::Summarize;

    #[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
    pub struct Count(usize);

    impl<'a> AddAssign<&'a Self> for Count {
        fn add_assign(&mut self, rhs: &'a Self) {
            self.0 += rhs.0;
        }
    }

    impl Summarize for usize {
        type Summary = Count;

        fn summarize(&self) -> Self::Summary {
            Count(*self)
        }
    }

    impl Leaf for usize {
        type Slice = Self;
    }

    impl Metric<usize> for usize {
        fn zero() -> Self {
            0
        }

        fn one() -> Self {
            1
        }

        fn measure(count: &Count) -> Self {
            count.0
        }
    }

    #[test]
    fn easy() {
        let tree = Tree::<4, usize>::from_leaves(0..20);
        assert_eq!(Count(190), *tree.summary());
    }
}
