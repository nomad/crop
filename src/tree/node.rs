use super::traits::{BalancedLeaf, FromMetric, Leaf, Metric};
use super::{Arc, Inode};

#[derive(Clone)]
pub(super) enum Node<const N: usize, L: Leaf> {
    Internal(Inode<N, L>),
    Leaf(L),
}

impl<const N: usize, L: Leaf + Default> Default for Node<N, L> {
    #[inline]
    fn default() -> Self {
        Node::Leaf(L::default())
    }
}

impl<const N: usize, L: Leaf> core::fmt::Debug for Node<N, L> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        if !f.alternate() {
            match self {
                Self::Internal(inode) => inode.fmt(f),
                Self::Leaf(leaf) => leaf.fmt(f),
            }
        } else {
            match self {
                Self::Internal(inode) => write!(f, "{inode:#?}"),
                Self::Leaf(leaf) => write!(f, "{leaf:?}"),
            }
        }
    }
}

impl<const N: usize, L: Leaf> Node<N, L> {
    /// Asserts the invariants of this node, then if it's an inode it calls
    /// itself recursively on all of its children.
    pub(super) fn assert_invariants(&self) {
        match self {
            Node::Internal(inode) => {
                inode.assert_invariants();

                for child in inode.children() {
                    child.assert_invariants()
                }
            },

            Node::Leaf(_) => (),
        }
    }

    /// # Panics
    ///
    /// Panics if `other` is at a different depth.
    #[inline]
    pub(super) fn balance(&mut self, other: &mut Self)
    where
        L: BalancedLeaf,
    {
        debug_assert_eq!(self.depth(), other.depth());

        match (self, other) {
            (Node::Internal(left), Node::Internal(right)) => {
                left.balance(right)
            },

            (Node::Leaf(left), Node::Leaf(right)) => {
                L::balance_leaves(left, right)
            },

            _ => unreachable!(),
        }
    }

    #[inline]
    pub(super) fn base_len(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    #[inline]
    pub(super) fn convert_len<M1, M2>(&self, up_to: M1) -> M2
    where
        M1: Metric<L::Summary>,
        M2: FromMetric<M1, L::Summary>,
    {
        debug_assert!(up_to <= self.measure::<M1>());

        let mut m1 = M1::zero();
        let mut m2 = M2::zero();

        let mut node = self;

        'outer: loop {
            match node {
                Node::Internal(inode) => {
                    for child in inode.children() {
                        let child_m1 = child.measure::<M1>();

                        if m1 + child_m1 >= up_to {
                            node = &**child;
                            continue 'outer;
                        } else {
                            m1 += child_m1;
                            m2 += child.measure::<M2>();
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    return m2 + M2::measure_up_to(leaf, up_to - m1);
                },
            }
        }
    }

    #[inline]
    pub(super) fn depth(&self) -> usize {
        match self {
            Node::Internal(inode) => inode.depth(),
            Node::Leaf(_) => 0,
        }
    }

    #[inline]
    pub(super) fn get_leaf(&self) -> &L {
        match self {
            Node::Internal(_) => panic!(""),
            Node::Leaf(leaf) => leaf,
        }
    }

    #[inline]
    pub(super) fn get_leaf_mut(&mut self) -> &mut L {
        match self {
            Node::Internal(_) => panic!(""),
            Node::Leaf(leaf) => leaf,
        }
    }

    #[inline]
    pub(super) fn get_internal(&self) -> &Inode<N, L> {
        match self {
            Node::Internal(inode) => inode,
            Node::Leaf(_) => panic!(""),
        }
    }

    #[inline]
    pub(super) fn get_internal_mut(&mut self) -> &mut Inode<N, L> {
        match self {
            Node::Internal(inode) => inode,
            Node::Leaf(_) => panic!(""),
        }
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        match self {
            Node::Internal(inode) => inode.is_empty(),
            Node::Leaf(leaf) => leaf.is_empty(),
        }
    }

    #[allow(dead_code)]
    #[inline]
    pub(super) fn is_internal(&self) -> bool {
        matches!(self, Node::Internal(_))
    }

    #[inline]
    pub(super) fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }

    #[inline]
    pub(super) fn is_underfilled(&self) -> bool
    where
        L: BalancedLeaf,
    {
        match self {
            Node::Internal(inode) => inode.is_underfilled(),
            Node::Leaf(leaf) => leaf.is_underfilled(),
        }
    }

    /// Returns the leaf at the given offset, together with the leaf's
    /// M-offset in the tree.
    ///
    /// If the offset falls on a leaf boundary, the leaf to its left is
    /// returned.
    #[inline]
    pub(super) fn leaf_at_offset<M>(&self, offset: M) -> (&L, M)
    where
        M: Metric<L::Summary>,
    {
        debug_assert!(offset <= self.measure::<M>());

        let mut measured = M::zero();

        let mut node = self;

        loop {
            match node {
                Node::Internal(inode) => {
                    let (child_idx, child_offset) =
                        inode.child_at_offset(offset - measured);

                    measured += child_offset;

                    node = inode.child(child_idx);
                },

                Node::Leaf(leaf) => return (leaf, measured),
            }
        }
    }

    #[inline]
    pub(super) fn measure<M>(&self) -> M
    where
        M: Metric<L::Summary>,
    {
        match self {
            Node::Internal(inode) => inode.measure(),
            Node::Leaf(leaf) => leaf.measure(),
        }
    }

    /// Continuously replaces the node its child as long as it's an internal
    /// node with a single child. Note that an inode might become a leaf node
    /// after calling this.
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` enclosing the root has a strong counter > 1.
    #[inline]
    pub(super) fn replace_with_single_child(node: &mut Arc<Self>) {
        while let Self::Internal(inode) = Arc::get_mut(node).unwrap() {
            if inode.len() == 1 {
                *node = Arc::clone(inode.first());
            } else {
                break;
            }
        }
    }

    #[inline]
    pub(super) fn summary(&self) -> L::Summary {
        match self {
            Node::Internal(inode) => inode.summary().clone(),
            Node::Leaf(leaf) => leaf.summarize(),
        }
    }
}
