use super::{Inode, Leaf, Lnode, Metric};

#[derive(Clone)]
pub(super) enum Node<const N: usize, L: Leaf> {
    Internal(Inode<N, L>),
    Leaf(Lnode<L>),
}

impl<const N: usize, L: Leaf + Default> Default for Node<N, L> {
    #[inline]
    fn default() -> Self {
        Node::Leaf(Lnode::default())
    }
}

impl<const N: usize, L: Leaf> std::fmt::Debug for Node<N, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            match self {
                Self::Internal(inode) => {
                    f.debug_tuple("Internal").field(&inode).finish()
                },
                Self::Leaf(leaf) => {
                    f.debug_tuple("Leaf").field(&leaf).finish()
                },
            }
        } else {
            match self {
                Self::Internal(inode) => write!(f, "{:#?}", inode),
                Self::Leaf(leaf) => write!(f, "{:#?}", leaf),
            }
        }
    }
}

impl<const N: usize, L: Leaf> Node<N, L> {
    /// Recursively asserts the invariants of...
    pub(super) fn assert_invariants(&self) {
        if let Node::Internal(inode) = self {
            inode.assert_invariants();

            for child in inode.children() {
                child.assert_invariants()
            }
        }
    }

    #[inline]
    pub(super) unsafe fn as_internal_unchecked(&self) -> &Inode<N, L> {
        debug_assert!(
            self.is_internal(),
            "A node was expected to be an internal node but it's a leaf. This \
            is a logic bug in crop. Please file an issue at \
            https://github.com/noib3/crop."
        );

        match self {
            Node::Leaf(_) => std::hint::unreachable_unchecked(),
            Node::Internal(inode) => inode,
        }
    }

    #[inline]
    pub(super) unsafe fn as_leaf_unchecked(&self) -> &Lnode<L> {
        debug_assert!(
            self.is_leaf(),
            "A node was expected to be a leaf but it's an internal node. This \
            is a logic bug in crop. Please file an issue at \
            https://github.com/noib3/crop."
        );

        match self {
            Node::Leaf(leaf) => leaf,
            Node::Internal(_) => std::hint::unreachable_unchecked(),
        }
    }

    #[inline]
    pub(super) unsafe fn as_mut_internal_unchecked(
        &mut self,
    ) -> &mut Inode<N, L> {
        debug_assert!(
            self.is_internal(),
            "A node was expected to be an internal node but it's a leaf. This \
            is a logic bug in crop. Please file an issue at \
            https://github.com/noib3/crop."
        );

        match self {
            Node::Leaf(_) => std::hint::unreachable_unchecked(),
            Node::Internal(inode) => inode,
        }
    }

    #[inline]
    pub fn convert_measure<M1, M2>(&self, from: M1) -> M2
    where
        M1: Metric<L>,
        M2: Metric<L>,
    {
        debug_assert!(from <= self.measure::<M1>() + M1::one());

        let mut m1 = M1::zero();
        let mut m2 = M2::zero();

        let mut node = self;

        'outer: loop {
            match node {
                Node::Internal(inode) => {
                    for child in inode.children() {
                        let child_m1 = child.measure::<M1>();

                        if m1 + child_m1 >= from {
                            node = &**child;
                            continue 'outer;
                        } else {
                            m1 += child_m1;
                            m2 += child.measure::<M2>();
                        }
                    }
                    unreachable!(
                        "Didn't I tell you to do bounds checks before \
                         calling this function?"
                    );
                },

                Node::Leaf(leaf) => {
                    let (_, left_summary, _, _) =
                        M1::split(leaf.as_slice(), from - m1, leaf.summary());

                    return m2 + M2::measure(&left_summary);
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
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = Lnode<L>>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut leaves = leaves.into_iter();

        if leaves.len() == 0 {
            panic!(
                "Cannot construct a Node<{}, {}> from an empty iterator",
                N,
                std::any::type_name::<L>(),
            )
        }

        if leaves.len() == 1 {
            return Self::Leaf(leaves.next().unwrap());
        }

        Self::Internal(Inode::from_leaves(leaves))
    }

    #[inline]
    pub(super) fn is_valid(&self) -> bool {
        match self {
            Node::Internal(inode) => inode.has_enough_children(),
            Node::Leaf(leaf) => leaf.is_big_enough(),
        }
    }

    #[inline]
    pub fn measure<M: Metric<L>>(&self) -> M {
        match self {
            Node::Internal(inode) => inode.measure(),
            Node::Leaf(leaf) => leaf.measure(),
        }
    }

    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    /// Note: doesn't do bounds checks.
    #[inline]
    pub fn leaf_at_measure<M>(&self, measure: M) -> (&L::Slice, M)
    where
        M: Metric<L>,
    {
        debug_assert!(measure < M::measure(self.summary()));

        let mut measured = M::zero();

        let mut node = self;

        'outer: loop {
            match node {
                Node::Internal(inode) => {
                    for child in inode.children() {
                        let this = M::measure(child.summary());
                        if measure < measured + this {
                            node = &**child;
                            continue 'outer;
                        } else {
                            measured += this;
                        }
                    }
                    unreachable!(
                        "Didn't I tell you to do bounds checks before \
                         calling this function?"
                    );
                },

                Node::Leaf(leaf) => {
                    return (leaf.as_slice(), measured);
                },
            }
        }
    }

    #[inline]
    pub(super) fn num_leaves(&self) -> usize {
        match self {
            Node::Internal(inode) => inode.num_leaves(),
            Node::Leaf(_) => 1,
        }
    }

    #[inline]
    pub(super) fn is_internal(&self) -> bool {
        matches!(self, Node::Internal(_))
    }

    #[inline]
    pub(super) fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        match self {
            Node::Internal(inode) => inode.summary(),
            Node::Leaf(leaf) => leaf.summary(),
        }
    }
}
