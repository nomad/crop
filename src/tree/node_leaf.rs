use std::ops::RangeBounds;

use super::traits::*;
use super::{Leaf, Metric};

#[derive(Clone, Default)]
pub(super) struct Lnode<L: Leaf> {
    value: L,
    summary: L::Summary,
}

impl<L: Leaf> std::fmt::Debug for Lnode<L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            f.debug_struct("Lnode")
                .field("value", &self.value)
                .field("summary", &self.summary)
                .finish()
        } else {
            write!(f, "{:?} — {:?}", self.value, self.summary)
        }
    }
}

impl<L: Leaf> From<L> for Lnode<L> {
    #[inline]
    fn from(value: L) -> Self {
        Self { summary: value.summarize(), value }
    }
}

impl<L: Leaf> From<(L, L::Summary)> for Lnode<L> {
    #[inline]
    fn from((value, summary): (L, L::Summary)) -> Self {
        Self { value, summary }
    }
}

impl<L: Leaf> Lnode<L> {
    pub(super) fn assert_invariants(&self) {
        assert_eq!(self.summary, self.value.summarize());
    }

    #[inline]
    pub(super) fn as_slice(&self) -> &L::Slice {
        self.value.borrow()
    }

    #[inline]
    pub(super) fn balance(&mut self, other: &mut Self)
    where
        L: BalancedLeaf,
    {
        L::balance_leaves(
            (&mut self.value, &mut self.summary),
            (&mut other.value, &mut other.summary),
        )
    }

    #[inline]
    pub(super) fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    #[inline]
    pub(super) fn is_underfilled(&self) -> bool
    where
        L: BalancedLeaf,
    {
        L::is_underfilled(self.as_slice(), self.summary())
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.base_measure() == L::BaseMetric::zero()
    }

    #[inline]
    pub(super) fn measure<M: Metric<L>>(&self) -> M {
        M::measure(self.summary())
    }

    #[inline]
    pub(super) fn new(value: L, summary: L::Summary) -> Self {
        Self { value, summary }
    }

    #[inline]
    pub(super) fn remove<M>(&mut self, up_to: M)
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M>,
    {
        self.value.remove(&mut self.summary, up_to);
    }

    #[inline]
    pub(super) fn replace<M, R>(
        &mut self,
        range: R,
        slice: &L::Slice,
    ) -> Option<impl ExactSizeIterator<Item = Self>>
    where
        M: Metric<L>,
        R: RangeBounds<M>,
        L: ReplaceableLeaf<M>,
    {
        self.value
            .replace(&mut self.summary, range, slice)
            .map(|extra_leaves| extra_leaves.map(Self::from))
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }
}
