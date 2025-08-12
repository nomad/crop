use core::ops::RangeBounds;

use super::traits::{BalancedLeaf, Leaf, Metric, ReplaceableLeaf};

#[derive(Clone, Default)]
pub(super) struct Lnode<L: Leaf> {
    value: L,
    summary: L::Summary,
}

impl<L: Leaf> core::fmt::Debug for Lnode<L> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
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
    pub(super) fn as_slice(&self) -> L::Slice<'_> {
        self.value.as_slice()
    }

    #[inline]
    pub(super) fn balance(&mut self, other: &mut Self)
    where
        L: BalancedLeaf,
    {
        L::balance_leaves(&mut self.value, &mut other.value);
        self.summary = self.value.summarize();
        other.summary = other.value.summarize();
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
        self.value.is_underfilled()
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.base_measure() == L::BaseMetric::zero()
    }

    #[inline]
    pub(super) fn measure<M: Metric<L::Summary>>(&self) -> M {
        M::measure(self.summary())
    }

    #[inline]
    pub(super) fn new(value: L, summary: L::Summary) -> Self {
        Self { value, summary }
    }

    #[inline]
    pub(super) fn remove_up_to<M>(&mut self, up_to: M)
    where
        M: Metric<L::Summary>,
        L: ReplaceableLeaf<M>,
    {
        self.value.remove_up_to(&mut self.summary, up_to);
    }

    #[track_caller]
    #[inline]
    pub(super) fn replace<M, R>(
        &mut self,
        range: R,
        replace_with: L::Replacement<'_>,
    ) -> Option<impl ExactSizeIterator<Item = Self> + use<M, R, L>>
    where
        M: Metric<L::Summary>,
        R: RangeBounds<M>,
        L: ReplaceableLeaf<M>,
    {
        self.value
            .replace(&mut self.summary, range, replace_with)
            .map(|extra_leaves| extra_leaves.map(Self::from))
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }
}
