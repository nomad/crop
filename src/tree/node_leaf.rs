use super::traits::*;
use super::{Leaf, Metric};

#[derive(Clone, Default)]
pub(super) struct Lnode<L: Leaf> {
    pub(super) value: L,
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
        // assert!(self.is_big_enough());
        // assert_eq!(self.summary, self.value.summarize());
    }

    #[inline]
    pub(super) fn as_slice(&self) -> &L::Slice {
        self.value.borrow()
    }

    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    #[inline]
    pub(super) fn is_big_enough(&self) -> bool {
        self.value.is_big_enough(self.summary())
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
    pub(super) fn replace<M>(
        &mut self,
        range: std::ops::Range<M>,
        slice: &L::Slice,
    ) -> Option<Self>
    where
        L: ReplaceableLeaf<M>,
        M: Metric<L>,
    {
        self.value.replace(&mut self.summary, range, slice).map(Into::into)
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }
}
