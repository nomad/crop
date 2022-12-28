use super::Leaf;

#[derive(Clone, Default)]
pub(super) struct Lnode<L: Leaf> {
    pub(super) value: L,
    pub(super) summary: L::Summary,
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

impl<L: Leaf> Lnode<L> {
    #[inline]
    pub fn as_slice(&self) -> &L::Slice {
        self.value.borrow()
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }
}
