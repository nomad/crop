#[derive(Default)]
pub(super) struct Leaf<L: super::Leaf> {
    pub(super) value: L,
    pub(super) summary: L::Summary,
}

impl<L: super::Leaf> std::fmt::Debug for Leaf<L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            f.debug_struct("Leaf")
                .field("value", &self.value)
                .field("summary", &self.summary)
                .finish()
        } else {
            write!(f, "{:?} — {:?}", self.value, self.summary)
        }
    }
}

impl<L: super::Leaf> Leaf<L> {
    #[inline]
    pub(super) fn from_value(value: L) -> Self {
        Self { summary: value.summarize(), value }
    }

    #[inline]
    pub fn as_slice(&self) -> &L::Slice {
        self.value.borrow()
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }

    #[inline]
    pub(super) fn value(&self) -> &L {
        &self.value
    }
}
