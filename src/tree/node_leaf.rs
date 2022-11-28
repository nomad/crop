use super::Summarize;

#[derive(Default)]
pub(super) struct Leaf<L: Summarize> {
    pub(super) value: L,
    pub(super) summary: L::Summary,
}

impl<L: Summarize> std::fmt::Debug for Leaf<L> {
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

impl<L: Summarize> Leaf<L> {
    pub(super) fn from_value(value: L) -> Self {
        Self { summary: value.summarize(), value }
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }

    pub(super) fn value(&self) -> &L {
        &self.value
    }
}
