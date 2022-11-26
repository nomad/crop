use super::Summarize;

pub(super) struct Leaf<L: Summarize> {
    value: L,
    summary: L::Summary,
}

impl<Leaf: Summarize> std::fmt::Debug for self::Leaf<Leaf> {
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

impl<Leaf: Summarize> self::Leaf<Leaf> {
    pub(super) fn from_value(value: Leaf) -> Self {
        Self { summary: value.summarize(), value }
    }

    #[inline]
    pub(super) fn summary(&self) -> &Leaf::Summary {
        &self.summary
    }

    pub(super) fn value(&self) -> &Leaf {
        &self.value
    }
}
