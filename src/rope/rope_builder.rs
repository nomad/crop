use crate::Rope;

/// TODO: docs
#[derive(Clone, Default)]
pub struct RopeBuilder {}

impl RopeBuilder {
    /// TODO: docs
    #[inline]
    pub fn append<T>(mut self, text: T) -> Self
    where
        T: AsRef<str>,
    {
        self
    }

    /// TODO: docs
    #[inline]
    pub fn build(self) -> Rope {
        todo!()
    }

    /// TODO: docs
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}
