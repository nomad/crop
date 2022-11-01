use super::Summarize;

pub struct Leaves<'a, Leaf: Summarize> {
    leaves: Vec<&'a Leaf>,
    current: usize,
    iterating_forward: bool,
}

impl<'a, Leaf: Summarize> Leaves<'a, Leaf> {
    /// Reverses the direction of the iterator.
    pub fn reverse(mut self) -> Self {
        self.iterating_forward = !self.iterating_forward;
        self
    }
}

impl<'a, Leaf: Summarize> Iterator for Leaves<'a, Leaf> {
    type Item = &'a Leaf;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
