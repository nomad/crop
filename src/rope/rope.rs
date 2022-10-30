use super::{TextChunk, TextChunkIter};
use crate::Tree;

const ROPE_FANOUT: usize = 8;

#[derive(Debug)]
pub struct Rope {
    root: Tree<ROPE_FANOUT, TextChunk>,
}

impl Rope {
    pub fn byte_len(&self) -> usize {
        self.root.summarize().byte_len
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_str(text: &str) -> Self {
        Rope { root: Tree::from_leaves(TextChunkIter::new(text)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn easy() {
        let r = Rope::from_str("Hello there");
        assert_eq!(11, r.byte_len());

        println!("{:#?}", r.root);
        panic!("")

        // let r = Rope::from_str("🐕‍🦺");
        // assert_eq!(11, r.byte_len());

        // panic!("{r:?}");
    }
}
