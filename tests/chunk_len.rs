use crop::Rope;
use rand::Rng;

mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};

#[test]
fn chunk_len_empty() {
    let r = Rope::from("");
    assert_eq!(r.chunk_len(), 0);
    assert_eq!(r.byte_slice(..).chunk_len(), 0);
}

#[cfg_attr(miri, ignore)]
#[test]
fn chunk_len_random() {
    let mut rng = common::rng();

    for str in [TINY, SMALL, MEDIUM, LARGE] {
        let rope = Rope::from(str);

        assert_eq!(rope.chunk_len(), rope.chunks().count());

        for _ in 0..100 {
            let start = rng.random_range(0..=rope.byte_len());
            let end = rng.random_range(start..=rope.byte_len());
            let slice = rope.byte_slice(start..end);
            assert_eq!(slice.chunk_len(), slice.chunks().count());
        }
    }
}
