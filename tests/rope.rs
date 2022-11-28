use crop::Rope;

mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};

#[test]
fn empty_rope() {
    let r = Rope::new();
    assert!(r.is_empty());

    let r = Rope::from("");
    assert!(r.is_empty());
}

#[test]
fn partial_eq() {
    for s in ["This is a service dog: 🐕‍🦺", TINY, SMALL, MEDIUM, LARGE]
    {
        let r = Rope::from(s);

        assert_eq!(r, r);
        assert_eq!(r.byte_slice(..), r.byte_slice(..));

        assert_eq!(r, s);
        assert_eq!(r.byte_slice(..), s);
        assert_eq!(r, r.byte_slice(..));
    }
}
