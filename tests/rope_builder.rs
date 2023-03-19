mod common;

use common::LARGE;
use crop::{Rope, RopeBuilder};

#[test]
fn builder_empty() {
    let r = RopeBuilder::new().build();

    assert!(r.is_empty());
    assert_eq!(Rope::new(), r);

    let mut b = RopeBuilder::new();

    b.append("").append("").append("").append("").append("");

    let r = b.build();

    assert!(r.is_empty());
    assert_eq!(Rope::new(), r);
}

#[cfg_attr(miri, ignore)]
#[test]
fn builder_0() {
    let mut b = RopeBuilder::new();
    let mut s = String::new();

    for line in LARGE.lines() {
        b.append(line);
        s.push_str(line);
    }

    assert_eq!(s, b.build());
}

#[test]
fn builder_crlf_0() {
    let mut b = RopeBuilder::new();
    b.append("aaa\r").append("\nbbb");
    let r = b.build();
    r.assert_invariants();
    assert_eq!(r, "aaa\r\nbbb");
}

#[test]
fn builder_crlf_1() {
    let mut b = RopeBuilder::new();
    b.append("aaa\r\nbbb");
    let r = b.build();
    r.assert_invariants();
    assert_eq!(r, "aaa\r\nbbb");
}
