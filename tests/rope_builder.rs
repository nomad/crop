mod common;

use common::LARGE;
use crop::{Rope, RopeBuilder};

#[test]
fn empty() {
    let r = RopeBuilder::new().build();

    assert!(r.is_empty());
    assert_eq!(Rope::new(), r);

    let mut b = RopeBuilder::new();

    b.append("").append("").append("").append("").append("");

    let r = b.build();

    assert!(r.is_empty());
    assert_eq!(Rope::new(), r);
}

#[test]
fn large_lines() {
    let mut b = RopeBuilder::new();
    let mut s = String::new();

    for line in LARGE.lines() {
        b.append(line);
        s.push_str(line);
    }

    assert_eq!(s, b.build());
}
