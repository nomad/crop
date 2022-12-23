mod common;

use common::LARGE;
use crop::{Rope, RopeBuilder};

#[test]
fn empty() {
    let r = RopeBuilder::new().build();

    assert!(r.is_empty());
    assert_eq!(Rope::new(), r);

    let r = RopeBuilder::new()
        .append("")
        .append("")
        .append("")
        .append("")
        .append("")
        .build();

    assert!(r.is_empty());
    assert_eq!(Rope::new(), r);
}

#[test]
fn large_lines() {
    let mut b = RopeBuilder::new();
    let mut s = String::new();

    for line in LARGE.lines() {
        b = b.append(line);
        s.push_str(line);
    }

    assert_eq!(s, b.build());
}
