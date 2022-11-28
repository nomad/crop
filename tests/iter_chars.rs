use crop::Rope;
use rand::{thread_rng, Rng};

mod common;

use common::{CURSED_LIPSUM, LARGE};

#[test]
fn chars_empty() {
    let r = Rope::new();
    assert_eq!(0, r.chars().count());
    assert_eq!(0, r.byte_slice(..).chars().count());
}

#[test]
fn chars_forward() {
    let r = Rope::from(LARGE);
    let mut i = 0;
    for (c_rope, c_str) in r.chars().zip(LARGE.chars()) {
        assert_eq!(c_rope, c_str);
        i += 1;
    }
    assert_eq!(i, LARGE.chars().count());
}

#[test]
fn chars_backward() {
    let r = Rope::from(LARGE);
    let mut i = 0;
    for (c_rope, c_str) in r.chars().rev().zip(LARGE.chars().rev()) {
        assert_eq!(c_rope, c_str);
        i += 1;
    }
    assert_eq!(i, LARGE.chars().count());
}

#[test]
fn chars_both_ways() {
    let rope = Rope::from(LARGE);

    let total_chars = LARGE.chars().count();
    let i = thread_rng().gen_range(0..=total_chars);

    println!("i: {i}");

    // Go forward for the first `i` chars, then backward.

    let mut slice_chars = LARGE.chars();
    let mut rope_chars = rope.chars();

    for _ in 0..i {
        let rope_c = rope_chars.next().unwrap();
        let slice_c = slice_chars.next().unwrap();
        assert_eq!(rope_c, slice_c);
    }

    for _ in i..total_chars {
        let rope_c = rope_chars.next_back().unwrap();
        let slice_c = slice_chars.next_back().unwrap();
        assert_eq!(rope_c, slice_c);
    }

    assert_eq!(None, rope_chars.next());
    assert_eq!(None, rope_chars.next_back());

    // Now the opposite, go backward for the first `i` chars, then forward.

    let mut slice_chars = LARGE.chars();
    let mut rope_chars = rope.chars();

    for _ in 0..i {
        let rope_c = rope_chars.next_back().unwrap();
        let slice_c = slice_chars.next_back().unwrap();
        assert_eq!(rope_c, slice_c);
    }

    for _ in i..total_chars {
        let rope_c = rope_chars.next().unwrap();
        let slice_c = slice_chars.next().unwrap();
        assert_eq!(rope_c, slice_c);
    }

    assert_eq!(None, rope_chars.next());
    assert_eq!(None, rope_chars.next_back());
}

#[test]
fn chars_cursed() {
    let s = CURSED_LIPSUM;
    let r = Rope::from(s);

    assert_eq!(r.chars().count(), s.chars().count());
    assert_eq!(r.byte_slice(..).chars().count(), s.chars().count());

    for (c1, c2) in r.chars().zip(s.chars()) {
        assert_eq!(c1, c2);
    }

    for (c1, c2) in r.chars().rev().zip(s.chars().rev()) {
        assert_eq!(c1, c2);
    }
}
