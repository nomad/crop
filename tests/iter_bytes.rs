use crop::Rope;
use rand::{thread_rng, Rng};

mod common;

use common::{CURSED_LIPSUM, LARGE};

#[test]
fn bytes_empty() {
    let r = Rope::new();
    assert_eq!(0, r.bytes().count());
    assert_eq!(0, r.byte_slice(..).bytes().count());
}

#[test]
fn bytes_forward() {
    let r = Rope::from(LARGE);
    let mut i = 0;
    for (b_rope, b_str) in r.bytes().zip(LARGE.bytes()) {
        assert_eq!(b_rope, b_str);
        i += 1;
    }
    assert_eq!(i, r.byte_len());
}

#[test]
fn bytes_backward() {
    let r = Rope::from(LARGE);
    let mut i = 0;
    for (b_rope, b_str) in r.bytes().rev().zip(LARGE.bytes().rev()) {
        assert_eq!(b_rope, b_str);
        i += 1;
    }
    assert_eq!(i, r.byte_len());
}

#[test]
fn bytes_both_ways() {
    let rope = Rope::from(LARGE);

    let i = thread_rng().gen_range(0..=LARGE.len());

    println!("i: {i}");

    // Go forward for the first `i` bytes, then backward.

    let mut slice_bytes = LARGE.bytes();
    let mut rope_bytes = rope.bytes();

    for _ in 0..i {
        let rope_b = rope_bytes.next().unwrap();
        let slice_b = slice_bytes.next().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    for _ in i..LARGE.len() {
        let rope_b = rope_bytes.next_back().unwrap();
        let slice_b = slice_bytes.next_back().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    assert_eq!(None, rope_bytes.next());
    assert_eq!(None, rope_bytes.next_back());

    // Now the opposite, go backward for the first `i` bytes, then forward.

    let mut slice_bytes = LARGE.bytes();
    let mut rope_bytes = rope.bytes();

    for _ in 0..i {
        let rope_b = rope_bytes.next_back().unwrap();
        let slice_b = slice_bytes.next_back().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    for _ in i..LARGE.len() {
        let rope_b = rope_bytes.next().unwrap();
        let slice_b = slice_bytes.next().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    assert_eq!(None, rope_bytes.next());
    assert_eq!(None, rope_bytes.next_back());
}

#[test]
fn bytes_cursed() {
    let s = CURSED_LIPSUM;
    let r = Rope::from(s);

    assert_eq!(r.bytes().count(), s.bytes().count());
    assert_eq!(r.byte_slice(..).bytes().count(), s.bytes().count());

    for (b1, b2) in r.bytes().zip(s.bytes()) {
        assert_eq!(b1, b2);
    }

    for (b1, b2) in r.bytes().rev().zip(s.bytes().rev()) {
        assert_eq!(b1, b2);
    }
}
