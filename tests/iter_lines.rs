use crop::Rope;

mod common;

use common::{CURSED_LIPSUM, LARGE, MEDIUM, SMALL, TINY};

#[test]
fn lines_empty() {
    let r = Rope::new();
    assert_eq!(0, r.lines().count());
    assert_eq!(0, r.line_slice(..).lines().count());
}

#[test]
fn lines_0() {
    // Note: all these ropes should fit in a single leaf node assuming a
    // `ROPE_CHUNK_MAX_BYTES` of 4 in test mode.

    let r = Rope::from("abc");
    assert_eq!(1, r.lines().count());
    assert_eq!(1, r.byte_slice(..).lines().count());

    let r = Rope::from("a\nb");
    assert_eq!(2, r.lines().count());
    assert_eq!(2, r.byte_slice(..).lines().count());

    let r = Rope::from("a\nb\n");
    assert_eq!(2, r.lines().count());
    assert_eq!(2, r.byte_slice(..).lines().count());

    let r = Rope::from("\na\nb");
    assert_eq!(3, r.lines().count());
    assert_eq!(3, r.byte_slice(..).lines().count());

    let r = Rope::from("\n\n\n");
    assert_eq!(3, r.lines().count());
    assert_eq!(3, r.byte_slice(..).lines().count());

    let r = Rope::from("\n\n\n\n");
    assert_eq!(4, r.lines().count());
    assert_eq!(4, r.byte_slice(..).lines().count());

    let r = Rope::from("\n\n\na");
    assert_eq!(4, r.lines().count());
    assert_eq!(4, r.byte_slice(..).lines().count());
}

#[test]
fn lines_1() {
    let s = "\n\n\r\n\r\n\n\r\n\n";

    let rope = Rope::from(s);
    let slice = rope.byte_slice(..);

    assert_eq!(rope.lines().count(), s.lines().count());
    assert_eq!(slice.lines().count(), s.lines().count());

    for ((rope_line, slice_line), s_line) in
        rope.lines().zip(slice.lines()).zip(s.lines())
    {
        assert_eq!(rope_line, s_line);
        assert_eq!(slice_line, s_line);
    }
}

#[test]
fn lines_2() {
    let s = "this is\na line\r\nwith mixed\nline breaks\n";

    let rope = Rope::from(s);
    let slice = rope.byte_slice(..);

    assert_eq!(rope.lines().count(), s.lines().count());
    assert_eq!(slice.lines().count(), s.lines().count());

    for ((rope_line, slice_line), s_line) in
        rope.lines().zip(slice.lines()).zip(s.lines())
    {
        assert_eq!(rope_line, s_line);
        assert_eq!(slice_line, s_line);
    }
}

#[test]
fn lines_3() {
    let s = "This is a piece\nof text that's not \ngonna fit\nin\none \
             chunk\nand it also\r\nhas mixed\r\n line breaks\n and no \
             trailing\nline breaks.";

    let rope = Rope::from(s);
    let slice = rope.byte_slice(..);

    assert_eq!(rope.lines().count(), s.lines().count());
    assert_eq!(slice.lines().count(), s.lines().count());

    for ((rope_line, slice_line), s_line) in
        rope.lines().zip(slice.lines()).zip(s.lines())
    {
        assert_eq!(rope_line, s_line);
        assert_eq!(slice_line, s_line);
    }
}

#[test]
fn lines_4() {
    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let rope = Rope::from(s);
        let slice = rope.byte_slice(..);

        assert_eq!(rope.lines().count(), s.lines().count());
        assert_eq!(slice.lines().count(), s.lines().count());

        for ((rope_line, slice_line), s_line) in
            rope.lines().zip(slice.lines()).zip(s.lines())
        {
            assert_eq!(rope_line, s_line);
            assert_eq!(slice_line, s_line);
        }
    }
}

#[test]
fn lines_cursed() {
    let s = CURSED_LIPSUM;
    let r = Rope::from(s);

    assert_eq!(r.lines().count(), s.lines().count());
    assert_eq!(r.byte_slice(..).lines().count(), s.lines().count());

    for (l1, l2) in r.lines().zip(s.lines()) {
        assert_eq!(l1, l2);
    }

    for (l1, l2) in r.lines().rev().zip(s.lines().rev()) {
        assert_eq!(l1, l2);
    }
}

#[test]
fn lines_asymmetric_forward_backward() {
    let r = Rope::from("\na\nb\nc\n");

    let mut forward = r.lines();
    assert_eq!("", forward.next().unwrap());
    assert_eq!("a", forward.next().unwrap());
    assert_eq!("b", forward.next().unwrap());
    assert_eq!("c", forward.next().unwrap());
    assert_eq!(None, forward.next());

    let mut backward = r.lines().rev();
    assert_eq!("c", backward.next().unwrap());
    assert_eq!("a", backward.next().unwrap());
    assert_eq!("b", backward.next().unwrap());
    assert_eq!("", backward.next().unwrap());
    assert_eq!(None, backward.next());
}
