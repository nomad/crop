use crop::Rope;
use rand::Rng;

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

#[test]
fn lines_redo_slicing() {
    let r = Rope::from(
        "Hey \r\nthis contains\nmixed line breaks, emojis -> \r\n🐕‍🦺 and \
         other -> こんにちは chars.\r\nCan we iterate\nover this?\n\r\n\n??",
    );

    let mut lines = r.lines();

    assert_eq!("Hey ", lines.next().unwrap());
    assert_eq!("this contains", lines.next().unwrap());
    assert_eq!("mixed line breaks, emojis -> ", lines.next().unwrap());
    assert_eq!("🐕‍🦺 and other -> こんにちは chars.", lines.next().unwrap());
    assert_eq!("Can we iterate", lines.next().unwrap());
    assert_eq!("over this?", lines.next().unwrap());
    assert_eq!("", lines.next().unwrap());
    assert_eq!("", lines.next().unwrap());
    assert_eq!("??", lines.next().unwrap());
    assert_eq!(None, lines.next());
}

#[test]
fn lines_raw() {
    let r = Rope::from(
        "Hey \r\nthis contains\nmixed line breaks, emojis -> \r\n🐕‍🦺 and \
         other -> こんにちは chars.\r\nCan we iterate\nover this?\n\r\n\n??",
    );

    let mut lines = r.lines_raw();

    assert_eq!("Hey \r\n", lines.next().unwrap());
    assert_eq!("this contains\n", lines.next().unwrap());
    assert_eq!("mixed line breaks, emojis -> \r\n", lines.next().unwrap());
    assert_eq!(
        "🐕‍🦺 and other -> こんにちは chars.\r\n",
        lines.next().unwrap()
    );
    assert_eq!("Can we iterate\n", lines.next().unwrap());
    assert_eq!("over this?\n", lines.next().unwrap());
    assert_eq!("\r\n", lines.next().unwrap());
    assert_eq!("\n", lines.next().unwrap());
    assert_eq!("??", lines.next().unwrap());
    assert_eq!(None, lines.next());
}

#[test]
fn lines_rau() {
    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let rope = Rope::from(s);

        for (i, (rope_line, s_line)) in
            rope.lines_raw().zip(s.lines()).enumerate()
        {
            if i != rope.line_len() - 1 || s.ends_with("\n") {
                let mut line = s_line.to_owned();
                line.push_str("\n");
                assert_eq!(line, rope_line);
            } else {
                assert_eq!(s_line, rope_line);
            }
        }
    }
}

#[allow(unused_mut)]
#[allow(unused_variables)]
#[test]
fn raw_lines_over_rope_slices() {
    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let r = Rope::from(s);

        for _ in 0..100 {
            let start = rand::thread_rng().gen_range(0..=r.byte_len());
            let end = rand::thread_rng().gen_range(start..=r.byte_len());

            println!("Byte range: {start}..{end}");

            let slice = r.byte_slice(start..end);

            let mut checked = 0;

            for (i, (rope_line, mut s_line)) in
                slice.lines_raw().zip(s[start..end].lines()).enumerate()
            {
                // TODO: use this once we have `Rope{Slice}::ends_with`.
                //
                // if rope_line.ends_with("\n") {
                //     s_line = &s[checked..s_line.len() + 1];
                // }
                //
                //  assert_eq!(s_line, rope_line);
                //  checked += rope_line.byte_len();

                println!("i: {i}");

                if i != slice.line_len() - 1 || s[start..end].ends_with("\n") {
                    let mut line = s_line.to_owned();
                    line.push_str("\n");
                    assert_eq!(line, rope_line);
                } else {
                    assert_eq!(s_line, rope_line);
                }
            }
        }
    }
}

#[test]
fn lines_backward() {
    let r = Rope::from(
        "Hey \r\nthis contains\nmixed line breaks, emojis -> \r\n🐕‍🦺 and \
         other -> こんにちは chars.\r\nCan we iterate\nover this?\n\r\n\n??",
    );

    let mut lines = r.lines_raw().rev();

    assert_eq!("??", lines.next().unwrap());
    assert_eq!("\n", lines.next().unwrap());
    assert_eq!("\r\n", lines.next().unwrap());
    assert_eq!("over this?\n", lines.next().unwrap());
    assert_eq!("Can we iterate\n", lines.next().unwrap());
    assert_eq!(
        "🐕‍🦺 and other -> こんにちは chars.\r\n",
        lines.next().unwrap()
    );
    assert_eq!("mixed line breaks, emojis -> \r\n", lines.next().unwrap());
    assert_eq!("this contains\n", lines.next().unwrap());
    assert_eq!("Hey \r\n", lines.next().unwrap());
    assert_eq!(None, lines.next());
}

#[allow(unused_mut)]
#[allow(unused_variables)]
#[test]
fn aaa_lines_over_rope_slices() {
    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let r = Rope::from(s);

        for _ in 0..100 {
            let start = rand::thread_rng().gen_range(0..=r.byte_len());
            let end = rand::thread_rng().gen_range(start..=r.byte_len());

            let slice = r.byte_slice(start..end);

            let mut checked = 0;

            let mut i = slice.line_len();

            let mut s_lines = s[start..end].lines().rev();
            let mut rope_lines = slice.lines_raw().rev();

            while i > 0 {
                i -= 1;

                let s_line = s_lines.next().unwrap();
                let rope_line = rope_lines.next().unwrap();

                if i != slice.line_len() - 1 || s[start..end].ends_with("\n") {
                    let mut line = s_line.to_owned();
                    line.push_str("\n");
                    if line != rope_line {
                        println!("i {i}");
                        println!("Byte range: {start}..{end}");
                        panic!("{line:?} vs {rope_line:?}");
                    }
                } else {
                    if s_line != rope_line {
                        println!("i {i}");
                        println!("Byte range: {start}..{end}");
                        panic!("{s_line:?} vs {rope_line:?}");
                    }
                }
            }
        }
    }
}
