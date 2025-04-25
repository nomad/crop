use crop::Rope;
use rand::{Rng, rng};

mod common;

use common::{CURSED_LIPSUM, LARGE, MEDIUM, SMALL, TINY};

#[test]
fn iter_bytes_empty() {
    let r = Rope::new();
    assert_eq!(0, r.bytes().count());
    assert_eq!(0, r.byte_slice(..).bytes().count());
}

#[test]
fn iter_bytes_forward() {
    let s = if cfg!(miri) { "Hello, world!" } else { LARGE };
    let r = Rope::from(s);
    let mut i = 0;
    for (b_rope, b_str) in r.bytes().zip(s.bytes()) {
        assert_eq!(b_rope, b_str);
        i += 1;
    }
    assert_eq!(i, r.byte_len());
}

#[test]
fn iter_bytes_backward() {
    let s = if cfg!(miri) { "Hello, world!" } else { LARGE };
    let r = Rope::from(s);
    let mut i = 0;
    for (b_rope, b_str) in r.bytes().rev().zip(s.bytes().rev()) {
        assert_eq!(b_rope, b_str);
        i += 1;
    }
    assert_eq!(i, r.byte_len());
}

#[test]
fn iter_bytes_both_ways() {
    let s = if cfg!(miri) { "Hello, world!" } else { LARGE };
    let rope = Rope::from(s);

    let i = rng().random_range(0..=s.len());

    println!("i: {i}");

    // Go forward for the first `i` bytes, then backward.

    let mut slice_bytes = s.bytes();
    let mut rope_bytes = rope.bytes();

    for _ in 0..i {
        let rope_b = rope_bytes.next().unwrap();
        let slice_b = slice_bytes.next().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    for _ in i..s.len() {
        let rope_b = rope_bytes.next_back().unwrap();
        let slice_b = slice_bytes.next_back().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    assert_eq!(None, rope_bytes.next());
    assert_eq!(None, rope_bytes.next_back());

    // Now the opposite, go backward for the first `i` bytes, then forward.

    let mut slice_bytes = s.bytes();
    let mut rope_bytes = rope.bytes();

    for _ in 0..i {
        let rope_b = rope_bytes.next_back().unwrap();
        let slice_b = slice_bytes.next_back().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    for _ in i..s.len() {
        let rope_b = rope_bytes.next().unwrap();
        let slice_b = slice_bytes.next().unwrap();
        assert_eq!(rope_b, slice_b);
    }

    assert_eq!(None, rope_bytes.next());
    assert_eq!(None, rope_bytes.next_back());
}

#[test]
fn iter_bytes_cursed() {
    let s = CURSED_LIPSUM;
    let r = Rope::from(s);

    assert_eq!(r.bytes().count(), s.len());
    assert_eq!(r.byte_slice(..).bytes().count(), s.len());

    for (b1, b2) in r.bytes().zip(s.bytes()) {
        assert_eq!(b1, b2);
    }

    for (b1, b2) in r.bytes().rev().zip(s.bytes().rev()) {
        assert_eq!(b1, b2);
    }
}

#[test]
fn iter_bytes_over_slice_forward() {
    let mut rng = rand::rng();

    let slices = if cfg!(miri) {
        ["foo", "bar", "baz", "Hello, world!"]
    } else {
        [TINY, SMALL, MEDIUM, LARGE]
    };

    for s in slices {
        let r = Rope::from(s);

        for _ in 0..1 {
            let start = rng.random_range(0..=r.byte_len());
            let end = rng.random_range(start..=r.byte_len());

            let rope_slice = r.byte_slice(start..end);
            let str_slice = &s[start..end];

            for (idx, (rope_byte, str_byte)) in
                rope_slice.bytes().zip(str_slice.bytes()).enumerate()
            {
                if rope_byte != str_byte {
                    println!("idx: {idx}");
                    println!("Byte range: {start}..{end}");
                    panic!("{rope_byte:?} vs {str_byte:?}");
                }
            }
        }
    }
}

#[test]
fn iter_bytes_over_slice_backward() {
    let mut rng = rand::rng();

    let slices = if cfg!(miri) {
        ["foo", "bar", "baz", "Hello, world!"]
    } else {
        [TINY, SMALL, MEDIUM, LARGE]
    };

    for s in slices {
        let r = Rope::from(s);

        for _ in 0..1 {
            let start = rng.random_range(0..=r.byte_len());
            let end = rng.random_range(start..=r.byte_len());

            let rope_slice = r.byte_slice(start..end);
            let str_slice = &s[start..end];

            for (idx, (rope_byte, str_byte)) in rope_slice
                .bytes()
                .rev()
                .zip(str_slice.bytes().rev())
                .enumerate()
            {
                if rope_byte != str_byte {
                    println!("idx: {idx}");
                    println!("Byte range: {start}..{end}");
                    panic!("{rope_byte:?} vs {str_byte:?}");
                }
            }
        }
    }
}

#[test]
fn iter_chars_empty() {
    let r = Rope::new();
    assert_eq!(0, r.chars().count());
    assert_eq!(0, r.byte_slice(..).chars().count());
}

#[cfg_attr(miri, ignore)]
#[test]
fn iter_chars_forward() {
    let r = Rope::from(LARGE);
    let mut i = 0;
    for (c_rope, c_str) in r.chars().zip(LARGE.chars()) {
        assert_eq!(c_rope, c_str);
        i += 1;
    }
    assert_eq!(i, LARGE.chars().count());
}

#[cfg_attr(miri, ignore)]
#[test]
fn iter_chars_backward() {
    let r = Rope::from(LARGE);
    let mut i = 0;
    for (c_rope, c_str) in r.chars().rev().zip(LARGE.chars().rev()) {
        assert_eq!(c_rope, c_str);
        i += 1;
    }
    assert_eq!(i, LARGE.chars().count());
}

#[cfg_attr(miri, ignore)]
#[test]
fn iter_chars_both_ways() {
    let rope = Rope::from(LARGE);

    let total_chars = LARGE.chars().count();
    let i = rng().random_range(0..=total_chars);

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
fn iter_chars_cursed() {
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

#[test]
fn iter_lines_empty() {
    let r = Rope::new();
    assert_eq!(0, r.lines().count());
    assert_eq!(0, r.line_slice(..).lines().count());
}

#[test]
fn iter_lines_0() {
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
fn iter_lines_1() {
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
fn iter_lines_2() {
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
fn iter_lines_3() {
    let s = "This is a piece\nof text that doesn't\nfit in one\n chunk\nand \
             it also\r\nhas mixed\r\n line breaks\n and no trailing\nline \
             break.";

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
fn iter_lines_4() {
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

#[cfg_attr(miri, ignore)]
#[test]
fn iter_lines_over_test_vectors() {
    for s in [TINY, SMALL, MEDIUM, LARGE, CURSED_LIPSUM] {
        let rope = Rope::from(s);
        let slice = rope.byte_slice(..);

        assert_eq!(rope.lines().count(), s.lines().count());
        assert_eq!(slice.lines().count(), s.lines().count());

        for ((rope_line, slice_line), s_line) in
            rope.lines().zip(slice.lines()).zip(s.lines())
        {
            rope_line.assert_invariants();
            slice_line.assert_invariants();
            assert_eq!(rope_line, s_line);
            assert_eq!(slice_line, s_line);
        }
    }
}

#[test]
fn iter_lines_forward_backward() {
    let r = Rope::from("\na\nb\nc\n");

    let mut forward = r.lines();
    assert_eq!("", forward.next().unwrap());
    assert_eq!("a", forward.next().unwrap());
    assert_eq!("b", forward.next().unwrap());
    assert_eq!("c", forward.next().unwrap());
    assert_eq!(None, forward.next());

    let mut backward = r.lines().rev();
    assert_eq!("c", backward.next().unwrap());
    assert_eq!("b", backward.next().unwrap());
    assert_eq!("a", backward.next().unwrap());
    assert_eq!("", backward.next().unwrap());
    assert_eq!(None, backward.next());
}

#[cfg_attr(miri, ignore)]
#[test]
fn iter_lines_over_random_slices() {
    let mut rng = rand::rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let rope = Rope::from(s);

        for _ in 0..100 {
            let start = rng.random_range(0..=rope.byte_len());
            let end = rng.random_range(start..=rope.byte_len());

            let range = start..end;

            let rope_slice = rope.byte_slice(range.clone());
            let str_slice = &s[range.clone()];

            for (idx, (rope_line, str_line)) in
                rope_slice.lines().zip(str_slice.lines()).enumerate()
            {
                rope_line.assert_invariants();
                if rope_line != str_line {
                    println!(
                        "Failed on line #{} in byte range: {range:?}",
                        idx + 1
                    );
                    assert_eq!(rope_line, str_line);
                }
            }

            for ((idx, rope_line), str_line) in rope_slice
                .lines()
                .enumerate()
                .rev()
                .zip(str_slice.lines().rev())
            {
                rope_line.assert_invariants();
                if rope_line != str_line {
                    println!(
                        "Failed on line #{} in byte range: {range:?}",
                        idx + 1
                    );
                    assert_eq!(rope_line, str_line);
                }
            }
        }
    }
}

#[test]
fn iter_raw_lines_0() {
    let r = Rope::from(
        "Hey \r\nthis contains\nmixed line breaks, emojis -> \r\n🐕‍🦺 and \
         other -> こんにちは chars.\r\nCan we iterate\nover this?\n\r\n\n??",
    );

    let mut lines = r.raw_lines();

    assert_eq!("Hey \r\n", lines.next().unwrap());
    assert_eq!("this contains\n", lines.next().unwrap());
    assert_eq!("mixed line breaks, emojis -> \r\n", lines.next().unwrap());
    assert_eq!("🐕‍🦺 and other -> こんにちは chars.\r\n", lines.next().unwrap());
    assert_eq!("Can we iterate\n", lines.next().unwrap());
    assert_eq!("over this?\n", lines.next().unwrap());
    assert_eq!("\r\n", lines.next().unwrap());
    assert_eq!("\n", lines.next().unwrap());
    assert_eq!("??", lines.next().unwrap());
    assert_eq!(None, lines.next());
}

#[test]
fn iter_raw_lines_backward_0() {
    let r = Rope::from(
        "Hey \r\nthis contains\nmixed line breaks, emojis -> \r\n🐕‍🦺 and \
         other -> こんにちは chars.\r\nCan we iterate\nover this?\n\r\n\n??",
    );

    let mut lines = r.raw_lines().rev();

    assert_eq!("??", lines.next().unwrap());
    assert_eq!("\n", lines.next().unwrap());
    assert_eq!("\r\n", lines.next().unwrap());
    assert_eq!("over this?\n", lines.next().unwrap());
    assert_eq!("Can we iterate\n", lines.next().unwrap());
    assert_eq!("🐕‍🦺 and other -> こんにちは chars.\r\n", lines.next().unwrap());
    assert_eq!("mixed line breaks, emojis -> \r\n", lines.next().unwrap());
    assert_eq!("this contains\n", lines.next().unwrap());
    assert_eq!("Hey \r\n", lines.next().unwrap());
    assert_eq!(None, lines.next());
}

#[cfg_attr(miri, ignore)]
#[test]
fn iter_raw_lines_over_test_vectors() {
    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let rope = Rope::from(s);

        for (i, (rope_line, s_line)) in
            rope.raw_lines().zip(s.lines()).enumerate()
        {
            rope_line.assert_invariants();
            if i != rope.line_len() - 1 || s.ends_with('\n') {
                let mut line = s_line.to_owned();
                line.push('\n');
                assert_eq!(line, rope_line);
            } else {
                assert_eq!(s_line, rope_line);
            }
        }
    }
}

#[cfg_attr(miri, ignore)]
#[test]
fn iter_raw_lines_over_random_slices() {
    let mut rng = rand::rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let rope = Rope::from(s);

        for _ in 0..100 {
            let start = rng.random_range(0..=rope.byte_len());
            let end = rng.random_range(start..=rope.byte_len());

            let range = start..end;

            let rope_slice = rope.byte_slice(range.clone());
            let str_slice = &s[range.clone()];

            for (idx, (rope_line, str_line)) in
                rope_slice.raw_lines().zip(str_slice.lines()).enumerate()
            {
                rope_line.assert_invariants();

                let is_last = idx == rope_slice.line_len() - 1;

                // TODO: use `RopeSlice::ends_with()` if/when that's
                // implemented.
                let str_line = if !is_last || str_slice.ends_with('\n') {
                    let mut l = str_line.to_owned();
                    l.push('\n');
                    std::borrow::Cow::Owned(l)
                } else {
                    std::borrow::Cow::Borrowed(str_line)
                };

                if rope_line != str_line {
                    println!(
                        "Failed on line #{} in byte range: {range:?}",
                        idx + 1
                    );
                    assert_eq!(rope_line, str_line);
                }
            }

            for ((idx, rope_line), str_line) in rope_slice
                .raw_lines()
                .enumerate()
                .rev()
                .zip(str_slice.lines().rev())
            {
                rope_line.assert_invariants();

                let is_last = idx == rope_slice.line_len() - 1;

                // TODO: use `RopeSlice::ends_with()` if/when that's
                // implemented.
                let str_line = if !is_last || str_slice.ends_with('\n') {
                    let mut l = str_line.to_owned();
                    l.push('\n');
                    std::borrow::Cow::Owned(l)
                } else {
                    std::borrow::Cow::Borrowed(str_line)
                };

                if rope_line != str_line {
                    println!(
                        "Failed on line #{} in byte range: {range:?}",
                        idx + 1
                    );
                    assert_eq!(rope_line, str_line);
                }
            }
        }
    }
}
