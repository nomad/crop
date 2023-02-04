use crop::Rope;
use rand::Rng;

mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};

#[test]
fn line_slice_empty() {
    let r = Rope::from("");
    assert!(r.line_slice(0..0).is_empty());

    let r = Rope::from("foo");
    assert!(!r.line_slice(0..1).is_empty());
}

/// ```
/// Root
/// ├───┐
/// │   ├── "aaa\n"
/// │   ├── "bbb\n"
/// │   ├── "ccc\n"
/// │   └── "ddd\n"
/// └───┐
///     ├── "eee\n"
///     └── "fff\n"
/// ```
#[test]
fn line_slice_0() {
    let r = Rope::from("aaa\nbbb\nccc\nddd\neee\nfff\n");

    let s = r.line_slice(1..2);
    assert_eq!("bbb\n", s);

    let s = r.line_slice(4..);
    assert_eq!("eee\nfff\n", s);

    let s = r.line_slice(..);
    assert_eq!(r, s);
}

#[test]
fn line_slice_1() {
    let r = Rope::from("Hello world");
    assert_eq!(1, r.line_len());
    assert_eq!("Hello world", r.line_slice(..));

    let r = Rope::from("Hello world\n");
    assert_eq!(1, r.line_len());
    assert_eq!("Hello world\n", r.line_slice(..));

    let r = Rope::from("Hello world\nthis is\na test");
    assert_eq!("Hello world\n", r.line_slice(..1));
    assert_eq!("Hello world\nthis is\n", r.line_slice(..2));
    assert_eq!("Hello world\nthis is\na test", r.line_slice(..3));
    assert_eq!("Hello world\nthis is\na test", r.line_slice(..));

    let r = Rope::from("Hello world\nthis is\na test\n");
    assert_eq!("Hello world\nthis is\na test\n", r.line_slice(..3));
    assert_eq!("Hello world\nthis is\na test\n", r.line_slice(..));
}

/// ```
/// Root
/// ├───┐
/// │   ├── "aaa\n"
/// │   ├── "bbb\n"
/// │   ├── "ccc\n"
/// │   └── "ddd\n"
/// └───┐
///     ├── "ee\ne"
///     └── "fff\n"
/// ```
#[test]
fn line_0() {
    let r = Rope::from("aaa\nbbb\nccc\nddd\nee\nefff\n");
    let s = r.line(4);
    assert_eq!("ee", s);
}

/// ```
/// Root
/// ├───┐
/// │   ├── "aaaa"
/// │   ├── "aaaa"
/// │   ├── "aaaa"
/// │   └── "aaa\n"
/// └───┐
///     ├── "bbbb"
///     └── "\nccc"
/// ```
#[test]
fn line_1() {
    let r = Rope::from("aaaaaaaaaaaaaaa\nbbbb\nccc");
    let l = r.line(1);
    assert_eq!("bbbb", l);
}

/// ```
/// Root
/// ├───┐
/// │   ├── "aaaa"
/// │   ├── "aaaa"
/// │   ├── "aaaa"
/// │   └── "aaa\n"
/// └───┐
///     ├── "\nbbb"
///     └── "bbbb"
/// ```
#[test]
fn line_2() {
    let r = Rope::from("aaaaaaaaaaaaaaa\n\nbbbbbbb");
    let l = r.line(1);
    assert_eq!("", l);
}

/// ```
/// Root
/// └── "\n\n\n\n"
/// ```
#[test]
fn line_3() {
    let r = Rope::from("\n\n\n\n");
    let l = r.line(2);
    assert_eq!("", l);
}

/// TODO: docs
#[test]
fn line_slices_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let r = Rope::from(s);

        let mut start = 0;
        let mut end = r.byte_len();

        let mut str_slice = &s[start..end];

        let mut rope_slice = r.byte_slice(start..end);

        let line_offsets = {
            let mut offset = 0;

            rope_slice
                .raw_lines()
                .map(|line| {
                    let o = offset;
                    offset += line.byte_len();
                    o
                })
                .collect::<Vec<_>>()
        };

        assert_eq!(line_offsets.len(), rope_slice.line_len());

        let mut offset = 0;

        while start != end {
            assert_eq!(str_slice, rope_slice);

            start = rng.gen_range(0..rope_slice.line_len());
            end = rng.gen_range(start..rope_slice.line_len());

            str_slice =
                &s[line_offsets[offset + start]..line_offsets[offset + end]];

            rope_slice = rope_slice.line_slice(start..end);

            offset += start;
        }
    }
}
