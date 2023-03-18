use crop::Rope;
use rand::Rng;

mod common;

use common::{LARGE, MEDIUM, SMALL, TEXT, TINY};

// TODO: remove the `ignore`s once we handle fixing CRLF seams in
// `Rope::replace()`.

#[test]
fn insert_1() {
    let mut r = Rope::from(TEXT);

    r.insert(3, "AA");

    r.assert_invariants();

    assert_eq!(
        r,
        "HelAAlo there!  How're you doing?  It's a fine day, isn't it?  \
         Aren't you glad we're alive?  こんにちは、みんなさん！"
    );
}

#[test]
fn insert_2() {
    let mut r = Rope::from(TEXT);

    r.insert(0, "AA");

    r.assert_invariants();

    assert_eq!(
        r,
        "AAHello there!  How're you doing?  It's a fine day, isn't it?  \
         Aren't you glad we're alive?  こんにちは、みんなさん！"
    );
}

#[test]
fn insert_3() {
    let mut r = Rope::from(TEXT);

    r.insert(127, "AA");

    r.assert_invariants();

    assert_eq!(
        r,
        "Hello there!  How're you doing?  It's a fine day, isn't it?  Aren't \
         you glad we're alive?  こんにちは、みんなさん！AA"
    );
}

#[test]
fn insert_4() {
    let mut r = Rope::new();

    r.insert(0, "He");
    r.insert(2, "l");
    r.insert(3, "l");
    r.insert(4, "o w");
    r.insert(7, "o");
    r.insert(8, "rl");
    r.insert(10, "d!");
    r.insert(3, "zopter");

    r.assert_invariants();

    assert_eq!("Helzopterlo world!", r);
}

#[test]
fn insert_5() {
    let mut r = Rope::new();

    r.insert(0, "こんいちは、みんなさん！");
    r.insert(21, "zopter");

    r.assert_invariants();

    assert_eq!("こんいちは、みzopterんなさん！", r);
}

#[test]
fn insert_6() {
    let mut r = Rope::new();

    r.insert(0, "こ");
    r.insert(3, "ん");
    r.insert(6, "い");
    r.insert(9, "ち");
    r.insert(12, "は");
    r.insert(15, "、");
    r.insert(18, "み");
    r.insert(21, "ん");
    r.insert(24, "な");
    r.insert(27, "さ");
    r.insert(30, "ん");
    r.insert(33, "！");
    r.insert(21, "zopter");

    r.assert_invariants();

    assert_eq!("こんいちは、みzopterんなさん！", r);
}

#[should_panic]
#[test]
fn insert_7() {
    let mut r = Rope::new();

    r.insert(0, "こ");
    r.insert(2, "zopter");
}

#[test]
fn insert_8() {
    let mut r = Rope::from("Hello Earth!");
    r.insert(11, " 🌎");
    assert_eq!(r, "Hello Earth 🌎!");
}

#[test]
fn insert_small_random() {
    let mut rng = rand::thread_rng();

    let mut rope = Rope::new();
    let mut string = String::new();

    for _ in 0..(1 << 8) {
        for s in [
            "Hello ",
            "How are ",
            "you ",
            "doing?\r\n",
            "Let's ",
            "keep ",
            "inserting ",
            "more ",
            "items.\r\n",
            "こんいちは、",
            "みんなさん！",
        ] {
            let mut at = rng.gen_range(0..=rope.byte_len());

            while !string.is_char_boundary(at) {
                at = rng.gen_range(0..=rope.byte_len());
            }

            rope.insert(at, s);
            string.insert_str(at, s);
        }
    }

    rope.assert_invariants();
    assert_eq!(string, rope);
}

#[test]
fn insert_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..10 {
            let insert_at = rng.gen_range(0..=r.byte_len());

            let insert = {
                let start = rng.gen_range(0..=r.byte_len());
                let end = rng.gen_range(start..=r.byte_len());
                s[start..end].to_owned()
            };

            r.insert(insert_at, &insert);
            s.insert_str(insert_at, &insert);

            r.assert_invariants();
            assert_eq!(s, r);
        }
    }
}
#[test]
fn delete_1() {
    let mut r = Rope::from(TEXT);

    r.delete(5..11);
    r.delete(24..31);
    r.delete(19..25);
    r.delete(81..93);

    r.assert_invariants();

    assert_eq!(
        r,
        "Hello!  How're you a fine day, isn't it?  Aren't you glad we're \
         alive?  こんにんなさん！"
    );
}

#[test]
fn delete_2() {
    let mut r = Rope::from(TEXT);

    // Make sure removing nothing actually does nothing.
    r.delete(45..45);
    assert_eq!(r, TEXT);

    r.assert_invariants();
}

#[test]
fn delete_3() {
    let mut r = Rope::from(TEXT);

    // Make sure removing everything works.
    r.delete(0..127);

    r.assert_invariants();
    assert_eq!(r, "");
}

#[test]
fn delete_4() {
    let mut r = Rope::from(TEXT);

    // Make sure removing a large range works.
    r.delete(3..118);

    r.assert_invariants();
    assert_eq!(r, "Helさん！");
}

#[test]
#[should_panic]
fn delete_5() {
    let mut r = Rope::from(TEXT);
    #[allow(clippy::reversed_empty_ranges)]
    r.delete(56..55); // Wrong ordering of start/end on purpose.
}

#[test]
#[should_panic]
fn delete_6() {
    let mut r = Rope::from(TEXT);
    r.delete(126..128); // Removing past the end
}

#[test]
#[should_panic]
fn delete_7() {
    let mut r = Rope::from(TEXT);
    r.delete(127..128); // Removing past the end
}

#[test]
#[should_panic]
fn delete_8() {
    let mut r = Rope::from(TEXT);
    r.delete(128..128); // Removing past the end
}

#[test]
#[should_panic]
fn delete_9() {
    let mut r = Rope::from(TEXT);
    r.delete(128..129); // Removing past the end
}

#[test]
fn delete_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..20 {
            let delete_range = {
                let start = rng.gen_range(0..=r.byte_len());
                let end = rng.gen_range(start..=r.byte_len());
                start..end
            };

            r.delete(delete_range.clone());
            s.replace_range(delete_range, "");

            r.assert_invariants();
            assert_eq!(s, r);
        }
    }
}

#[test]
fn replace_0() {
    let mut r = Rope::from("aaaa");
    r.replace(2..3, "b");
    r.assert_invariants();
    assert_eq!("aaba", r);
}

/// ```
/// Root
/// ├───┐
/// │   ├── "aaaa"
/// │   ├── "bbbb"
/// │   ├── "cccc"
/// │   └── "dddd"
/// └───┐
///     ├── "eeee"
///     └── "ffff"
/// ```
#[test]
fn replace_1() {
    let mut r = Rope::from("aaaabbbbccccddddeeeeffff");
    r.replace(2..10, "gggggggggggg");
    r.assert_invariants();
    assert_eq!("aaggggggggggggccddddeeeeffff", r);
}

#[test]
fn replace_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..20 {
            let replace_range = {
                let start = rng.gen_range(0..=r.byte_len());
                let end = rng.gen_range(start..=r.byte_len());
                start..end
            };

            let replace_with = {
                let start = rng.gen_range(0..=r.byte_len());
                let end = rng.gen_range(start..=r.byte_len());
                s[start..end].to_owned()
            };

            r.replace(replace_range.clone(), &replace_with);
            s.replace_range(replace_range, &replace_with);

            r.assert_invariants();
            assert_eq!(s, r);
        }
    }
}

/// ```
/// Root
/// ├── "aaa\r"
/// ├── "bbbb"
/// └── "\nccc"
/// ```
#[ignore]
#[test]
fn fix_crlf_0() {
    let mut r = Rope::from("aaa\rbbbb\nccc");
    r.delete(4..8);
    r.assert_invariants();
    assert_eq!(r, "aaa\r\nccc");
}

/// ```
/// Root
/// └── "aaa\r"
/// ```
#[ignore]
#[test]
fn fix_crlf_1() {
    let mut r = Rope::from("aaa\r");
    r.insert(4, "\nbbb");
    r.assert_invariants();
    assert_eq!(r, "aaa\r\nbbb");
}

/// ```
/// Root
/// ├── "aaaa"
/// ├── "bbbb"
/// └── "\nccc"
/// ```
#[ignore]
#[test]
fn fix_crlf_2() {
    let mut r = Rope::from("aaaabbbb\nccc");
    r.replace(4..8, "ddd\r");
    r.assert_invariants();
    assert_eq!(r, "aaaaddd\r\nccc");
}

#[ignore]
#[test]
fn fix_crlf_4() {
    let mut r =
        Rope::from("\r\n\r\n\r\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n");

    r.delete(3..6);

    r.assert_invariants();

    assert_eq!(r, "\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n\r\n");
}
