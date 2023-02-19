use crop::Rope;
use rand::Rng;

mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};

#[test]
fn rope_replace_0() {
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
fn rope_replace_1() {
    let mut r = Rope::from("aaaabbbbccccddddeeeeffff");
    r.replace(2..10, "gggggggggggg");
    r.assert_invariants();
    assert_eq!("aaggggggggggggccddddeeeeffff", r);
}

#[test]
fn rope_insert_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..5 {
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
fn rope_delete_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..15 {
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
fn rope_replace_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..10 {
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
