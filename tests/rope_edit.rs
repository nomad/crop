use crop::Rope;
use rand::Rng;

mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};

#[test]
fn rope_replace_0() {
    let mut r = Rope::from("aaaa");
    r.replace(2..3, "b");
    assert_eq!("aaba", r);
    r.assert_invariants();
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
    assert_eq!("aaggggggggggggccddddeeeeffff", r);
    r.assert_invariants();
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

            s.insert_str(insert_at, &insert);
            r.insert(insert_at, &insert);

            assert_eq!(s, r);

            r.assert_invariants();
        }
    }
}

#[test]
fn rope_delete_random() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..5 {
            let delete_range = {
                let start = rng.gen_range(0..=r.byte_len());
                let end = rng.gen_range(start..=r.byte_len());
                start..end
            };

            s.replace_range(delete_range.clone(), "");
            r.delete(delete_range);

            assert_eq!(s, r);

            r.assert_invariants();
        }
    }
}

#[test]
fn rope_replace_random() {
    let mut rng = rand::thread_rng();

    // let s = &TINY[..100];
    // let mut r = Rope::from(s);
    // let mut s = s.to_owned();
    // let replace_range = 78..92;
    // let replace_with = "ng elit. Mae";
    // s.replace_range(replace_range.clone(), &replace_with);
    // r.replace(replace_range, &replace_with);
    // assert_eq!(s, r);

    // let s = &TINY[..40];
    // let mut r = Rope::from(s);
    // let mut s = s.to_owned();
    // let replace_range = 21..39;
    // let replace_with = "orem ipsum dolor sit amet, consecte";
    // s.replace_range(replace_range.clone(), &replace_with);
    // r.replace(replace_range, &replace_with);
    // assert_eq!(s, r);

    let s = &TINY[..20];
    let mut r = Rope::from(s);
    let mut s = s.to_owned();

    let replace_range = 12..15;
    let replace_with = " dolor";
    s.replace_range(replace_range.clone(), &replace_with);
    r.replace(replace_range, &replace_with);
    assert_eq!(s, r);

    if true {
        panic!("AA");
    }

    // for s in [TINY, SMALL, MEDIUM, LARGE] {
    for s in [&TINY[..20]] {
        let mut r = Rope::from(s);
        let mut s = s.to_owned();

        for _ in 0..5 {
            let replace_range = {
                let start = rng.gen_range(0..=r.byte_len());
                let end = rng.gen_range(start..=r.byte_len());
                start..end
            };

            println!("replace_range: {replace_range:?}");

            let replace_with = {
                let start = rng.gen_range(0..=r.byte_len());
                let end = rng.gen_range(start..=r.byte_len());
                s[start..end].to_owned()
            };

            println!("replace_with: {replace_with:?}");

            s.replace_range(replace_range.clone(), &replace_with);
            r.replace(replace_range, &replace_with);

            assert_eq!(s, r);

            r.assert_invariants();
        }
    }
}
