mod common;

use common::TINY;
use crop::Rope;

#[test]
fn empty_slice() {
    let r = Rope::from("");
    let s = r.byte_slice(..);
    assert!(s.is_empty());
}

#[test]
fn byte_slice() {
    let r = Rope::from("Hello there");

    let s = r.byte_slice(..);
    assert_eq!(11, s.byte_len());

    let s = s.byte_slice(0..5);
    assert_eq!(5, s.byte_len());

    let t = "Hello there this is a really long line that I'm gonna use to \
             test this fucking slicing methods that we got going on well \
             hope this shit works 'cause if it doesn't I'm gonna fucking \
             lose it ok bye :)";

    let r = Rope::from(t);

    let s = r.byte_slice(14..79);
    assert_eq!(65, s.byte_len());
    assert_eq!(s, &t[14..79]);

    let s = r.byte_slice(0..11);
    assert_eq!(11, s.byte_len());

    let s = r.byte_slice(0..=10);
    assert_eq!(11, s.byte_len());
}

#[test]
fn slice_grapheme_cluster() {
    let r = Rope::from("🐕‍🦺");

    assert_eq!(11, r.byte_slice(..).byte_len());

    assert_eq!("🐕", r.byte_slice(0..4));
    assert_eq!("‍", r.byte_slice(4..7));
    assert_eq!("🦺", r.byte_slice(7..11));
}

#[test]
fn slice_slice() {
    let s = TINY;
    let r = Rope::from(s);

    let rope_slice = r.byte_slice(129..512);
    let str_slice = &s[129..512];
    assert_eq!(rope_slice, str_slice);

    let rope_slice = rope_slice.byte_slice(37..319);
    let str_slice = &str_slice[37..319];
    assert_eq!(str_slice, rope_slice);
}
