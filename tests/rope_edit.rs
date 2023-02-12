use crop::Rope;

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
