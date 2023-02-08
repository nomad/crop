use crop::Rope;

#[test]
fn rope_replace_0() {
    let mut r = Rope::from("aaaa");
    r.replace(2..3, "b");
    assert_eq!("aaba", r);
    r.assert_invariants();
}
