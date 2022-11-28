use crop::Rope;

#[test]
fn line_slice() {
    let r = Rope::from("Hello world");
    assert_eq!(1, r.line_len());
    assert_eq!("Hello world", r.line_slice(..));

    let r = Rope::from("Hello world\n");
    assert_eq!(1, r.line_len());
    assert_eq!("Hello world", r.line_slice(..));

    let r = Rope::from("Hello world\nthis is \na test");
    assert_eq!("Hello world", r.line_slice(..1));
    assert_eq!("Hello world\nthis is", r.line_slice(..2));
    assert_eq!("Hello world\nthis is\na test", r.line_slice(..3));
    assert_eq!("Hello world\nthis is\na test", r.line_slice(..));

    let r = Rope::from("Hello world\nthis is \na test\n");
    assert_eq!("Hello world", r.line_slice(..1));
    assert_eq!("Hello world\nthis is", r.line_slice(..2));
    assert_eq!("Hello world\nthis is\na test", r.line_slice(..3));
    assert_eq!("Hello world\nthis is\na test", r.line_slice(..));
}
