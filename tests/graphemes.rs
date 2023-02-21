#[cfg(feature = "graphemes")]
use std::borrow::Cow;

#[cfg(feature = "graphemes")]
use crop::Rope;

// TODO: remove the `#[ignore]`s once
// https://github.com/unicode-rs/unicode-segmentation/issues/115 gets
// resolved.

#[cfg(feature = "graphemes")]
#[test]
fn iter_graphemes_ascii() {
    let r = Rope::from("abcd");

    let mut graphemes = r.graphemes();

    assert_eq!(Cow::Borrowed("a"), graphemes.next().unwrap());
    assert_eq!(Cow::Borrowed("b"), graphemes.next().unwrap());
    assert_eq!(Cow::Borrowed("c"), graphemes.next().unwrap());
    assert_eq!(Cow::Borrowed("d"), graphemes.next().unwrap());
    assert_eq!(None, graphemes.next());
}

/// ```
/// Root
/// ├── "🇷"
/// ├── "🇸"
/// ├── "🇮"
/// └── "🇴"
#[ignore]
#[cfg(all(feature = "graphemes", feature = "small_chunks"))]
#[test]
fn iter_graphemes_two_flags() {
    let r = Rope::from("🇷🇸🇮🇴");

    let mut graphemes = r.graphemes();

    assert_eq!(
        Cow::<str>::Owned(String::from("🇷🇸")),
        graphemes.next().unwrap()
    );

    assert_eq!(
        Cow::<str>::Owned(String::from("🇮🇴")),
        graphemes.next().unwrap()
    );

    assert_eq!(None, graphemes.next());
}

#[ignore]
#[cfg(feature = "graphemes")]
#[test]
fn graphemes_iter_flags() {
    let r = Rope::from("🇬🇧🇯🇵🇺🇸🇫🇷🇷🇺🇨🇳🇩🇪🇪🇸🇬🇧🇯🇵🇺🇸🇫🇷🇷🇺🇨🇳🇩🇪🇪🇸🇬🇧🇯🇵🇺🇸🇫🇷🇷🇺🇨🇳🇩🇪🇪🇸");

    let mut graphemes = r.graphemes();

    assert_eq!("🇬🇧", graphemes.next().unwrap());
    assert_eq!("🇯🇵", graphemes.next().unwrap());
    assert_eq!("🇺🇸", graphemes.next().unwrap());
    assert_eq!("🇫🇷", graphemes.next().unwrap());
    assert_eq!("🇷🇺", graphemes.next().unwrap());
    assert_eq!("🇨🇳", graphemes.next().unwrap());
    assert_eq!("🇩🇪", graphemes.next().unwrap());
    assert_eq!("🇪🇸", graphemes.next().unwrap());
    assert_eq!("🇬🇧", graphemes.next().unwrap());
    assert_eq!("🇯🇵", graphemes.next().unwrap());
    assert_eq!("🇺🇸", graphemes.next().unwrap());
    assert_eq!("🇫🇷", graphemes.next().unwrap());
    assert_eq!("🇷🇺", graphemes.next().unwrap());
    assert_eq!("🇨🇳", graphemes.next().unwrap());
    assert_eq!("🇩🇪", graphemes.next().unwrap());
    assert_eq!("🇪🇸", graphemes.next().unwrap());
    assert_eq!("🇬🇧", graphemes.next().unwrap());
    assert_eq!("🇯🇵", graphemes.next().unwrap());
    assert_eq!("🇺🇸", graphemes.next().unwrap());
    assert_eq!("🇫🇷", graphemes.next().unwrap());
    assert_eq!("🇷🇺", graphemes.next().unwrap());
    assert_eq!("🇨🇳", graphemes.next().unwrap());
    assert_eq!("🇩🇪", graphemes.next().unwrap());
    assert_eq!("🇪🇸", graphemes.next().unwrap());
    assert_eq!(None, graphemes.next());

    let mut graphemes = r.graphemes().rev();

    assert_eq!("🇪🇸", graphemes.next().unwrap());
    assert_eq!("🇩🇪", graphemes.next().unwrap());
    assert_eq!("🇨🇳", graphemes.next().unwrap());
    assert_eq!("🇷🇺", graphemes.next().unwrap());
    assert_eq!("🇫🇷", graphemes.next().unwrap());
    assert_eq!("🇺🇸", graphemes.next().unwrap());
    assert_eq!("🇯🇵", graphemes.next().unwrap());
    assert_eq!("🇬🇧", graphemes.next().unwrap());
    assert_eq!("🇪🇸", graphemes.next().unwrap());
    assert_eq!("🇩🇪", graphemes.next().unwrap());
    assert_eq!("🇨🇳", graphemes.next().unwrap());
    assert_eq!("🇷🇺", graphemes.next().unwrap());
    assert_eq!("🇫🇷", graphemes.next().unwrap());
    assert_eq!("🇺🇸", graphemes.next().unwrap());
    assert_eq!("🇯🇵", graphemes.next().unwrap());
    assert_eq!("🇬🇧", graphemes.next().unwrap());
    assert_eq!("🇪🇸", graphemes.next().unwrap());
    assert_eq!("🇩🇪", graphemes.next().unwrap());
    assert_eq!("🇨🇳", graphemes.next().unwrap());
    assert_eq!("🇷🇺", graphemes.next().unwrap());
    assert_eq!("🇫🇷", graphemes.next().unwrap());
    assert_eq!("🇺🇸", graphemes.next().unwrap());
    assert_eq!("🇯🇵", graphemes.next().unwrap());
    assert_eq!("🇬🇧", graphemes.next().unwrap());
    assert_eq!(None, graphemes.next());
}

#[cfg(feature = "graphemes")]
#[test]
fn graphemes_is_boundary_two_flags() {
    let r = Rope::from("🇷🇸🇮🇴");
    assert!(r.is_grapheme_boundary(0));

    for i in 1..8 {
        assert!(!r.is_grapheme_boundary(i));
    }

    assert!(r.is_grapheme_boundary(8));

    for i in 9..16 {
        assert!(!r.is_grapheme_boundary(i));
    }

    assert!(r.is_grapheme_boundary(16));
}

#[cfg(feature = "graphemes")]
#[should_panic]
#[test]
fn graphemes_is_boundary_out_of_bounds() {
    let r = Rope::from("🇷🇸🇮🇴");
    assert!(r.is_grapheme_boundary(17));
}
