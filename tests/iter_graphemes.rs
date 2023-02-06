#[cfg(feature = "graphemes")]
use std::borrow::Cow;

#[cfg(feature = "graphemes")]
use crop::Rope;

// TODO: remove the `#[ignore]`s once
// https://github.com/unicode-rs/unicode-segmentation/issues/115 gets
// addressed.

/// ```
/// Root
/// └── "abcd"
/// ```
#[cfg(feature = "graphemes")]
#[test]
fn graphemes_iter_ascii() {
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
#[cfg(feature = "graphemes")]
#[test]
fn graphemes_iter_two_flags() {
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
    assert!(!r.is_grapheme_boundary(1));
    assert!(!r.is_grapheme_boundary(2));
    assert!(!r.is_grapheme_boundary(3));
    assert!(!r.is_grapheme_boundary(4));
    assert!(!r.is_grapheme_boundary(5));
    assert!(!r.is_grapheme_boundary(6));
    assert!(!r.is_grapheme_boundary(7));
    assert!(r.is_grapheme_boundary(8));
    assert!(!r.is_grapheme_boundary(9));
    assert!(!r.is_grapheme_boundary(10));
    assert!(!r.is_grapheme_boundary(11));
    assert!(!r.is_grapheme_boundary(12));
    assert!(!r.is_grapheme_boundary(13));
    assert!(!r.is_grapheme_boundary(14));
    assert!(!r.is_grapheme_boundary(15));
    assert!(r.is_grapheme_boundary(16));
}

#[cfg(feature = "graphemes")]
#[should_panic]
#[test]
fn graphemes_is_boundary_out_of_bounds() {
    let r = Rope::from("🇷🇸🇮🇴");
    assert!(r.is_grapheme_boundary(17));
}
