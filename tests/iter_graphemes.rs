#[cfg(feature = "graphemes")]
mod graphemes {
    use std::borrow::Cow;

    use crop::Rope;

    #[test]
    fn graphemes_ascii() {
        let r = Rope::from("abcd");

        assert_eq!(4, r.graphemes().count());

        let mut graphemes = r.graphemes();

        assert_eq!(Cow::<str>::Borrowed("a"), graphemes.next().unwrap());
        assert_eq!(Cow::<str>::Borrowed("b"), graphemes.next().unwrap());
        assert_eq!(Cow::<str>::Borrowed("c"), graphemes.next().unwrap());
        assert_eq!(Cow::<str>::Borrowed("d"), graphemes.next().unwrap());
        assert_eq!(None, graphemes.next());
    }

    #[ignore]
    #[test]
    fn graphemes_two_flags() {
        // Each flag is made by 2 4-byte codepoints, for a total of 16
        // bytes.
        //
        // Since 8 > ROPE_CHUNK_MAX_BYTES in test mode we should get owned
        // strings.

        let r = Rope::from("🇷🇸🇮🇴");

        assert_eq!(2, r.graphemes().count());

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

    #[test]
    fn is_boundary_two_flags() {
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

    #[test]
    #[should_panic]
    fn is_boundary_out_of_bounds() {
        let r = Rope::from("🇷🇸🇮🇴");
        assert!(r.is_grapheme_boundary(17));
    }
}
