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
        // Since 8 > TEXT_CHUNK_MAX_BYTES in test mode we should get owned
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
}
