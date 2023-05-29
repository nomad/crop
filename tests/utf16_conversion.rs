mod common;

#[cfg(feature = "utf16-metric")]
mod tests {
    use crop::Rope;

    use crate::common::{TEXT, TEXT_EMOJI};

    #[test]
    fn utf16_len_0() {
        let r = Rope::from(TEXT);
        assert_eq!(r.utf16_len(), 103);

        let s = r.byte_slice(..);
        assert_eq!(s.utf16_len(), 103);
    }

    #[test]
    fn utf16_len_1() {
        let r = Rope::from(TEXT_EMOJI);
        assert_eq!(r.utf16_len(), 111);

        let s = r.byte_slice(..);
        assert_eq!(s.utf16_len(), 111);
    }

    #[test]
    fn utf16_len_2() {
        let r = Rope::new();
        assert_eq!(r.utf16_len(), 0);
    }

    #[test]
    fn utf16_len_3() {
        let r = Rope::from("🐸");
        assert_eq!(r.utf16_len(), 2);

        let r = Rope::from(TEXT_EMOJI);
        let s = r.byte_slice(16..39);
        assert_eq!(s.utf16_len(), 21);
    }

    #[test]
    fn byte_to_utf16_0() {
        let r = Rope::new();
        assert_eq!(r.utf16_code_unit_of_byte(0), 0);

        let s = r.byte_slice(..);
        assert_eq!(s.utf16_code_unit_of_byte(0), 0);
    }

    #[should_panic]
    #[test]
    fn byte_to_utf16_1() {
        let r = Rope::new();
        let _ = r.utf16_code_unit_of_byte(1);
    }

    #[test]
    fn byte_to_utf16_2() {
        let r = Rope::from("🐸");
        assert_eq!(r.utf16_code_unit_of_byte(4), 2);

        let s = r.byte_slice(..);
        assert_eq!(s.utf16_code_unit_of_byte(4), 2);
    }

    #[test]
    fn byte_to_utf16_3() {
        let r = Rope::from(TEXT_EMOJI);

        assert_eq!(0, r.utf16_code_unit_of_byte(0));

        assert_eq!(12, r.utf16_code_unit_of_byte(12));
        assert_eq!(14, r.utf16_code_unit_of_byte(16));

        assert_eq!(33, r.utf16_code_unit_of_byte(35));
        assert_eq!(35, r.utf16_code_unit_of_byte(39));

        assert_eq!(63, r.utf16_code_unit_of_byte(67));
        assert_eq!(65, r.utf16_code_unit_of_byte(71));

        assert_eq!(95, r.utf16_code_unit_of_byte(101));
        assert_eq!(97, r.utf16_code_unit_of_byte(105));

        assert_eq!(111, r.utf16_code_unit_of_byte(143));
    }

    #[test]
    fn byte_to_utf16_4() {
        let r = Rope::from(TEXT_EMOJI);
        let s = r.byte_slice(..);

        assert_eq!(0, s.utf16_code_unit_of_byte(0));

        assert_eq!(12, s.utf16_code_unit_of_byte(12));
        assert_eq!(14, s.utf16_code_unit_of_byte(16));

        assert_eq!(33, s.utf16_code_unit_of_byte(35));
        assert_eq!(35, s.utf16_code_unit_of_byte(39));

        assert_eq!(63, s.utf16_code_unit_of_byte(67));
        assert_eq!(65, s.utf16_code_unit_of_byte(71));

        assert_eq!(95, s.utf16_code_unit_of_byte(101));
        assert_eq!(97, s.utf16_code_unit_of_byte(105));

        assert_eq!(111, s.utf16_code_unit_of_byte(143));
    }

    #[should_panic]
    #[test]
    fn byte_to_utf16_5() {
        let r = Rope::from(TEXT_EMOJI);
        let _ = r.utf16_code_unit_of_byte(13);
    }

    #[should_panic]
    #[test]
    fn byte_to_utf16_6() {
        let r = Rope::from(TEXT_EMOJI);
        let s = r.byte_slice(..);
        let _ = s.utf16_code_unit_of_byte(13);
    }

    #[test]
    fn utf16_to_byte_0() {
        let r = Rope::new();
        assert_eq!(r.byte_of_utf16_code_unit(0), 0);

        let s = r.byte_slice(..);
        assert_eq!(s.byte_of_utf16_code_unit(0), 0);
    }

    #[should_panic]
    #[test]
    fn utf16_to_byte_1() {
        let r = Rope::new();
        let _ = r.byte_of_utf16_code_unit(1);
    }

    #[test]
    fn utf16_to_byte_2() {
        let r = Rope::from("🐸");
        assert_eq!(r.byte_of_utf16_code_unit(2), 4);

        let s = r.byte_slice(..);
        assert_eq!(s.byte_of_utf16_code_unit(2), 4);
    }

    #[test]
    fn utf16_to_byte_3() {
        let r = Rope::from(TEXT_EMOJI);

        assert_eq!(0, r.byte_of_utf16_code_unit(0));

        assert_eq!(12, r.byte_of_utf16_code_unit(12));
        assert_eq!(16, r.byte_of_utf16_code_unit(14));

        assert_eq!(35, r.byte_of_utf16_code_unit(33));
        assert_eq!(39, r.byte_of_utf16_code_unit(35));

        assert_eq!(67, r.byte_of_utf16_code_unit(63));
        assert_eq!(71, r.byte_of_utf16_code_unit(65));

        assert_eq!(101, r.byte_of_utf16_code_unit(95));
        assert_eq!(105, r.byte_of_utf16_code_unit(97));

        assert_eq!(143, r.byte_of_utf16_code_unit(111));
    }

    #[test]
    fn utf16_to_byte_4() {
        let r = Rope::from(TEXT_EMOJI);
        let s = r.byte_slice(..);

        assert_eq!(0, s.byte_of_utf16_code_unit(0));

        assert_eq!(12, s.byte_of_utf16_code_unit(12));
        assert_eq!(16, s.byte_of_utf16_code_unit(14));

        assert_eq!(35, s.byte_of_utf16_code_unit(33));
        assert_eq!(39, s.byte_of_utf16_code_unit(35));

        assert_eq!(67, s.byte_of_utf16_code_unit(63));
        assert_eq!(71, s.byte_of_utf16_code_unit(65));

        assert_eq!(101, s.byte_of_utf16_code_unit(95));
        assert_eq!(105, s.byte_of_utf16_code_unit(97));

        assert_eq!(143, s.byte_of_utf16_code_unit(111));
    }

    // TODO: we should panic the given UTF-16 offset doesn't lie on a char
    // boundary. Right now we just return the byte offset up to the previous
    // char boundary.
    #[ignore]
    #[should_panic]
    #[test]
    fn utf16_to_byte_5() {
        let r = Rope::from(TEXT_EMOJI);
        let _ = r.byte_of_utf16_code_unit(13);
    }

    // TODO: see above.
    #[ignore]
    #[should_panic]
    #[test]
    fn utf16_to_byte_6() {
        let r = Rope::from(TEXT_EMOJI);
        let s = r.byte_slice(..);
        let _ = s.byte_of_utf16_code_unit(13);
    }
}
