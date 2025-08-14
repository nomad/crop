#[cfg(feature = "serde")]
mod tests {
    use crop::Rope;

    #[test]
    fn ser_de_empty() {
        let rope = Rope::new();

        serde_test::assert_tokens(
            &rope,
            &[
                serde_test::Token::Seq { len: chunk_len(&rope) },
                serde_test::Token::SeqEnd,
            ],
        );
    }

    #[test]
    #[cfg_attr(feature = "small_chunks", ignore)]
    fn ser_de_single_chunk() {
        let mut rope = Rope::new();
        rope.insert(0, "lorem ");
        rope.insert(6, "ipsum");

        serde_test::assert_tokens(
            &rope,
            &[
                serde_test::Token::Seq { len: chunk_len(&rope) },
                serde_test::Token::Str("lorem ipsum"),
                serde_test::Token::SeqEnd,
            ],
        );
    }

    #[test]
    #[cfg_attr(feature = "small_chunks", ignore)]
    fn ser_de_multiple_chunks() {
        let mut rope = Rope::new();
        rope.insert(0, "lorem dolor");
        rope.insert(6, "ipsuma ");
        rope.delete(11..12);

        serde_test::assert_tokens(
            &rope,
            &[
                serde_test::Token::Seq { len: chunk_len(&rope) },
                serde_test::Token::Str("lorem ipsum"),
                serde_test::Token::Str(" dolor"),
                serde_test::Token::SeqEnd,
            ],
        );
    }

    #[test]
    #[cfg_attr(feature = "small_chunks", ignore)]
    fn ser_de_lf() {
        let mut rope = Rope::new();
        rope.insert(0, "lorem\n");
        rope.insert(6, "ipsum");

        serde_test::assert_tokens(
            &rope,
            &[
                serde_test::Token::Seq { len: chunk_len(&rope) },
                serde_test::Token::Str("lorem\nipsum"),
                serde_test::Token::SeqEnd,
            ],
        );
    }

    #[test]
    #[cfg_attr(feature = "small_chunks", ignore)]
    fn ser_de_crlf() {
        let mut rope = Rope::new();
        rope.insert(0, "lorem\r\n");
        rope.insert(7, "ipsum");

        serde_test::assert_tokens(
            &rope,
            &[
                serde_test::Token::Seq { len: chunk_len(&rope) },
                serde_test::Token::Str("lorem\r\nipsum"),
                serde_test::Token::SeqEnd,
            ],
        );
    }

    fn chunk_len(rope: &Rope) -> Option<usize> {
        if cfg!(feature = "chunk-len") { Some(rope.chunk_len()) } else { None }
    }

    #[cfg(feature = "chunk-len")]
    #[test]
    fn ser_de_bincode() {
        let mut rope = Rope::new();
        rope.insert(0, "lorem dolor");
        rope.insert(6, "ipsuma ");
        rope.delete(11..12);

        let config = bincode::config::standard();

        let serialized = bincode::serde::encode_to_vec(&rope, config).unwrap();

        let (deserialized, _) =
            bincode::serde::decode_from_slice::<Rope, _>(&serialized, config)
                .unwrap();

        assert_eq!(rope, deserialized);
    }
}
