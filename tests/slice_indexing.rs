use crop::Rope;
use rand::Rng;

mod common;

use common::{CURSED_LIPSUM, LARGE, MEDIUM, SMALL, TINY};

/// Tests `RopeSlice::byte()` on a bunch of random RopeSlices over different
/// texts.
#[cfg_attr(miri, ignore)]
#[test]
fn byte_random() {
    let mut rng = common::rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let r = Rope::from(s);

        for _ in 0..10 {
            let start = rng.random_range(0..=r.byte_len());
            let end = rng.random_range(start..=r.byte_len());

            let str_slice = &s[start..end];
            let rope_slice = r.byte_slice(start..end);

            for (idx, str_byte) in str_slice.bytes().enumerate() {
                let rope_byte = rope_slice.byte(idx);
                if str_byte != rope_byte {
                    panic!(
                        "string's byte is {str_byte}, but rope's byte is \
                         {rope_byte}",
                    );
                }
            }
        }
    }
}

/// Tests `RopeSlice::is_char_boundary()` on a bunch of random RopeSlices over
/// different texts.
#[cfg_attr(miri, ignore)]
#[test]
fn is_char_boundary_random() {
    let mut rng = common::rng();

    for s in [CURSED_LIPSUM, TINY, SMALL, MEDIUM, LARGE] {
        let r = Rope::from(s);

        for _ in 0..10 {
            let start = rng.random_range(0..=r.byte_len());
            let end = rng.random_range(start..=r.byte_len());

            if !(s.is_char_boundary(start) && s.is_char_boundary(end)) {
                continue;
            }

            let str_slice = &s[start..end];
            let rope_slice = r.byte_slice(start..end);

            for byte_idx in 0..rope_slice.byte_len() {
                if str_slice.is_char_boundary(byte_idx)
                    != rope_slice.is_char_boundary(byte_idx)
                {
                    println!("byte range: {:?}", start..end);
                    assert_eq!(
                        str_slice.is_char_boundary(byte_idx),
                        rope_slice.is_char_boundary(byte_idx)
                    );
                }
            }
        }
    }
}

/// Tests `crop::RopeSlice::line_of_byte()` against Ropey's
/// `ropey::RopeSlice::byte_to_line()`.
#[cfg_attr(miri, ignore)]
#[test]
fn line_of_byte_random() {
    let mut rng = common::rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let crop = Rope::from(s);
        let ropey = ropey::Rope::from(s);

        for _ in 0..100 {
            let start = rng.random_range(0..crop.byte_len());
            let end = rng.random_range(start + 1..=crop.byte_len());
            let range = start..end;

            let crop_slice = crop.byte_slice(range.clone());
            let ropey_slice = ropey.byte_slice(range.clone());

            for _ in 0..10 {
                let byte_offset = rng.random_range(0..=crop_slice.byte_len());
                let crop_line_offset = crop_slice.line_of_byte(byte_offset);
                let ropey_line_offset = ropey_slice.byte_to_line(byte_offset);

                if crop_line_offset != ropey_line_offset {
                    println!("byte offset: {byte_offset}");
                    println!("byte range: {:?}", start..end);
                    assert_eq!(crop_line_offset, ropey_line_offset)
                }
            }
        }
    }
}

/// Tests `crop::RopeSlice::byte_of_line()` against Ropey's
/// `ropey::RopeSlice::line_to_byte()`.
#[cfg_attr(miri, ignore)]
#[test]
fn byte_of_line_random() {
    let mut rng = common::rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let crop = Rope::from(s);
        let ropey = ropey::Rope::from(s);

        for _ in 0..100 {
            let start = rng.random_range(0..crop.byte_len());
            let end = rng.random_range(start + 1..=crop.byte_len());
            let range = start..end;

            let crop_slice = crop.byte_slice(range.clone());
            let ropey_slice = ropey.byte_slice(range.clone());

            for _ in 0..10 {
                let line_offset = rng.random_range(0..=crop_slice.line_len());
                let crop_byte_offset = crop_slice.byte_of_line(line_offset);
                let ropey_byte_offset = ropey_slice.line_to_byte(line_offset);

                if crop_byte_offset != ropey_byte_offset {
                    println!("line offset: {line_offset}");
                    println!("byte range: {range:?}");
                    assert_eq!(crop_byte_offset, ropey_byte_offset)
                }
            }
        }
    }
}
