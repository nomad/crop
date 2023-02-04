use crop::Rope;
use rand::Rng;

mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};

/// TODO: docs
#[test]
fn random_byte_slices() {
    // let ss = TINY;
    // let r = Rope::from(ss);
    // let rs = r.byte_slice(..);

    // let range = 153..562;
    // let ss = &ss[range.clone()];
    // println!("{ss:?}");
    // let rs = rs.byte_slice(range);
    // assert_eq!(ss, rs);

    // let range = 276..384;
    // let ss = &ss[range.clone()];
    // println!("{ss:?}");
    // let rs = rs.byte_slice(range);
    // assert_eq!(ss, rs);

    // let range = 7..11;
    // let ss = &ss[range.clone()];
    // println!("{ss:?}");
    // let rs = rs.byte_slice(range);
    // assert_eq!(ss, rs);

    // let range = 3..4;
    // let ss = &ss[range.clone()];
    // println!("{ss:?}");
    // let rs = rs.byte_slice(range);
    // assert_eq!(ss, rs);

    // let range = 0..1;
    // let ss = &ss[range.clone()];
    // println!("{ss:?}");
    // let rs = rs.byte_slice(range);
    // assert_eq!(ss, rs);

    // if true {
    //     panic!("AA");
    // }

    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let r = Rope::from(s);

        let mut start = 0;
        let mut end = r.byte_len();

        let mut str_slice = &s[start..end];
        let mut rope_slice = r.byte_slice(start..end);

        while start != end {
            println!("start: {start}, end: {end}");
            assert_eq!(str_slice, rope_slice);

            str_slice = &str_slice[start..end];

            rope_slice = rope_slice.byte_slice(start..end);
            start = rng.gen_range(0..=rope_slice.byte_len());
            end = rng.gen_range(start..=rope_slice.byte_len());
        }
    }
}

#[test]
fn line_offset_of_byte_over_random_slices() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let crop = Rope::from(s);
        let ropey = ropey::Rope::from(s);

        for _ in 0..100 {
            let start = rng.gen_range(0..crop.byte_len());
            let end = rng.gen_range(start + 1..=crop.byte_len());
            let range = start..end;

            let crop_slice = crop.byte_slice(range.clone());
            let ropey_slice = ropey.byte_slice(range.clone());

            for _ in 0..10 {
                let byte_index = rng.gen_range(0..crop_slice.byte_len());
                let crop_line_offset = crop_slice.line_of_byte(byte_index);
                let ropey_line_offset = ropey_slice.byte_to_line(byte_index);

                if crop_line_offset != ropey_line_offset {
                    println!(
                        "Failed on byte index {byte_index} in byte range: \
                         {range:?}",
                    );
                    assert_eq!(crop_line_offset, ropey_line_offset)
                }
            }
        }
    }
}

#[test]
fn byte_offset_of_line_over_random_slices() {
    let mut rng = rand::thread_rng();

    for s in [TINY, SMALL, MEDIUM, LARGE] {
        let crop = Rope::from(s);
        let ropey = ropey::Rope::from(s);

        for _ in 0..100 {
            let start = rng.gen_range(0..crop.byte_len());
            let end = rng.gen_range(start + 1..=crop.byte_len());
            let range = start..end;

            let crop_slice = crop.byte_slice(range.clone());
            let ropey_slice = ropey.byte_slice(range.clone());

            for _ in 0..10 {
                let line_index = rng.gen_range(0..crop_slice.line_len());
                let crop_byte_offset = crop_slice.byte_of_line(line_index);
                let ropey_byte_offset = ropey_slice.line_to_byte(line_index);

                if crop_byte_offset != ropey_byte_offset {
                    println!(
                        "Failed on line index {line_index} in byte range: \
                         {range:?}",
                    );
                    assert_eq!(crop_byte_offset, ropey_byte_offset)
                }
            }
        }
    }
}
