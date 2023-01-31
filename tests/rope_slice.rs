use crop::Rope;
use rand::Rng;

mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};

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
