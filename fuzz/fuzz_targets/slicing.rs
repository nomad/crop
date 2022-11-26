#![no_main]

use crop::Rope;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::fuzz_target;

const LARGE: &str = include_str!("../../benches/large.txt");

fuzz_target!(|ranges: Vec<std::ops::Range<usize>>| {
    let s = LARGE;

    let rope = Rope::from(s);

    for range in ranges {
        if range.end > s.len() {
            continue;
        }

        let rope_slice = rope.byte_slice(range.clone());
        let str_slice = &s[range];

        assert_eq!(rope_slice.byte_len(), str_slice.len());
        assert_eq!(rope_slice, str_slice);
    }
});
