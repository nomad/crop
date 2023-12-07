#![no_main]

use std::ops::Range;

use crop::Rope;
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use libfuzzer_sys::fuzz_target;

const NON_ASCII: &str = include_str!("../../tests/common/non-ascii.txt");

#[derive(Arbitrary, Clone, Debug)]
enum EditOp<'a> {
    Insert { byte_offset: usize, text: &'a str },
    Delete { byte_range: Range<usize> },
    Replace { byte_range: Range<usize>, text: &'a str },
}

#[derive(Arbitrary, Copy, Clone, Debug)]
enum StartingText<'a> {
    Custom(&'a str),
    NonAscii,
}

fuzz_target!(|data: (StartingText, Vec<EditOp>)| {
    let (starting, ops) = data;

    let start = match starting {
        StartingText::Custom(s) => s,
        StartingText::NonAscii => NON_ASCII,
    };
    let mut rope = Rope::from(start);
    let mut string = String::from(start);

    for op in ops {
        match op {
            EditOp::Insert { mut byte_offset, text }
                if byte_offset <= rope.byte_len() =>
            {
                while !rope.is_char_boundary(byte_offset) {
                    byte_offset += 1;
                }
                rope.insert(byte_offset, text);
                string.insert_str(byte_offset, text);
            },

            EditOp::Delete { mut byte_range }
                if byte_range.start <= byte_range.end
                    && byte_range.end <= rope.byte_len() =>
            {
                while !rope.is_char_boundary(byte_range.start) {
                    byte_range.start += 1;
                }
                while !rope.is_char_boundary(byte_range.end) {
                    byte_range.end += 1;
                }
                rope.delete(byte_range.clone());
                string.replace_range(byte_range, "");
            },

            EditOp::Replace { mut byte_range, text }
                if byte_range.start <= byte_range.end
                    && byte_range.end <= rope.byte_len() =>
            {
                while !rope.is_char_boundary(byte_range.start) {
                    byte_range.start += 1;
                }
                while !rope.is_char_boundary(byte_range.end) {
                    byte_range.end += 1;
                }
                rope.replace(byte_range.clone(), text);
                string.replace_range(byte_range, text);
            },

            _ => continue,
        }
    }

    rope.assert_invariants();
    assert_eq!(rope, string);
    assert_eq!(
        rope.lines().collect::<Vec<_>>(),
        string.lines().collect::<Vec<_>>(),
    );
});
