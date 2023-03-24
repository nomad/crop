use std::fs::File;
use std::io::{BufWriter, Write};
use std::thread;

use crop::{Rope, RopeBuilder, RopeSlice};

fn main() {
    let mut builder = RopeBuilder::new();

    builder
        .append("I am a 🦀\n")
        .append("Who walks the shore\n")
        .append("And pinches toes all day.\n")
        .append("\n")
        .append("If I were you\n")
        .append("I'd wear some 👟\n")
        .append("And not get in my way.\n");

    let mut rope: Rope = builder.build();

    let byte_slice: RopeSlice = rope.byte_slice(..32);

    assert_eq!(byte_slice, "I am a 🦀\nWho walks the shore\n");

    let line_slice: RopeSlice = rope.line_slice(..2);

    assert_eq!(line_slice, byte_slice);

    assert_eq!(rope.line(5), "I'd wear some 👟");

    let start: usize = rope.byte_of_line(5);

    let end: usize = rope.byte_of_line(6);

    rope.replace(start..end, "I'd rock some 👠\n");

    assert_eq!(rope.line(5), "I'd rock some 👠");

    let snapshot: Rope = rope.clone();

    thread::spawn(move || {
        let mut file =
            BufWriter::new(File::create("my_little_poem.txt").unwrap());

        for chunk in snapshot.chunks() {
            file.write_all(chunk.as_bytes()).unwrap();
        }
    })
    .join()
    .unwrap();
}
