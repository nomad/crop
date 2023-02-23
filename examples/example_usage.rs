use std::fs::File;
use std::io::{BufWriter, Write};
use std::thread;

use crop::{RopeBuilder, RopeSlice};

fn main() {
    // A `Rope` can be created either directly from a string or incrementally
    // using the `RopeBuilder`.

    let mut builder = RopeBuilder::new();

    builder
        .append("I am a 🦀\n")
        .append("Who walks the shore\n")
        .append("And pinches toes all day.\n")
        .append("\n")
        .append("If I were you\n")
        .append("I'd wear some 👟\n")
        .append("And not get in my way.\n");

    let mut rope = builder.build();

    // `Rope`s can be sliced to obtain `RopeSlice`s.
    //
    // A `RopeSlice` is to a `Rope` as a `&str` is to a `String`: the former in
    // each pair are borrowed references of the latter.

    // A `Rope` can be sliced using either byte offsets:

    let byte_slice: RopeSlice = rope.byte_slice(..32);

    assert_eq!(byte_slice, "I am a 🦀\nWho walks the shore\n");

    // or line offsets:

    let line_slice: RopeSlice = rope.line_slice(..2);

    assert_eq!(line_slice, byte_slice);

    // We can also get a `RopeSlice` by asking the `Rope` for a specific line
    // index:

    assert_eq!(rope.line(5), "I'd wear some 👟");

    // We can modify that line by getting its start/end byte offsets:

    let start: usize = rope.byte_of_line(5);

    let end: usize = rope.byte_of_line(6);

    // and replacing that byte range with some other text:

    rope.replace(start..end, "I'd rock some 👠\n");

    assert_eq!(rope.line(5), "I'd rock some 👠");

    // `Rope`s use `Arc`s to share data between threads, so cloning them is
    // extremely cheap.

    let cloned = rope.clone();

    // This allows to save a `Rope` to disk in a background thread while
    // keeping the main thread responsive.

    thread::spawn(move || {
        let mut file =
            BufWriter::new(File::create("my_little_poem.txt").unwrap());

        // The text content is stored in the leaves of the B-tree, where each
        // chunk can store up to 1KB of data.
        //
        // We can iterate over those leaves via the `Chunks` iterator which
        // yields the chunks of the `Rope` as string slices.

        for chunk in cloned.chunks() {
            file.write_all(chunk.as_bytes()).unwrap();
        }
    })
    .join()
    .unwrap();
}
