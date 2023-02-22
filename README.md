# 🌾 crop

[![Latest version]](https://crates.io/crates/crop)
[![CI]](https://github.com/noib3/crop/actions)
[![Docs]](https://docs.rs/crop)

[Latest version]: https://img.shields.io/crates/v/crop.svg
[CI]: https://github.com/noib3/crop/actions/workflows/ci.yml/badge.svg
[Docs]: https://docs.rs/crop/badge.svg

crop is an implementation of a UTF-8 text rope, a data structure designed to
be used in applications that need to handle frequent edits to arbitrarily large
buffers, such as text editors.

crop's `Rope` is backed by a [B-tree](https://en.wikipedia.org/wiki/B-tree),
ensuring that the time complexity of inserting, deleting or replacing a piece
of text is always logarithmic in the size of the `Rope`.

crop places an extreme focus on performance: check out [the
benchmarks](https://github.com/noib3/crop/blob/master/benches/README.md) to see
how it stacks up against similar projects.

## Example usage

```rust
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
// `RopeSlice` is to a `Rope` as a `&str` is to a `String`: the former in
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

// and replacing it with some other text:

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

    // The text content is stored in the leaves of the B-tree, with each
    // leaf being able to store up to a 1KB chunk of data.
    //
    // We can iterate over the leaves using the `Chunks` iterator which
    // yields the chunks of the `Rope` as string slices.

    for chunk in cloned.chunks() {
        file.write_all(chunk.as_bytes()).unwrap();
    }
})
.join()
.unwrap();
```

Check out [the docs](https://docs.rs/crop) for a more in-depth overview of the
crate.

## Acknowledgements

A significant portion of crop's public API was inspired by the excellent
[Ropey](https://github.com/cessen/ropey) crate (from which I also borrowed some
test vectors).

Unlike crop, Ropey uses code points (`char`s in Rust-speak) as its primary
indexing metric. If you'd prefer to work with `char`-offsets rather than
byte-offsets Ropey might be a great alternative.
