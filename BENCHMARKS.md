# Benchmarks

The following benchmarks measure crop's performance against
[Jumprope][jumprope] and [Ropey][ropey] across 4 different use cases:

- [creating](#creation) a rope from a string or using a builder;
- [slicing](#slices) the rope and converting the slice back to an owned `Rope`;
- [iterating](#iterators) over the rope's chunks, bytes, `char`s, and lines;
- [editing](#edits) the rope by continuously inserting/deleting/replacing text
  at random offsets;

using 4 different input texts to track the change in performance as the size of
the underlying buffer increases:

- [tiny.txt][tiny]: 669 bytes, 9 lines;
- [small.txt][small]: 1.5 KB, 20 lines;
- [medium.txt][medium]: 219 KB, 3086 lines;
- [large.txt][large]: 1.5 MB, 21596 lines.

It wasn't possible to add Jumprope to the `builder` and `*_slice` benchmarks
because it doesn't provide similar APIs, and it wasn't included in the `iter_*`
benchmarks because even though
[some](https://docs.rs/jumprope/latest/jumprope/struct.JumpRope.html#method.slice_chars)
[iterators](https://docs.rs/jumprope/latest/jumprope/struct.JumpRope.html#method.substrings)
are implemented, they are not exported publicly.

The `xi_rope` project was not included in the benchmarks as it's been
discontinued together with the rest of the Xi editor (and it was about an order
of magnitude slower that all the other ropes on most use cases).

The code used to run the benchmarks can be found
[here](https://github.com/noib3/rope_benches).

All the benchmarks were run on a 2018 MacBook Pro with a (not so) mighty 2.2
GHz 6-Core Intel Core i7.

## Creation

| `cargo bench from_str` | `cargo bench builder` |
|          :--:          |         :--:          |
| ![from_str][from_str]  | ![builder][builder]   |

## Slices

|  `cargo bench byte_slice`  | `cargo bench line_slice`  |
|            :--:            |            :--:           |
| ![byte_slice][byte_slice]  | ![line_slice][line_slice] |

|       `cargo bench from_slice`      |      |
|                 :--:                | :--: |
| ![from_slice][from_slice] | &emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&nbsp; |

## Iterators

| `cargo bench iter_chunks`   | `cargo bench iter_bytes`  |
|             :--:            |            :--:           |
| ![iter_chunks][iter_chunks] | ![iter_bytes][iter_bytes] |

| `cargo bench iter_chars`  | `cargo bench iter_lines`  |
|            :--:           |            :--:           |
| ![iter_chars][iter_chars] | ![iter_lines][iter_lines] |


## Edits

| `cargo bench insert_char`   |    `cargo bench insert_sentence`    |
|             :--:            |                 :--:                |
| ![insert_char][insert_char] | ![insert_sentence][insert_sentence] |

|  `cargo bench insert_large`   |  `cargo bench delete_char`  |
|              :--:             |             :--:            |
| ![insert_large][insert_large] | ![delete_char][delete_char] |

| `cargo bench delete_sentence`       |  `cargo bench delete_large`   |
|                 :--:                |              :--:             |
| ![delete_sentence][delete_sentence] | ![delete_large][delete_large] |

|  `cargo bench replace_char`   |    `cargo bench replace_sentence`     |
|              :--:             |                  :--:                 |
| ![replace_char][replace_char] | ![replace_sentence][replace_sentence] |

|   `cargo bench replace_large`   |      |
|               :--:              | :--: |
| ![replace_large][replace_large] | &emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&nbsp; |

<!-- ## Traces -->

<!-- | `cargo run --release -- --bench traces` | -->
<!-- |  :--:  | -->
<!-- | ![traces][traces] | -->

[jumprope]: https://github.com/josephg/jumprope-rs
[ropey]: https://github.com/cessen/ropey

[tiny]: https://github.com/noib3/rope_benches/blob/master/benches/common/tiny.txt
[small]: https://github.com/noib3/rope_benches/blob/master/benches/common/small.txt
[medium]: https://github.com/noib3/rope_benches/blob/master/benches/common/medium.txt
[large]: https://github.com/noib3/rope_benches/blob/master/benches/common/large.txt

[builder]: https://user-images.githubusercontent.com/59321248/227067900-48478bca-8fe9-403d-a92e-e95bd94e2ebc.png
[byte_slice]: https://user-images.githubusercontent.com/59321248/232328565-ac74e6b6-07cb-40b3-8379-7e9e3f47acad.png
[delete_char]: https://user-images.githubusercontent.com/59321248/227067911-3509f006-3830-4d36-b8f5-8c78bb684b11.png
[delete_large]: https://user-images.githubusercontent.com/59321248/227067916-e3ed1bbe-d706-4e53-bbc1-04218c8e46a7.png
[delete_sentence]: https://user-images.githubusercontent.com/59321248/227067918-91af2770-8dea-49ad-a894-50a0cede60cf.png
[from_slice]: https://user-images.githubusercontent.com/59321248/227067921-c97f882f-5f3e-4d6c-8141-f9692c8935ef.png
[from_str]: https://user-images.githubusercontent.com/59321248/227067923-364d6d7a-86f8-46e1-a371-84fda094fb22.png
[insert_char]: https://user-images.githubusercontent.com/59321248/227067924-7ca04879-7c67-423c-ba96-cd3e43d974a5.png
[insert_large]: https://user-images.githubusercontent.com/59321248/227067926-718b5b34-ff89-458b-9906-4ca19ea1f020.png
[insert_sentence]: https://user-images.githubusercontent.com/59321248/227067928-6a69ff30-73ca-4272-9c2d-381064fc9170.png
[iter_bytes]: https://user-images.githubusercontent.com/59321248/227067929-5f067398-4fae-4f7d-9b49-fcb21efba86f.png
[iter_chars]: https://user-images.githubusercontent.com/59321248/227067932-3f8a5207-1c24-4285-8bfe-3f56f2c26a8b.png
[iter_chunks]: https://user-images.githubusercontent.com/59321248/227067937-7fe9e437-5050-4524-b5b0-8ed56d1dd560.png
[iter_lines]: https://user-images.githubusercontent.com/59321248/227067939-4198ed29-e886-4f90-b9bf-33c817a867a8.png
[line_slice]: https://user-images.githubusercontent.com/59321248/227067941-f41c6970-6ee1-4bd9-aa1a-74ffb816af7c.png
[replace_char]: https://user-images.githubusercontent.com/59321248/227067944-bd1931ba-c287-4b0e-a2d6-c3e46dd9d665.png
[replace_large]: https://user-images.githubusercontent.com/59321248/227067948-78cf6e37-e4e6-4689-834b-b087da538054.png
[replace_sentence]: https://user-images.githubusercontent.com/59321248/227067952-a51b5e77-71d9-4e84-acba-a146013e44da.png
<!-- [traces]: https://user-images.githubusercontent.com/59321248/227782573-799d45fb-91d5-4c29-8613-cc8e35eb7a9f.png -->
