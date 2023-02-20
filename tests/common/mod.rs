#![allow(dead_code)]

pub const TINY: &str = include_str!("../../benches/tiny.txt");
pub const SMALL: &str = include_str!("../../benches/small.txt");
pub const MEDIUM: &str = include_str!("../../benches/medium.txt");
pub const LARGE: &str = include_str!("../../benches/large.txt");

/// A cursed version of a lorem ipsum paragraph taken from [this online
/// tool][1] with mixed line breaks (LF and CRLF).
///
/// [1]: https://jeff.cis.cabrillo.edu/tools/homoglyphs
pub const CURSED_LIPSUM: &str = "Ḽơᶉëᶆ ȋṕšᶙṁ\nḍỡḽǭᵳ ʂǐť ӓṁệẗ,\r\n \
                                 ĉṓɲṩḙċťᶒțûɾ \nấɖḯƥĭ\r\nṩčįɳġ ḝłįʈ, șế\r\nᶑ \
                                 ᶁⱺ ẽḭŭŝḿꝋď\n ṫĕᶆᶈṓɍ ỉñḉīḑȋᵭṵńť \nṷŧ ḹẩḇőꝛế \
                                 éȶ đꝍꞎ\r\nôꝛȇ ᵯáꞡ\r\nᶇā ąⱡ\nîɋṹẵ.";

// The following test vectors were taken from Ropey.

/// 127 bytes, 103 chars, 1 line
pub const TEXT: &str = "Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?  \
                        こんにちは、みんなさん！";

/// 124 bytes, 100 chars, 4 lines
pub const TEXT_LINES: &str = "Hello there!  How're you doing?\nIt's a fine \
                              day, isn't it?\nAren't you glad we're \
                              alive?\nこんにちは、みんなさん！";

/// 127 bytes, 107 chars, 111 utf16 code units, 1 line
pub const TEXT_EMOJI: &str = "Hello there!🐸  How're you doing?🐸  It's a \
                              fine day, isn't it?🐸  Aren't you glad we're \
                              alive?🐸  こんにちは、みんなさん！";
