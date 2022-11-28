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
