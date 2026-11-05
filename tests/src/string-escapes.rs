//@ [!lean] skip
//! String literals with characters which must be escaped, and long literals.

pub const QUOTES: &str = "{\"meta\":\"\\u03b1\"}\n";
pub const CONTROL: &str = "tab\tcr\rnul\0del\x7f";
pub const UNICODE: &str = "αβ ∀";

pub fn quoted() -> &'static str {
    "say \"hi\""
}

macro_rules! x16 {
    ($s:expr) => {
        concat!($s, $s, $s, $s, $s, $s, $s, $s, $s, $s, $s, $s, $s, $s, $s, $s)
    };
}

/// 12032 bytes
pub const LONG: &str = x16!(x16!("{\"in\":2,\"str\":{\"pre\":0,\"str\":\"u\"}}\n0123456789ab"));
