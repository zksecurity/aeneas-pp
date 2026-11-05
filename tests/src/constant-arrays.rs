//@ [!lean] skip
//! Array constants, which byte string literals become.
#![feature(register_tool)]
#![register_tool(verify)]

/// A byte string with a repeated byte: its constant is a repeat.
pub fn braces() -> u8 {
    let a = *b"}}";
    a[0] + a[1]
}

pub fn bytes_sum() -> u32 {
    let a = *b"ab}";
    a[0] as u32 + a[1] as u32 + a[2] as u32
}

#[verify::test]
pub fn test_braces() {
    assert!(braces() == 250);
}

#[verify::test]
pub fn test_bytes_sum() {
    assert!(bytes_sum() == 97 + 98 + 125);
}
