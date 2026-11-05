//@ [!lean] skip
//! Casts from characters to integers.
#![feature(register_tool)]
#![register_tool(verify)]

fn code(c: char) -> u32 {
    c as u32
}

fn low_byte(c: char) -> u8 {
    c as u8
}

fn signed_low_byte(c: char) -> i8 {
    c as i8
}

#[verify::test]
fn test_casts() {
    assert!(code('λ') == 955);
    assert!(code('\n') == 10);
    assert!(low_byte('λ') == 187);
    assert!(signed_low_byte('λ') == -69);
}
