//@ [!lean] skip
//! Globals whose types contain static borrows.
#![feature(register_tool)]
#![register_tool(verify)]

const NAMES: [&str; 2] = ["a", "bc"];
const LIMITS: [&u32; 2] = [&3, &7];

fn name(i: usize) -> &'static str {
    NAMES[i]
}

fn limit_sum() -> u32 {
    *LIMITS[0] + *LIMITS[1]
}

#[verify::test]
fn test_limit_sum() {
    assert!(limit_sum() == 10);
}
