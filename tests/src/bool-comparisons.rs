//@ [!lean] skip
//! Comparisons used as booleans in branches whose type Lean does not know yet.
#![feature(register_tool)]
#![register_tool(verify)]

pub fn first(o: Option<u64>, d: bool, n: u32) -> bool {
    let b = match o {
        None => n == 0,
        Some(_) => d,
    };
    !b
}

pub fn pair(o: Option<u64>, d: bool, n: u32) -> (bool, u32) {
    let (b, m) = match o {
        None => (n < 3, n),
        Some(_) => (d, n + 1),
    };
    (b, m + 1)
}

#[verify::test]
pub fn test_comparisons() {
    assert!(!first(None, true, 0));
    assert!(first(Some(1), false, 0));
    assert!(matches!(pair(None, false, 2), (true, 3)));
    assert!(matches!(pair(Some(0), false, 2), (false, 4)));
}
