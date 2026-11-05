//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins where a value holding shared borrows is live in one branch only.
#![feature(register_tool)]
#![register_tool(verify)]

/// A number which is borrowed or owned: dropping it runs drop glue.
pub enum Number<'a> {
    Borrowed(&'a u32),
    Owned(Vec<u32>),
}

pub fn decode(x: &u32, owned: bool) -> Option<Number<'_>> {
    if owned {
        Some(Number::Owned(Vec::new()))
    } else {
        Some(Number::Borrowed(x))
    }
}

pub fn value(n: Number<'_>) -> u32 {
    match n {
        Number::Borrowed(x) => *x,
        Number::Owned(_) => 0,
    }
}

/// The first number is live on the path which decodes the second one only.
pub fn sum(x: &u32, y: &u32, owned: bool) -> Option<u32> {
    let a = match decode(x, owned) {
        Some(a) => a,
        None => return None,
    };
    let b = match decode(y, owned) {
        Some(b) => b,
        None => return None,
    };
    Some(value(a) + value(b))
}

#[verify::test]
pub fn test_sum() {
    assert!(matches!(sum(&1, &2, false), Some(3)));
    assert!(matches!(sum(&1, &2, true), Some(0)));
}
