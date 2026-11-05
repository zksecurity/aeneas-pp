//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Loops over iterators of shared references: shared values containing shared borrows in joins.
#![feature(register_tool)]
#![register_tool(verify)]

/// A loop over an iterator of shared references, with an early return.
pub fn all_nonzero(xs: &[&u32]) -> Result<(), ()> {
    for x in xs {
        if **x == 0 {
            return Err(());
        }
    }
    Ok(())
}

/// A loop over an iterator of shared references.
pub fn sum_refs(xs: &[&u32]) -> u32 {
    let mut s = 0;
    for x in xs {
        s += **x;
    }
    s
}

#[verify::test]
pub fn test_all_nonzero() {
    let (a, b, z) = (3, 4, 0);
    assert!(matches!(all_nonzero(&[&a, &b]), Ok(())));
    assert!(matches!(all_nonzero(&[&a, &z]), Err(())));
}

#[verify::test]
pub fn test_sum_refs() {
    let (a, b) = (3, 4);
    assert!(sum_refs(&[&a, &b]) == 7);
}
