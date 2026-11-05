//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! A loop evaluated in the exit branch of an enclosing loop (the code after a
//! loop with an early return) while a structure holding mutable borrows is
//! borrowed by the loop abstractions of the enclosing loop.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Engine<'a> {
    pub total: &'a mut u32,
    pub bound: &'a u32,
}

fn step(e: &mut Engine<'_>, x: u32) -> Result<u32, ()> {
    if x < *e.bound {
        *e.total += x;
        Ok(x + 1)
    } else {
        Err(())
    }
}

pub fn steps(e: &mut Engine<'_>, k: u32, i: u32) -> Result<u32, ()> {
    let mut x = 0;
    for _ in 0..k {
        x = step(e, x)?;
    }
    for _ in 0..i {
        x = step(e, x)?;
    }
    Ok(x)
}

#[verify::test]
pub fn test_steps() {
    let mut total = 0;
    let bound = 10;
    let mut e = Engine { total: &mut total, bound: &bound };
    assert!(matches!(steps(&mut e, 2, 3), Ok(5)));
    assert!(*e.total == 10);
    let bound = 3;
    let mut total = 0;
    let mut e = Engine { total: &mut total, bound: &bound };
    assert!(matches!(steps(&mut e, 2, 3), Err(())));
    assert!(*e.total == 3);
}
