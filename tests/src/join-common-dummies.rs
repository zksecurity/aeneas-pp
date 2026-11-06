//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! The exits of a forward scope share the dummy values created inside it
//! before they diverge (here the reborrow of [t] which [ck] holds): the join
//! keeps them as dummy values in every exit.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Checker<'a> {
    pub t: &'a mut u32,
}

pub fn infer(ck: &mut Checker<'_>) -> Result<(), ()> {
    if *ck.t > 10 {
        return Err(());
    }
    *ck.t += 1;
    Ok(())
}

pub fn verify(t: &mut u32, b: bool) -> Result<(), ()> {
    let mut ck = Checker { t: &mut *t };
    if b {
        infer(&mut ck)?;
    }
    infer(&mut ck)?;
    Ok(())
}

#[verify::test]
pub fn test_verify() {
    let mut t = 0;
    assert!(matches!(verify(&mut t, true), Ok(())));
    assert!(t == 2);
    assert!(matches!(verify(&mut t, false), Ok(())));
    assert!(t == 3);
    let mut t = 11;
    assert!(matches!(verify(&mut t, true), Err(())));
    assert!(t == 11);
    let mut t = 10;
    assert!(matches!(verify(&mut t, true), Err(())));
    assert!(t == 11);
}
