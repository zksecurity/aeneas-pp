//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! Function items whose signatures have late-bound regions, used as closures.
#![feature(register_tool)]
#![register_tool(verify)]

fn is_zero(x: &u32) -> bool {
    *x == 0
}

pub struct W {
    pub v: u32,
}

fn inner(w: &W) -> &u32 {
    &w.v
}

fn apply<F: Fn(&u32) -> bool>(f: F, x: u32) -> bool {
    f(&x)
}

fn apply_mut<F: FnMut(&mut u32)>(mut f: F, x: u32) -> u32 {
    let mut y = x;
    f(&mut y);
    f(&mut y);
    y
}

fn incr(x: &mut u32) {
    *x += 1;
}

pub fn zero_first(v: Option<u32>) -> bool {
    v.is_some_and(|x| is_zero(&x))
}

pub fn via_apply(x: u32) -> bool {
    apply(is_zero, x)
}

pub fn via_apply_mut(x: u32) -> u32 {
    apply_mut(incr, x)
}

pub fn first_inner(w: Option<&W>) -> Option<&u32> {
    w.map(inner)
}

#[verify::test]
pub fn test_fn_items() {
    assert!(via_apply(0));
    assert!(!via_apply(1));
    assert!(via_apply_mut(5) == 7);
    assert!(zero_first(Some(0)));
    let w = W { v: 3 };
    assert!(matches!(first_inner(Some(&w)), Some(3)));
}
