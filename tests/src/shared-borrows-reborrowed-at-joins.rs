//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins reborrowing shared values which contain shared borrows: the reborrows
//! remain covered by the owners of the inner borrows.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct P<'b> {
    r: &'b u32,
    n: u32,
}

fn id_ref<'b>(r: &'b u32) -> &'b u32 {
    r
}

/// A join over a reborrow of `p`, after which the inner reference goes through
/// a call and outlives the reborrow.
pub fn pick<'a, 'b>(p: &'a P<'b>, b: bool) -> &'b u32 {
    let n = if b { p.n } else { 0 };
    let r = id_ref(p.r);
    if n == 0 { r } else { id_ref(p.r) }
}

/// A loop over a reborrow of a local whose inner reference outlives the
/// reborrow, then the owner of the inner reference is updated.
pub fn loop_local(n: u32) -> u32 {
    let mut v = 3u32;
    let p = P { r: &v, n };
    let q = &p;
    let mut i = 0;
    let mut s = 0;
    while i < q.n {
        s += *id_ref(q.r);
        i += 1;
    }
    let r = id_ref(q.r);
    let x = *r;
    v = 4;
    x + v + s
}

/// A join over a reborrow of a slice of references, after which an element
/// goes through a call.
pub fn first_or<'a, 'b>(xs: &'a [&'b u32], d: &'b u32, b: bool) -> &'b u32 {
    let n = if b { xs.len() } else { 0 };
    let r = if n > 0 { id_ref(xs[0]) } else { d };
    r
}

#[verify::test]
pub fn test_pick() {
    let (x, y) = (3, 4);
    let p = P { r: &x, n: 0 };
    assert!(*pick(&p, true) == 3);
    let q = P { r: &y, n: 1 };
    assert!(*pick(&q, true) == 4);
}

#[verify::test]
pub fn test_loop_local() {
    assert!(loop_local(0) == 7);
    assert!(loop_local(2) == 13);
}

#[verify::test]
pub fn test_first_or() {
    let (x, y, d) = (3, 4, 5);
    assert!(*first_or(&[&x, &y], &d, true) == 3);
    assert!(*first_or(&[&x, &y], &d, false) == 5);
    assert!(*first_or(&[], &d, true) == 5);
}
