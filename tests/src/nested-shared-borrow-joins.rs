//@ [!lean] skip
//! Joins of contexts whose region abstractions hold shared loans of values
//! containing shared borrows (nested shared borrows, e.g. `&&T`).
#![feature(register_tool)]
#![register_tool(verify)]

// ------------------------------------------------------------------
// Comparing references goes through `impl PartialEq<&B> for &A`, which
// borrows a reference: the comparison against a promoted literal leaves
// an abstraction holding a shared loan of a shared borrow. It is the same
// in both branches of every later join.
// ------------------------------------------------------------------

pub fn str_eq_then_branch(a: &str, c: bool) -> u32 {
    let e = if a == "lift" { 10 } else { 20 };
    let r = if c { 1 } else { 2 };
    r + e
}

pub fn str_match_then_branches(kind: &str, n: u32) -> Option<u32> {
    let base = match kind {
        "type" => 1,
        "ctor" => 2,
        "lift" => 3,
        "ind" => 4,
        _ => return None,
    };
    let count = if kind == "lift" { 2 } else { 1 };
    let extra = if count == 2 { n } else { 0 };
    let scaled = if n > 10 { base * 2 } else { base };
    Some(scaled + extra)
}

pub fn ref_eq_then_branch(a: &u32, b: &u32, c: bool) -> u32 {
    let e = if a == b { 10 } else { 20 };
    let r = if c { 1 } else { 2 };
    r + e
}

// ------------------------------------------------------------------
// A nested shared borrow that differs between the branches and is used
// after the join.
// ------------------------------------------------------------------

fn get<'a, 'b>(x: &'a &'b u32) -> &'a &'b u32 {
    x
}

pub fn join_call_and_local(a: &u32, c: bool) -> u32 {
    let aa = &a;
    let r = if c { get(aa) } else { aa };
    **r
}

pub fn join_aliased_handles(a: &u32, c: bool) -> u32 {
    let aa = &a;
    let ab = aa;
    let r = if c { get(aa) } else { ab };
    **r + **ab
}

// ------------------------------------------------------------------
// A mutable borrow updated through a call while a nested shared borrow is
// live across the join: the update must reach the caller.
// ------------------------------------------------------------------

fn bump(x: &mut u32) {
    *x = x.wrapping_add(1);
}

pub fn update_across_join(a: &u32, b: &u32, x: &mut u32, c: bool) {
    if a == b {
        bump(x);
    }
    if c {
        bump(x);
    }
}

// ------------------------------------------------------------------
// The comparison happens inside a branch (dead temporaries meet bottom in
// the other branch).
// ------------------------------------------------------------------

pub fn eq_in_branch(a: &u32, b: &u32, c: bool) -> u32 {
    let e = if c {
        if a == b { 1 } else { 2 }
    } else {
        3
    };
    e + 1
}

// ------------------------------------------------------------------
// Structs holding references, accessed through `&self`/`&mut self`.
// ------------------------------------------------------------------

pub struct Holder<'a> {
    pub r: &'a u32,
}

pub fn holder_branch(h: &Holder<'_>, other: &u32, c: bool) -> u32 {
    let x = if c { h.r } else { other };
    let y = if *x > 3 { 1 } else { 0 };
    *x + y
}

// ------------------------------------------------------------------
// Executed checks
// ------------------------------------------------------------------

#[verify::test]
pub fn test_ref_eq_then_branch() {
    let (a, b) = (3, 3);
    assert!(ref_eq_then_branch(&a, &b, true) == 11);
    assert!(ref_eq_then_branch(&a, &4, false) == 22);
}

#[verify::test]
pub fn test_join_call_and_local() {
    let a = 7;
    assert!(join_call_and_local(&a, true) == 7);
    assert!(join_call_and_local(&a, false) == 7);
}

#[verify::test]
pub fn test_join_aliased_handles() {
    let a = 5;
    assert!(join_aliased_handles(&a, true) == 10);
    assert!(join_aliased_handles(&a, false) == 10);
}

#[verify::test]
pub fn test_update_across_join() {
    let (a, b) = (1, 1);
    let mut x = 0;
    update_across_join(&a, &b, &mut x, true);
    assert!(x == 2);
    update_across_join(&a, &2, &mut x, false);
    assert!(x == 2);
    update_across_join(&a, &2, &mut x, true);
    assert!(x == 3);
}

#[verify::test]
pub fn test_eq_in_branch() {
    let (a, b) = (1, 1);
    assert!(eq_in_branch(&a, &b, true) == 2);
    assert!(eq_in_branch(&a, &2, true) == 3);
    assert!(eq_in_branch(&a, &b, false) == 4);
}

#[verify::test]
pub fn test_holder_branch() {
    let a = 5;
    let h = Holder { r: &a };
    assert!(holder_branch(&h, &2, true) == 6);
    assert!(holder_branch(&h, &2, false) == 2);
}
