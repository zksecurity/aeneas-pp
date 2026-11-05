//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins after matching on the variant of a shared enumeration: the branches
//! expand the value shared by the input abstractions differently.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum E<'a> {
    A,
    B(&'a u32),
}

pub enum F<'a> {
    A(u32),
    B(&'a u32),
}

pub fn is_b(t: &E<'_>) -> u32 {
    match t {
        E::B(_) => 1,
        _ => 0,
    }
}

pub fn is_fb(t: &F<'_>) -> u32 {
    match t {
        F::B(_) => 1,
        F::A(_) => 0,
    }
}

pub fn get(t: &F<'_>) -> u32 {
    match t {
        F::A(n) => *n,
        F::B(x) => **x,
    }
}

/// The branches borrow the fields of the variants, and copy their values out
/// of them. We use the enumeration again after the join.
pub fn get_twice(t: &F<'_>) -> u32 {
    let n = match t {
        F::B(x) => **x,
        F::A(n) => *n,
    };
    n + get(t)
}

#[verify::test]
pub fn test_shared_enum_joins() {
    let x = 3;
    assert!(is_b(&E::B(&x)) == 1);
    assert!(is_b(&E::A) == 0);
    assert!(is_fb(&F::B(&x)) == 1);
    assert!(is_fb(&F::A(2)) == 0);
    assert!(get_twice(&F::B(&x)) == 6);
    assert!(get_twice(&F::A(2)) == 4);
}
