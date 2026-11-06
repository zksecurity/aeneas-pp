//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Loop joins after matching on the variant of a shared enumeration: the
//! iterations expand the value shared by the input abstractions, together with
//! the loan projectors over its borrows.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum F<'a> {
    A(u32),
    B(&'a u32),
}

pub fn get(t: &F<'_>) -> u32 {
    match t {
        F::A(n) => *n,
        F::B(x) => **x,
    }
}

pub fn sum(t: &F<'_>, mut i: u32) -> u32 {
    let mut acc = 0;
    while i != 0 {
        i -= 1;
        acc += match t {
            F::A(n) => *n,
            F::B(x) => **x,
        };
    }
    acc
}

/// The loop breaks after matching on the enumeration, which we use again
/// after the loop.
pub fn count_until(t: &F<'_>, x: u32, mut i: u32) -> u32 {
    while i != 0 {
        i -= 1;
        match t {
            F::A(n) if *n == x => break,
            _ => (),
        }
    }
    i + get(t)
}

/// The loop breaks after matching on the enumeration.
pub fn has_a(t: &F<'_>, mut i: u32) -> bool {
    let mut found = false;
    while i != 0 {
        i -= 1;
        match t {
            F::A(_) => {
                found = true;
                break;
            }
            _ => (),
        }
    }
    found
}

#[verify::test]
pub fn test_shared_enum_loop_joins() {
    let x = 3;
    assert!(sum(&F::A(2), 3) == 6);
    assert!(sum(&F::B(&x), 2) == 6);
    assert!(count_until(&F::A(4), 4, 2) == 5);
    assert!(count_until(&F::A(4), 5, 2) == 4);
    assert!(count_until(&F::B(&x), 3, 2) == 3);
    assert!(has_a(&F::A(4), 1));
    assert!(!has_a(&F::A(4), 0));
    assert!(!has_a(&F::B(&x), 2));
}
