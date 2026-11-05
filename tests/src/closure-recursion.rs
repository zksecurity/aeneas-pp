//@ [!lean] skip
//! Functions which are mutually recursive with closures: the closures call the
//! functions which create them, through generic helpers.
#![feature(register_tool)]
#![register_tool(verify)]

fn apply<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

fn apply_twice<F: FnMut(u32) -> u32>(mut f: F, x: u32) -> u32 {
    let y = f(x);
    f(y)
}

fn apply_once<F: FnOnce(u32) -> u32>(f: F, x: u32) -> u32 {
    if x > 1000 {
        return 0;
    }
    f(x)
}

/// Recursion through a `Fn` closure.
pub fn sum_to(n: u32) -> u32 {
    if n == 0 { 0 } else { n + apply(|k| sum_to(k), n - 1) }
}

/// Recursion through a `FnMut` closure capturing a value.
pub fn steps(n: u32) -> u32 {
    if n < 2 {
        return n;
    }
    let d = 1;
    apply_twice(|k| if k == 0 { 0 } else { steps(k - d) }, n - 1) + 1
}

/// Two functions recursing through each other's closures.
pub fn even(n: u32) -> bool {
    if n == 0 { true } else { apply_once(|k| if odd(k) { 1 } else { 0 }, n - 1) == 1 }
}

pub fn odd(n: u32) -> bool {
    if n == 0 { false } else { apply_once(|k| if even(k) { 1 } else { 0 }, n - 1) == 1 }
}

#[verify::test]
pub fn test_sum_to() {
    assert!(sum_to(5) == 15);
}

#[verify::test]
pub fn test_steps() {
    assert!(steps(1) == 1);
    assert!(steps(4) == 1);
}

#[verify::test]
pub fn test_even_odd() {
    assert!(even(4) && !even(3) && odd(5) && !odd(2));
}
