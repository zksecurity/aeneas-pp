//@ [!lean] skip
//! Joins after matching on a value returned by a call, which holds borrows in
//! some branches only: the call's region abstraction ends early in the other
//! branches.
#![feature(register_tool)]
#![register_tool(verify)]

pub fn get_or_zero(v: &[u32], i: usize) -> u32 {
    match v.get(i) {
        Some(x) => *x,
        None => 0,
    }
}

fn first_mut_if_long(a: &mut [u32]) -> Option<&mut u32> {
    if a.len() > 3 {
        return Some(&mut a[0]);
    }
    None
}

pub fn is_short(a: &mut [u32]) -> bool {
    matches!(first_mut_if_long(a), None)
}

pub fn bump_first_if_long(a: &mut [u32]) -> u32 {
    let n = match first_mut_if_long(a) {
        Some(x) => {
            *x += 1;
            *x
        }
        None => 0,
    };
    n + a[0]
}

#[verify::test]
pub fn test_get_or_zero() {
    let v = [1, 2, 3];
    assert!(get_or_zero(&v, 1) == 2);
    assert!(get_or_zero(&v, 5) == 0);
}

#[verify::test]
pub fn test_is_short() {
    let mut a = [1, 2, 3];
    assert!(is_short(&mut a));
    let mut b = [1, 2, 3, 4];
    assert!(!is_short(&mut b));
}

#[verify::test]
pub fn test_bump_first_if_long() {
    let mut a = [1, 2, 3];
    assert!(bump_first_if_long(&mut a) == 1);
    let mut b = [1, 2, 3, 4];
    assert!(bump_first_if_long(&mut b) == 4);
    assert!(b[0] == 2);
}
