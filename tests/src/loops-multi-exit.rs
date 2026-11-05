//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! Loops with several exits: early returns, and breaks and continues to outer
//! loops.
#![feature(register_tool)]
#![register_tool(verify)]

/// An early return from a loop.
pub fn find(a: &[u32], x: u32) -> Option<usize> {
    let mut i = 0;
    while i < a.len() {
        if a[i] == x {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// A loop which only exits by returning.
pub fn first_above(a: &[u32], x: u32) -> u32 {
    let mut i = 0;
    loop {
        if i >= a.len() {
            return 0;
        }
        if a[i] > x {
            return a[i];
        }
        i += 1;
    }
}

/// An early return after mutating through a borrow live across the iterations.
pub fn add_until(a: &mut [u32], stop: u32) -> Result<u32, u32> {
    let mut s = 0;
    let mut i = 0;
    while i < a.len() {
        if a[i] == stop {
            a[i] = 0;
            return Err(s);
        }
        a[i] += 1;
        s += a[i];
        i += 1;
    }
    Ok(s)
}

/// An early return through a reborrow which lives across the iterations.
pub fn bump_until(a: &mut [u32; 2], n: u32) -> u32 {
    let r = &mut a[0];
    let mut i = 0;
    while i < n {
        *r += 1;
        if *r > 10 {
            return i;
        }
        i += 1;
    }
    a[1] += 1;
    a[0] + a[1]
}

/// Breaks and continues to the outer loop, after several inner iterations.
pub fn outer_exits(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    'outer: while i < n {
        i += 1;
        let mut j = 0;
        while j < n {
            j += 1;
            if j == i {
                continue 'outer;
            }
            if i * j > 12 {
                break 'outer;
            }
            s += j;
        }
        s += 100;
    }
    s + i
}

/// A return from a nested loop, mutating through the borrow on the way.
pub fn nested_return(m: &mut [[u32; 3]; 3], x: u32) -> Option<(usize, usize)> {
    let mut i = 0;
    while i < 3 {
        let mut j = 0;
        while j < 3 {
            if m[i][j] == x {
                m[i][j] = 0;
                return Some((i, j));
            }
            m[i][j] += 1;
            j += 1;
        }
        i += 1;
    }
    None
}

/// Several returns and breaks to the same destinations, with different values.
pub fn classify(a: &[i32]) -> i32 {
    let mut i = 0;
    let mut neg = 0;
    while i < a.len() {
        let v = a[i];
        i += 1;
        if v == 0 {
            break;
        }
        if v < -100 {
            return -1;
        }
        if v > 100 {
            return 1;
        }
        if v < 0 {
            neg += 1;
            if neg > 2 {
                break;
            }
        }
    }
    neg * 10 + i as i32
}

/// An early return of a mutable borrow into the slice.
pub fn find_mut(a: &mut [u32], x: u32) -> Option<&mut u32> {
    let mut i = 0;
    while i < a.len() {
        if a[i] == x {
            return Some(&mut a[i]);
        }
        i += 1;
    }
    None
}

pub enum List {
    Cons(u32, Box<List>),
    Nil,
}

/// A return of a mutable borrow into a list, from a loop which only exits by
/// returning.
pub fn nth_mut(l: &mut List, n: u32) -> Option<&mut u32> {
    let mut l = l;
    let mut i = 0;
    loop {
        match l {
            List::Cons(x, tl) => {
                if i == n {
                    return Some(x);
                }
                i += 1;
                l = tl;
            }
            List::Nil => return None,
        }
    }
}

/// Exits of an inner loop whose outputs overlap without being equal: the
/// continue uses [s], the break [t], the normal exit [i].
pub fn overlapping_outputs(a: &[u32], k: u32) -> u32 {
    let mut total = 0;
    let mut t = 0;
    let mut j = 0;
    'outer: while j < 3 {
        j += 1;
        let mut i = 0;
        let mut s = 0;
        while i < a.len() {
            if a[i] == k + j {
                total += s;
                continue 'outer;
            }
            if a[i] > 100 {
                t = a[i];
                break 'outer;
            }
            s += a[i];
            i += 1;
        }
        total += i as u32;
    }
    total + t + j
}

/// Several exits to the same outer destinations through a mutable borrow
/// live across the inner iterations, written back after the loops.
pub fn bump_rows(m: &mut [[u32; 2]; 2], x: u32) -> u32 {
    let mut i = 0;
    'outer: while i < 2 {
        let row = &mut m[i];
        i += 1;
        let mut j = 0;
        while j < 2 {
            if row[j] == x {
                row[j] += 10;
                break 'outer;
            }
            if row[j] == x + 1 {
                break 'outer;
            }
            if row[j] > 50 {
                row[j] = 0;
                continue 'outer;
            }
            row[j] += 1;
            j += 1;
        }
    }
    m[0][0] + m[0][1] + m[1][0] + m[1][1]
}

/// An early return, and statements with calls and a write after the loop,
/// which go to the place which breaks out of it.
pub fn push_until(v: &mut Vec<u32>, a: &[u32], base: u32) -> u32 {
    let mut i = 0;
    while i < a.len() {
        if a[i] == 0 {
            return base;
        }
        if a[i] > 10 {
            break;
        }
        v.push(a[i]);
        i += 1;
    }
    v.push(base);
    let n = v.len();
    base + n as u32 + i as u32
}

/// A loop with an early return, followed by a loop.
pub fn return_then_loop(a: &[u32], x: u32) -> u32 {
    let mut i = 0;
    while i < a.len() {
        if a[i] == x {
            return 100;
        }
        i += 1;
    }
    let mut s = 0;
    while i > 0 {
        i -= 1;
        s += a[i];
    }
    s
}

/// Two loops with early returns in sequence: only the straight-line code
/// after the second one goes to the places which break out of it.
pub fn two_searches(a: &[u32], x: u32, y: u32) -> u32 {
    let mut i = 0;
    while i < a.len() {
        if a[i] == x {
            return 100;
        }
        if a[i] > 50 {
            break;
        }
        i += 1;
    }
    let mut j = 0;
    while j < a.len() {
        if a[j] == y {
            return 200;
        }
        if a[j] > 60 {
            break;
        }
        j += 1;
    }
    (i + j) as u32
}

#[verify::test]
pub fn test_find() {
    let a = [3, 5, 7];
    assert!(matches!(find(&a, 5), Some(1)));
    assert!(matches!(find(&a, 4), None));
}

#[verify::test]
pub fn test_first_above() {
    let a = [3, 5, 7];
    assert!(first_above(&a, 4) == 5);
    assert!(first_above(&a, 9) == 0);
}

#[verify::test]
pub fn test_add_until() {
    let mut a = [1, 2, 3];
    assert!(matches!(add_until(&mut a, 3), Err(5)));
    assert!(a[0] == 2 && a[1] == 3 && a[2] == 0);
    assert!(matches!(add_until(&mut a, 9), Ok(8)));
    assert!(a[0] == 3 && a[1] == 4 && a[2] == 1);
}

#[verify::test]
pub fn test_bump_until() {
    let mut a = [8, 0];
    assert!(bump_until(&mut a, 2) == 11);
    assert!(a[0] == 10 && a[1] == 1);
    assert!(bump_until(&mut a, 5) == 0);
    assert!(a[0] == 11 && a[1] == 1);
}

#[verify::test]
pub fn test_outer_exits() {
    assert!(outer_exits(3) == 7);
    assert!(outer_exits(5) == 18);
}

#[verify::test]
pub fn test_nested_return() {
    let mut m = [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
    assert!(matches!(nested_return(&mut m, 5), Some((1, 1))));
    assert!(m[0][0] == 2 && m[0][2] == 4 && m[1][0] == 5 && m[1][1] == 0 && m[1][2] == 6);
    assert!(matches!(nested_return(&mut m, 100), None));
    assert!(m[2][2] == 10 && m[1][1] == 1);
}

#[verify::test]
pub fn test_classify() {
    assert!(classify(&[1, -2, 0, 500]) == 13);
    assert!(classify(&[1, 500, -500]) == 1);
    assert!(classify(&[-1, -2, -3, -4]) == 33);
    assert!(classify(&[-500]) == -1);
    assert!(classify(&[5, 6]) == 2);
}

#[verify::test]
pub fn test_find_mut() {
    let mut a = [3, 5, 7];
    if let Some(r) = find_mut(&mut a, 5) {
        *r = 6;
    }
    if let Some(r) = find_mut(&mut a, 5) {
        *r = 0;
    }
    assert!(a[0] == 3 && a[1] == 6 && a[2] == 7);
}

#[verify::test]
pub fn test_nth_mut() {
    let mut l = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
    if let Some(r) = nth_mut(&mut l, 1) {
        *r = 5;
    }
    if let Some(r) = nth_mut(&mut l, 2) {
        *r = 0;
    }
    let mut s = 0;
    if let Some(r) = nth_mut(&mut l, 0) {
        s += *r;
    }
    if let Some(r) = nth_mut(&mut l, 1) {
        s += *r;
    }
    assert!(s == 6);
}

#[verify::test]
pub fn test_overlapping_outputs() {
    assert!(overlapping_outputs(&[1, 2, 3], 1) == 10);
    assert!(overlapping_outputs(&[1, 200, 3], 9) == 201);
    assert!(overlapping_outputs(&[5, 6], 0) == 9);
}

#[verify::test]
pub fn test_bump_rows() {
    let mut m = [[1, 2], [3, 4]];
    assert!(bump_rows(&mut m, 2) == 21);
    assert!(m[0][0] == 2 && m[0][1] == 12);
    let mut m = [[60, 2], [3, 5]];
    assert!(bump_rows(&mut m, 4) == 11);
    assert!(m[0][0] == 0 && m[1][0] == 4 && m[1][1] == 5);
}

#[verify::test]
pub fn test_push_until() {
    let mut v = Vec::new();
    assert!(push_until(&mut v, &[1, 2, 20, 3], 5) == 10);
    assert!(v.len() == 3);
    assert!(push_until(&mut v, &[1, 0], 5) == 5);
    assert!(v.len() == 4);
}

#[verify::test]
pub fn test_return_then_loop() {
    assert!(return_then_loop(&[1, 2, 3], 2) == 100);
    assert!(return_then_loop(&[1, 2, 3], 5) == 6);
}

#[verify::test]
pub fn test_two_searches() {
    assert!(two_searches(&[1, 2, 3], 2, 9) == 100);
    assert!(two_searches(&[1, 70, 3], 9, 3) == 2);
    assert!(two_searches(&[1, 2], 9, 2) == 200);
    assert!(two_searches(&[1, 2], 9, 9) == 4);
}
