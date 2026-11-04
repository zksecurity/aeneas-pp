//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! Control flow reconstructed without duplicating code: Charon introduces
//! `loop { ...; break }` scopes which `break` statements jump forward out of.
#![feature(register_tool)]
#![register_tool(verify)]

#[derive(Clone, Copy)]
pub enum Class {
    Def,
    Ctor,
    Other,
}

#[derive(Clone, Copy)]
pub enum Head {
    Var(u32),
    Const(u32, Class),
}

#[derive(Clone, Copy)]
pub enum Val {
    Neutral(Head, u32),
    Nat(u32),
    Sort,
}

fn check(x: u32) -> Result<u32, u32> {
    if x > 100 { Err(x) } else { Ok(x + 1) }
}

/// Sequences of early returns, `let ... else` and `?`, each with side effects.
pub fn let_else_chain(v: Val, w: Val, acc: &mut u32) -> Result<Option<u32>, u32> {
    *acc += 1;
    let Val::Neutral(Head::Const(c, Class::Ctor), sp) = v else {
        return Ok(None);
    };
    *acc += 1;
    let x = check(c)?;
    let y = match w {
        Val::Nat(n) => check(n)?,
        Val::Sort => return Ok(Some(0)),
        Val::Neutral(Head::Var(i), _) => i,
        Val::Neutral(Head::Const(..), _) => return Err(7),
    };
    *acc += 10;
    let Val::Neutral(Head::Const(d, _), _) = v else {
        return Ok(None);
    };
    Ok(Some(x + y + sp + d))
}

/// Every path returns: the scopes have no normal exit.
pub fn all_return(v: Val) -> u32 {
    match v {
        Val::Neutral(Head::Const(c, Class::Def), _) => {
            if c > 3 {
                return 1;
            }
            return 2;
        }
        Val::Neutral(_, _) => return 3,
        Val::Nat(n) => {
            if n == 0 {
                return 4;
            }
            return 5;
        }
        Val::Sort => return 6,
    }
}

/// The branches of an inner switch skip the code after the switch, jumping to
/// the end of an enclosing scope.
pub fn skip_to_outer(v: Val, b: bool, x: &mut u32) -> u32 {
    let mut r = 0;
    if b {
        match v {
            Val::Nat(n) => {
                *x += n;
                r = n;
            }
            Val::Sort => {
                r = 1;
            }
            Val::Neutral(..) => {
                *x += 100;
            }
        }
        *x += 1;
    } else {
        *x += 2;
    }
    *x + r
}

/// A loop: the forward scopes inside its body break out of it and continue it.
pub fn scopes_in_loop(a: &[Val]) -> u32 {
    let mut n = 0;
    let mut i = 0;
    while i < a.len() {
        let v = a[i];
        i += 1;
        let Val::Neutral(Head::Const(c, cls), _) = v else {
            continue;
        };
        match cls {
            Class::Ctor => n += c,
            Class::Def => {
                if c > 50 {
                    break;
                }
                n += 1;
            }
            Class::Other => continue,
        }
        n += 1;
    }
    n
}

/// Loops which iterate: one which never reaches the end of its body but
/// continues from a nested switch, and one with an implicit backedge.
pub fn real_loops(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    loop {
        if i < n {
            i += 1;
            if i % 2 == 0 {
                s += 1;
                continue;
            }
            s += 2;
            continue;
        }
        break;
    }
    let mut j = 0;
    while j < n {
        j += 1;
        s += j;
    }
    s
}

/// A panic in one branch, returns in others.
pub fn panic_or_return(v: Val, x: u32) -> u32 {
    let y = match v {
        Val::Nat(n) => {
            assert!(n < 50);
            n
        }
        Val::Sort => return x,
        Val::Neutral(Head::Var(i), _) => i,
        Val::Neutral(Head::Const(..), _) => return 0,
    };
    let z = if y > x { y - x } else { return y };
    z + 1
}

/// A loop which iterates, inside a forward scope.
pub fn loop_in_scope(v: Val, n: u32) -> u32 {
    let k = match v {
        Val::Nat(m) => {
            let mut i = 0;
            while i < m {
                i += 1;
            }
            i
        }
        Val::Sort => return n,
        Val::Neutral(..) => 0,
    };
    k + n
}

/// A mutable borrow which lives across the scopes, updated before the early
/// returns and after them.
pub fn live_borrow(a: &mut [u32; 2], v: Val, w: Val) -> u32 {
    let r = &mut a[0];
    *r += 1;
    let Val::Nat(n) = v else {
        return *r;
    };
    *r += n;
    let m = match w {
        Val::Nat(m) => m,
        Val::Sort => {
            *r += 100;
            return 0;
        }
        Val::Neutral(..) => 1,
    };
    *r += m;
    a[1] += *r;
    a[1]
}

/// Like [live_borrow], with the branch ending the borrow first.
pub fn live_borrow_rev(a: &mut [u32; 2], v: Val) -> u32 {
    let r = &mut a[0];
    *r += 1;
    let Val::Nat(n) = v else {
        *r += 2;
        return *r;
    };
    match v {
        Val::Nat(0) => {
            *r += 3;
            a[1] += 1;
        }
        _ => *r += n,
    }
    a[0] + a[1]
}

fn bump_and_get<'a>(a: &'a mut [u32; 2], k: &u32) -> &'a u32 {
    a[0] += *k;
    &a[1]
}

/// A shared borrow returned by a function which also mutably borrows: the
/// region abstraction gives back the array.
pub fn shared_from_call(a: &mut [u32; 2], v: Val, k: u32) -> u32 {
    let s = match v {
        Val::Nat(_) => bump_and_get(a, &k),
        Val::Sort => return 0,
        Val::Neutral(..) => &a[1],
    };
    *s + 1
}

/// A shared borrow whose referent depends on the branch, live after the join.
pub fn conditional_referent(a: &mut [u32; 2], v: Val) -> u32 {
    let s = match v {
        Val::Nat(_) => &a[0],
        Val::Sort => return 0,
        Val::Neutral(..) => &a[1],
    };
    *s
}

/// A switch with continue, break and fall-through branches, in a loop which
/// mutates through a borrow live across the iterations.
pub fn loop_live_borrow(a: &mut [u32; 2], vs: &[Val]) -> u32 {
    let r = &mut a[0];
    let mut i = 0;
    while i < vs.len() {
        let v = vs[i];
        i += 1;
        match v {
            Val::Nat(n) => {
                *r += n;
                continue;
            }
            Val::Sort => break,
            Val::Neutral(..) => *r += 1,
        }
        *r += 10;
    }
    a[1] = i as u32;
    a[0]
}

#[verify::test]
pub fn test_let_else_chain() {
    let mut acc = 0;
    let v = Val::Neutral(Head::Const(5, Class::Ctor), 2);
    assert!(matches!(let_else_chain(v, Val::Nat(3), &mut acc), Ok(Some(17))));
    assert!(acc == 12);
    assert!(matches!(let_else_chain(Val::Sort, Val::Nat(3), &mut acc), Ok(None)));
    assert!(acc == 13);
    assert!(matches!(let_else_chain(v, Val::Nat(200), &mut acc), Err(200)));
    assert!(acc == 15);
    assert!(matches!(let_else_chain(v, Val::Sort, &mut acc), Ok(Some(0))));
    assert!(acc == 17);
}

#[verify::test]
pub fn test_all_return() {
    assert!(all_return(Val::Neutral(Head::Const(5, Class::Def), 0)) == 1);
    assert!(all_return(Val::Neutral(Head::Var(5), 0)) == 3);
    assert!(all_return(Val::Nat(0)) == 4);
    assert!(all_return(Val::Sort) == 6);
}

#[verify::test]
pub fn test_skip_to_outer() {
    let mut x = 0;
    assert!(skip_to_outer(Val::Nat(4), true, &mut x) == 9);
    assert!(x == 5);
    assert!(skip_to_outer(Val::Neutral(Head::Var(0), 0), true, &mut x) == 106);
    assert!(x == 106);
    assert!(skip_to_outer(Val::Sort, false, &mut x) == 108);
}

#[verify::test]
pub fn test_scopes_in_loop() {
    let a = [
        Val::Neutral(Head::Const(5, Class::Ctor), 0),
        Val::Sort,
        Val::Neutral(Head::Const(1, Class::Other), 0),
        Val::Neutral(Head::Const(1, Class::Def), 0),
        Val::Neutral(Head::Const(60, Class::Def), 0),
        Val::Neutral(Head::Const(5, Class::Ctor), 0),
    ];
    assert!(scopes_in_loop(&a) == 8);
}

#[verify::test]
pub fn test_real_loops() {
    assert!(real_loops(5) == 23);
}

#[verify::test]
pub fn test_panic_or_return() {
    assert!(panic_or_return(Val::Nat(10), 3) == 8);
    assert!(panic_or_return(Val::Sort, 3) == 3);
    assert!(panic_or_return(Val::Nat(2), 3) == 2);
}

#[verify::test]
pub fn test_loop_in_scope() {
    assert!(loop_in_scope(Val::Nat(3), 2) == 5);
    assert!(loop_in_scope(Val::Sort, 2) == 2);
    assert!(loop_in_scope(Val::Neutral(Head::Var(0), 0), 2) == 2);
}

#[verify::test]
pub fn test_live_borrow() {
    let mut a = [0, 0];
    assert!(live_borrow(&mut a, Val::Sort, Val::Sort) == 1);
    assert!(a[0] == 1 && a[1] == 0);
    assert!(live_borrow(&mut a, Val::Nat(2), Val::Sort) == 0);
    assert!(a[0] == 104 && a[1] == 0);
    assert!(live_borrow(&mut a, Val::Nat(2), Val::Nat(3)) == 110);
    assert!(a[0] == 110 && a[1] == 110);
}

#[verify::test]
pub fn test_live_borrow_rev() {
    let mut a = [0, 0];
    assert!(live_borrow_rev(&mut a, Val::Sort) == 3);
    assert!(live_borrow_rev(&mut a, Val::Nat(0)) == 8);
    assert!(a[0] == 7 && a[1] == 1);
    assert!(live_borrow_rev(&mut a, Val::Nat(5)) == 14);
}

#[verify::test]
pub fn test_shared_from_call() {
    let mut a = [1, 2];
    assert!(shared_from_call(&mut a, Val::Nat(0), 5) == 3);
    assert!(a[0] == 6);
    assert!(shared_from_call(&mut a, Val::Sort, 5) == 0);
    assert!(shared_from_call(&mut a, Val::Neutral(Head::Var(0), 0), 5) == 3);
    assert!(a[0] == 6);
}

#[verify::test]
pub fn test_conditional_referent() {
    let mut a = [1, 2];
    assert!(conditional_referent(&mut a, Val::Nat(0)) == 1);
    assert!(conditional_referent(&mut a, Val::Neutral(Head::Var(0), 0)) == 2);
}

#[verify::test]
pub fn test_loop_live_borrow() {
    let mut a = [0, 0];
    let vs = [
        Val::Nat(3),
        Val::Neutral(Head::Var(0), 0),
        Val::Nat(1),
        Val::Sort,
        Val::Nat(100),
    ];
    assert!(loop_live_borrow(&mut a, &vs) == 15);
    assert!(a[1] == 4);
}
