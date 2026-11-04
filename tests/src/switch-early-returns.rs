//@ [!lean] skip
//! Joins after switches some branches of which return early (for instance
//! with `?`): the branches which continue are joined, and the code after the
//! switch is not duplicated.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum V {
    A(u32),
    B(u32),
    C(u32),
}

fn check(x: u32) -> Result<u32, u32> {
    if x > 100 { Err(x) } else { Ok(x + 1) }
}

/// Every match has two continuing branches which may return: the size of the
/// translation is linear in the number of matches.
pub fn chain(v0: V, v1: V, v2: V, v3: V, v4: V, v5: V) -> Result<u32, u32> {
    let mut r = 0u32;
    r = match v0 { V::A(x) => check(x)?, V::B(x) => check(x + r)?, V::C(_) => r };
    r = match v1 { V::A(x) => check(x)?, V::B(x) => check(x + r)?, V::C(_) => r };
    r = match v2 { V::A(x) => check(x)?, V::B(x) => check(x + r)?, V::C(_) => r };
    r = match v3 { V::A(x) => check(x)?, V::B(x) => check(x + r)?, V::C(_) => r };
    r = match v4 { V::A(x) => check(x)?, V::B(x) => check(x + r)?, V::C(_) => r };
    r = match v5 { V::A(x) => check(x)?, V::B(x) => check(x + r)?, V::C(_) => r };
    Ok(r)
}

/// An explicit return in one branch of an if.
pub fn early_return_if(x: u32, b: bool, c: bool) -> u32 {
    let y = if b {
        if c {
            return 0;
        }
        x + 1
    } else {
        x + 2
    };
    y * 2
}

/// Nested switches, returning from the inner one.
pub fn nested(v: V, w: V) -> Result<u32, u32> {
    let a = match v {
        V::A(x) => match w {
            V::A(y) => check(x + y)?,
            V::B(y) => check(y)?,
            V::C(_) => x,
        },
        V::B(x) => check(x)?,
        V::C(x) => x,
    };
    Ok(a + 1)
}

/// The mutable borrow is updated before the error: the update is visible to
/// the caller, and nothing after the switch happens.
pub fn update_then_error(v: V, acc: &mut u32) -> Result<u32, u32> {
    *acc += 1;
    let x = match v {
        V::A(x) => check(x)?,
        V::B(x) => check(x + 1)?,
        V::C(x) => x,
    };
    *acc += 10;
    Ok(x)
}

/// A panic in one branch, a return in another.
pub fn panic_or_return(v: V) -> u32 {
    let x = match v {
        V::A(x) => x,
        V::B(x) => {
            assert!(x < 50);
            x + 1
        }
        V::C(_) => return 7,
    };
    x + 1
}

pub struct Ck<'a> {
    pub t: &'a mut Vec<u32>,
    pub s: &'a mut Vec<u32>,
}

impl<'a> Ck<'a> {
    pub fn push(&mut self, x: u32) -> Result<u32, u32> {
        let y = check(x)?;
        self.t.push(y);
        self.s.push(x);
        Ok(y)
    }
}

/// A struct holding mutable borrows, updated by calls which may return early.
pub fn struct_calls(t: &mut Vec<u32>, s: &mut Vec<u32>, v: V) -> Result<u32, u32> {
    let mut ck = Ck { t, s };
    let x = match v {
        V::A(x) => ck.push(x)?,
        V::B(x) => {
            let y = ck.push(x)?;
            ck.push(y)?
        }
        V::C(x) => x,
    };
    ck.push(x)
}

/// The branches contain a loop consuming its own `break`: the switch is joined.
pub fn inner_loop(b: bool, n: u32) -> u32 {
    let x = if b {
        let mut i = 0;
        loop {
            if i >= n {
                break;
            }
            i += 1;
        }
        i
    } else {
        n + 1
    };
    x * 2
}

#[verify::test]
pub fn test_chain() {
    assert!(matches!(chain(V::A(1), V::B(1), V::C(0), V::A(2), V::C(0), V::B(0)), Ok(4)));
    assert!(matches!(chain(V::A(1), V::A(200), V::C(0), V::A(2), V::C(0), V::B(0)), Err(200)));
}

#[verify::test]
pub fn test_early_return_if() {
    assert!(early_return_if(3, true, true) == 0);
    assert!(early_return_if(3, true, false) == 8);
    assert!(early_return_if(3, false, false) == 10);
}

#[verify::test]
pub fn test_nested() {
    assert!(matches!(nested(V::A(1), V::A(2)), Ok(5)));
    assert!(matches!(nested(V::A(1), V::B(200)), Err(200)));
    assert!(matches!(nested(V::A(1), V::C(0)), Ok(2)));
    assert!(matches!(nested(V::C(5), V::C(0)), Ok(6)));
}

#[verify::test]
pub fn test_update_then_error() {
    let mut acc = 0;
    assert!(matches!(update_then_error(V::A(200), &mut acc), Err(200)));
    assert!(acc == 1);
    assert!(matches!(update_then_error(V::C(3), &mut acc), Ok(3)));
    assert!(acc == 12);
}

#[verify::test]
pub fn test_panic_or_return() {
    assert!(panic_or_return(V::A(1)) == 2);
    assert!(panic_or_return(V::B(1)) == 3);
    assert!(panic_or_return(V::C(1)) == 7);
}

#[verify::test]
pub fn test_struct_calls() {
    let (mut t, mut s) = (Vec::new(), Vec::new());
    assert!(matches!(struct_calls(&mut t, &mut s, V::B(1)), Ok(4)));
    assert!(t.len() == 3 && s.len() == 3);
    let (mut t, mut s) = (Vec::new(), Vec::new());
    assert!(matches!(struct_calls(&mut t, &mut s, V::B(200)), Err(200)));
    assert!(t.len() == 0 && s.len() == 0);
}

#[verify::test]
pub fn test_inner_loop() {
    assert!(inner_loop(true, 3) == 6);
    assert!(inner_loop(false, 3) == 8);
}
