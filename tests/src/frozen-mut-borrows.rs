//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! Mutable borrows seen through shared borrows: a struct holding a mutable
//! borrow, itself shared-borrowed, across joins and calls.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Env {
    pub decls: Vec<u32>,
}

pub struct Eng<'a> {
    pub t: &'a mut Vec<u32>,
    pub env: &'a Env,
}

/// A reference with the lifetime of the shared field, chosen by a branch.
pub fn get_if<'a>(e: &Eng<'a>, n: usize) -> &'a u32 {
    if n < e.env.decls.len() { &e.env.decls[n] } else { &e.env.decls[0] }
}

/// Reads through the mutable field in one branch only.
pub fn len_if(e: &Eng<'_>, b: bool) -> usize {
    if b { e.t.len() } else { 0 }
}

/// A reference into the mutably borrowed vector lives as long as the shared
/// borrow of the struct.
pub fn first<'a, 'b>(e: &'b Eng<'a>) -> &'b u32 {
    &e.t[0]
}

/// Reads through the frozen field, then mutates it once the read ended.
pub fn read_then_push(e: &mut Eng<'_>) -> usize {
    let x = *first(e);
    e.t.push(x + 1);
    e.t.len()
}

/// Several shared borrows of the struct, read in different branches.
pub fn two_views(e: &Eng<'_>, b: bool) -> u32 {
    let e2 = e;
    let a = if b { e.t[0] } else { e2.t[1] };
    a + e2.t.len() as u32
}

impl<'a> Eng<'a> {
    fn decl(&self, n: usize) -> Result<&'a u32, u32> {
        if n < self.env.decls.len() { Ok(&self.env.decls[n]) } else { Err(0) }
    }

    fn kc(&mut self, x: u32) -> Result<Option<u32>, u32> {
        self.t.push(x);
        if x > 5 { Ok(Some(x)) } else { Ok(None) }
    }

    /// A reference obtained through `&self`, live across calls through
    /// `&mut self` in a branch which may return early.
    pub fn iota(&mut self, n: usize, k: bool) -> Result<Option<u32>, u32> {
        let d = self.decl(n)?;
        let mut major = *d;
        if k {
            match self.kc(major)? {
                Some(c) => major = c,
                None => return Ok(None),
            }
        }
        Ok(Some(major + *d))
    }
}

#[verify::test]
pub fn test_reads() {
    let mut v = Vec::new();
    v.push(3);
    v.push(4);
    let mut decls = Vec::new();
    decls.push(7);
    let env = Env { decls };
    let e = Eng { t: &mut v, env: &env };
    assert!(*get_if(&e, 0) == 7);
    assert!(*get_if(&e, 5) == 7);
    assert!(len_if(&e, true) == 2);
    assert!(len_if(&e, false) == 0);
    assert!(*first(&e) == 3);
    assert!(two_views(&e, true) == 5);
    assert!(two_views(&e, false) == 6);
}

/// Runs [read_then_push] on a vector, giving back its new length and last
/// element.
pub fn run_read_then_push(v: &mut Vec<u32>) -> (usize, u32) {
    let env = Env { decls: Vec::new() };
    let mut e = Eng { t: v, env: &env };
    let n = read_then_push(&mut e);
    (n, e.t[n - 1])
}

#[verify::test]
pub fn test_read_then_push() {
    let mut v = Vec::new();
    v.push(3);
    let (n, x) = run_read_then_push(&mut v);
    assert!(n == 2 && x == 4);
}

#[verify::test]
pub fn test_iota() {
    let mut v = Vec::new();
    let mut decls = Vec::new();
    decls.push(7);
    decls.push(2);
    let env = Env { decls };
    let mut e = Eng { t: &mut v, env: &env };
    assert!(matches!(e.iota(0, true), Ok(Some(14))));
    assert!(matches!(e.iota(1, true), Ok(None)));
    assert!(matches!(e.iota(1, false), Ok(Some(4))));
    assert!(matches!(e.iota(3, false), Err(0)));
    assert!(v.len() == 2 && v[0] == 7 && v[1] == 2);
}
