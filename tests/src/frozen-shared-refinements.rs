//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Reads through shared borrows of the inputs (in particular through mutable
//! borrows seen through shared borrows) refine the shared values of the input
//! abstractions: the branches and loop iterations expand the borrowed structs
//! and share parts of them, which joins forget once those parts are not
//! observed anymore.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Store {
    pub v: Vec<u32>,
    pub n: u32,
}

pub struct Eng<'a> {
    pub s: &'a mut Store,
    pub env: &'a Store,
}

impl<'a> Eng<'a> {
    /// Branches reading different fields through the frozen field.
    pub fn pick(&self, b: bool) -> u32 {
        let x = if b { self.s.v[0] } else { self.s.n };
        x + self.s.v[1]
    }

    /// A loop reading through the frozen field.
    pub fn sum(&self, mut i: usize) -> u32 {
        let mut acc = 0;
        while i != 0 {
            i -= 1;
            acc += self.s.v[i];
        }
        acc
    }

    /// A loop with an early return, reading through the frozen and the shared
    /// fields.
    pub fn find(&self, x: u32) -> Option<usize> {
        let mut i = 0;
        while i < self.s.v.len() {
            if self.s.v[i] == x || self.env.v[0] == x {
                return Some(i);
            }
            i += 1;
        }
        None
    }
}

/// Reads through the frozen field in a join, then writes through the mutable
/// field once the reads ended.
pub fn read_join_then_write(e: &mut Eng<'_>, b: bool) -> u32 {
    let r: &Eng<'_> = e;
    let x = if b { r.s.v[0] } else { r.s.n };
    e.s.v[0] = x + 1;
    e.s.n = x;
    e.s.v[0] + e.s.n
}

/// Reads through a loop, then writes.
pub fn sum_then_write(e: &mut Eng<'_>, i: usize) -> u32 {
    let acc = e.sum(i);
    let r: &Eng<'_> = e;
    let n = if acc > 10 { r.s.n } else { r.env.n };
    e.s.n = acc + n;
    e.s.n
}

/// An owned engine read in a join, then written.
pub fn local_write(st: &mut Store, env: &Store, b: bool) -> u32 {
    let e = Eng { s: st, env };
    let x = if b { e.pick(true) } else { e.s.n };
    e.s.n = x + 2;
    e.s.n
}

/// Shared borrows of shared borrows.
pub fn pick2(x: &&Store, b: bool) -> u32 {
    let y = if b { x.v[0] } else { x.n };
    y + x.v[1]
}

fn store(a: u32, b: u32, n: u32) -> Store {
    let mut v = Vec::new();
    v.push(a);
    v.push(b);
    Store { v, n }
}

#[verify::test]
pub fn test_reads() {
    let mut st = store(3, 4, 9);
    let env = store(5, 6, 1);
    let e = Eng { s: &mut st, env: &env };
    assert!(e.pick(true) == 7);
    assert!(e.pick(false) == 13);
    assert!(e.sum(2) == 7);
    assert!(matches!(e.find(4), Some(1)));
    assert!(matches!(e.find(5), Some(0)));
    assert!(matches!(e.find(8), None));
    assert!(pick2(&&env, true) == 11);
    assert!(pick2(&&env, false) == 7);
}

#[verify::test]
pub fn test_writes() {
    let mut st = store(3, 4, 9);
    let env = store(5, 6, 1);
    let mut e = Eng { s: &mut st, env: &env };
    assert!(read_join_then_write(&mut e, true) == 7);
    assert!(read_join_then_write(&mut e, false) == 7);
    assert!(sum_then_write(&mut e, 2) == 9);
    assert!(local_write(&mut st, &env, true) == 10);
    assert!(st.v[0] == 4 && st.v[1] == 4 && st.n == 10);
    assert!(local_write(&mut st, &env, false) == 12);
    assert!(st.n == 12);
}
