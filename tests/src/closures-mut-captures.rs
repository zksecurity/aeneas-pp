//@ [!lean] skip
//@ charon-args=--no-code-duplication --monomorphize-mut=except-types
//! Closures capturing mutable borrows. Charon specializes the functions they are passed to.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Eng<'a> {
    pub t: &'a mut Vec<u32>,
    pub d: u32,
}

impl<'a> Eng<'a> {
    /// Calls the callback in a loop, stopping at the first error.
    fn telescope(
        &mut self,
        n: u32,
        mut next: impl FnMut(&mut Self, u32) -> Result<bool, ()>,
    ) -> Result<u32, ()> {
        let mut i = 0;
        let mut c = 0;
        while i < n {
            if next(self, i)? {
                c += 1;
            }
            i += 1;
        }
        Ok(c)
    }

    /// The closure records whether it saw [2].
    pub fn count(&mut self, n: u32) -> Result<(u32, bool), ()> {
        let mut seen = false;
        let c = self.telescope(n, |e, i| {
            e.t.push(i);
            if i == 2 {
                seen = true;
            }
            Ok(i % 2 == 0)
        })?;
        Ok((c, seen))
    }

    /// The closure captures [self] by shared borrow, and another closure.
    pub fn consecutive(&mut self, v: &[u32]) -> bool {
        let shift = |e: &Self, x: u32| e.d + x;
        both_pairs(v, |a, b| shift(self, b) == shift(self, a) + 1)
    }
}

fn call_mut_twice(v: &mut Vec<u32>, mut f: impl FnMut(&mut Vec<u32>) -> u32) -> u32 {
    let a = f(v);
    let b = f(v);
    a + b
}

/// A closure updating a counter it borrows.
pub fn push_counter(v: &mut Vec<u32>, k: &mut u32) -> u32 {
    call_mut_twice(v, |w| {
        *k += 1;
        w.push(*k);
        *k
    })
}

fn both_pairs(v: &[u32], mut f: impl FnMut(u32, u32) -> bool) -> bool {
    f(v[0], v[1]) && f(v[1], v[2])
}

pub trait Visit {
    fn size(&self) -> u32;

    /// A default method, which Charon specializes for the closures capturing mutable borrows.
    fn each(&self, mut f: impl FnMut(u32)) {
        let mut i = 0;
        while i < self.size() {
            f(i);
            i += 1;
        }
    }
}

pub struct Upto(pub u32);

impl Visit for Upto {
    fn size(&self) -> u32 {
        self.0
    }
}

pub fn sum_upto(n: u32, acc: &mut u32) {
    let u = Upto(n);
    u.each(|_| ());
    u.each(|i| *acc += i);
}

#[verify::test]
pub fn test_count() {
    let mut t = Vec::new();
    let mut e = Eng { t: &mut t, d: 0 };
    assert!(matches!(e.count(2), Ok((1, false))));
    assert!(matches!(e.count(4), Ok((2, true))));
    assert!(t.len() == 6);
}

#[verify::test]
pub fn test_push_counter() {
    let mut v = Vec::new();
    let mut k = 10;
    assert!(push_counter(&mut v, &mut k) == 23);
    assert!(k == 12 && v[0] == 11 && v[1] == 12);
}

#[verify::test]
pub fn test_consecutive() {
    let mut t = Vec::new();
    let mut e = Eng { t: &mut t, d: 3 };
    assert!(e.consecutive(&[1, 2, 3]));
    assert!(!e.consecutive(&[1, 3, 4]));
}

#[verify::test]
pub fn test_sum_upto() {
    let mut acc = 1;
    sum_upto(4, &mut acc);
    assert!(acc == 7);
}
