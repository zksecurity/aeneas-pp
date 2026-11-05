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
