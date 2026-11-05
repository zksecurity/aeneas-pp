//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! [FnMut] and [Fn] closures whose arguments are mutable borrows.
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
        mut next: impl FnMut(&mut Self, u32) -> Result<bool, u32>,
    ) -> Result<u32, u32> {
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

    pub fn count_even(&mut self, n: u32, limit: u32) -> Result<u32, u32> {
        self.telescope(n, |e, i| {
            if i > limit {
                return Err(i);
            }
            e.t.push(i);
            e.d += 1;
            if i % 2 == 0 { Ok(true) } else { Ok(false) }
        })
    }
}

fn apply_twice(v: &mut Vec<u32>, f: impl Fn(&mut Vec<u32>, u32), g: impl FnOnce(&mut Vec<u32>) -> usize) -> usize {
    f(v, 1);
    f(v, 2);
    g(v)
}

/// A closure called twice through [Fn].
pub fn push_twice(v: &mut Vec<u32>, k: u32) -> usize {
    apply_twice(v, |w, x| w.push(x + k), |w| w.len())
}

fn call_mut_twice(v: &mut Vec<u32>, mut f: impl FnMut(&mut Vec<u32>) -> u32) -> u32 {
    let a = f(v);
    let b = f(v);
    a + b
}

/// A closure owning a counter which it updates at each call.
pub fn push_counter(v: &mut Vec<u32>) -> u32 {
    let mut k = 10;
    call_mut_twice(v, move |w| {
        k += 1;
        w.push(k);
        k
    })
}

#[verify::test]
pub fn test_count_even() {
    let mut t = Vec::new();
    let mut e = Eng { t: &mut t, d: 0 };
    assert!(matches!(e.count_even(5, 10), Ok(3)));
    assert!(e.d == 5);
    assert!(matches!(e.count_even(5, 2), Err(3)));
    assert!(e.d == 8);
    assert!(t.len() == 8);
}

#[verify::test]
pub fn test_push_twice() {
    let mut v = Vec::new();
    assert!(push_twice(&mut v, 5) == 2);
    assert!(v[0] == 6 && v[1] == 7);
}

#[verify::test]
pub fn test_push_counter() {
    let mut v = Vec::new();
    assert!(push_counter(&mut v) == 23);
    assert!(v[0] == 11 && v[1] == 12);
}
