//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! Closures whose arguments are mutable borrows, called through generic
//! helpers: the calls give back the borrowed values.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Eng<'a> {
    pub t: &'a mut Vec<u32>,
    pub d: u32,
}

impl<'a> Eng<'a> {
    fn guarded<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, u32>) -> Result<T, u32> {
        self.d += 1;
        if self.d > 3 {
            self.d -= 1;
            return Err(self.d);
        }
        let r = f(self);
        self.d -= 1;
        r
    }

    fn under<T>(&mut self, x: u32, f: impl FnOnce(&mut Self, u32) -> Result<T, u32>) -> Result<T, u32> {
        self.d += 1;
        let r = f(self, x + self.d);
        self.d -= 1;
        r
    }

    /// Forwards the closure to another generic helper.
    fn guarded_under<T>(&mut self, x: u32, f: impl FnOnce(&mut Self, u32) -> Result<T, u32>) -> Result<T, u32> {
        self.guarded(|e| e.under(x, f))
    }

    fn with<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        f(self)
    }

    /// Two calls, the second one using the result of the first, with `?`.
    pub fn work(&mut self, x: u32) -> Result<u32, u32> {
        let y = self.guarded(|e| {
            e.t.push(x);
            Ok(e.d)
        })?;
        self.under(y, |e, v| {
            e.t.push(v);
            Ok(v + e.d)
        })
    }

    /// A closure with a unit output.
    pub fn push(&mut self, x: u32) {
        self.with(|e| e.t.push(x))
    }

    /// A closure capturing a shared borrow, through two helpers.
    pub fn push_all(&mut self, xs: &[u32]) -> Result<usize, u32> {
        self.guarded_under(1, |e, v| {
            let mut i = 0;
            while i < xs.len() {
                e.t.push(xs[i] + v);
                i += 1;
            }
            Ok(e.t.len())
        })
    }

    /// Nested calls, until the depth limit fails.
    pub fn nest(&mut self) -> Result<u32, u32> {
        self.guarded(|e| e.guarded(|e| e.guarded(|e| e.guarded(|e| Ok(e.d)))))
    }
}

#[verify::test]
pub fn test_work() {
    let mut t = Vec::new();
    let mut e = Eng { t: &mut t, d: 0 };
    assert!(matches!(e.work(5), Ok(3)));
    assert!(e.d == 0);
    e.push(9);
    assert!(t.len() == 3 && t[0] == 5 && t[1] == 2 && t[2] == 9);
}

#[verify::test]
pub fn test_push_all() {
    let mut t = Vec::new();
    let mut e = Eng { t: &mut t, d: 0 };
    assert!(matches!(e.push_all(&[1, 2]), Ok(2)));
    assert!(t[0] == 4 && t[1] == 5);
}

#[verify::test]
pub fn test_nest() {
    let mut t = Vec::new();
    let mut e = Eng { t: &mut t, d: 0 };
    assert!(matches!(e.nest(), Err(3)));
    assert!(e.d == 0);
    e.d = 0;
    let mut e2 = Eng { t: &mut t, d: 0 };
    assert!(matches!(e2.guarded(|e| e.guarded(|e| Ok(e.d))), Ok(2)));
}
