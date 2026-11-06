//@ [!lean] skip
//@ charon-args=--monomorphize-mut=except-types
//! A helper whose closure takes a `&mut` argument, called with a closure which captures no `&mut`:
//! its bound stays about the generic `FnOnce` the closure implements.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Eng<'a> {
    pub t: &'a mut Vec<u32>,
    pub depth: u32,
}

impl<'a> Eng<'a> {
    fn guarded<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.depth += 1;
        let r = f(self);
        self.depth -= 1;
        r
    }

    fn push(&mut self, x: u32) -> u32 {
        self.t.push(x);
        self.depth
    }

    pub fn eval(&mut self, x: u32) -> u32 {
        self.guarded(|en| en.push(x))
    }
}

#[verify::test]
pub fn test_eval() {
    let mut v = Vec::new();
    let mut e = Eng { t: &mut v, depth: 0 };
    assert!(e.eval(3) == 1);
    assert!(e.depth == 0);
}
