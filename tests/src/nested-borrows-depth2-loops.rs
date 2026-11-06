//@ [!lean] skip
//@ aeneas-args=-strict-joins
//@ charon-args=--no-code-duplication
//! Loops calling methods on `&mut self` where `self` holds mutable borrows:
//! the call abstractions hold the borrows nested two levels deep.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Engine<'a> {
    pub t: &'a mut u32,
    pub s: &'a mut u32,
}

impl<'a> Engine<'a> {
    pub fn eval(&mut self, e: u32) -> Result<u32, ()> {
        *self.t += e;
        if e > 100 {
            return Err(());
        }
        Ok(*self.t)
    }

    /// Calls [eval] until it returns a non-zero value
    pub fn eval_nonzero(&mut self, mut e: u32) -> Result<u32, ()> {
        loop {
            let v = self.eval(e)?;
            if v == 0 {
                e = 1;
            } else {
                return Ok(v);
            }
        }
    }

    /// Writes through both inner references at every iteration
    pub fn run(&mut self, mut n: u32) -> Result<u32, ()> {
        loop {
            let v = self.eval(n)?;
            *self.s += v;
            if n == 0 {
                return Ok(v);
            }
            n -= 1;
        }
    }
}

/// Exchanges the inner references of the engine at every iteration
pub fn run_swap(a: &mut u32, b: &mut u32, mut n: u32) -> Result<u32, ()> {
    let mut e = Engine { t: a, s: b };
    loop {
        let v = e.eval(n)?;
        e = Engine { t: e.s, s: e.t };
        *e.t += 10;
        if n == 0 {
            return Ok(v);
        }
        n -= 1;
    }
}

pub fn run_engine() -> (u32, u32, u32) {
    let mut a = 1;
    let mut b = 100;
    let mut e = Engine { t: &mut a, s: &mut b };
    let r = match e.run(3) {
        Ok(v) => v,
        Err(_) => 0,
    };
    (r, a, b)
}

pub fn nonzero_engine() -> (u32, u32) {
    let mut a = 0;
    let mut b = 100;
    let mut e = Engine { t: &mut a, s: &mut b };
    let r = match e.eval_nonzero(0) {
        Ok(v) => v,
        Err(_) => 0,
    };
    (r, a)
}

pub fn swap_engine() -> (u32, u32, u32) {
    let mut a = 1;
    let mut b = 100;
    let r = match run_swap(&mut a, &mut b, 3) {
        Ok(v) => v,
        Err(_) => 0,
    };
    (r, a, b)
}

#[verify::test]
pub fn test_run_engine() {
    assert!(matches!(run_engine(), (7, 7, 124)));
}

#[verify::test]
pub fn test_nonzero_engine() {
    assert!(matches!(nonzero_engine(), (1, 1)));
}

#[verify::test]
pub fn test_swap_engine() {
    assert!(matches!(swap_engine(), (122, 25, 122)));
}
