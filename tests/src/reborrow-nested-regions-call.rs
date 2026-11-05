//@ [!lean] skip
//! A method on a struct of mutable borrows which reborrows them into a value
//! built by a function call: the backward function of the outer region does
//! not need the values given back to the inner one.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Engine<'a> {
    pub xs: &'a mut Vec<u32>,
    pub n: &'a mut u32,
    pub k: &'a u32,
}

impl<'a> Engine<'a> {
    pub fn new(xs: &'a mut Vec<u32>, n: &'a mut u32, k: &'a u32) -> Self {
        Engine { xs, n, k }
    }

    pub fn push(&mut self) {
        self.xs.push(*self.k);
        *self.n += 1;
    }
}

pub struct Checker<'a> {
    pub xs: &'a mut Vec<u32>,
    pub n: &'a mut u32,
    pub k: u32,
}

impl<'a> Checker<'a> {
    pub fn engine(&mut self) -> Engine<'_> {
        Engine::new(self.xs, &mut *self.n, &self.k)
    }
}

#[verify::test]
pub fn test_engine() {
    let mut xs = Vec::new();
    let mut n = 0;
    let mut c = Checker { xs: &mut xs, n: &mut n, k: 7 };
    c.engine().push();
    c.k = 9;
    c.engine().push();
    assert!(*c.n == 2);
    assert!(xs.len() == 2 && xs[0] == 7 && xs[1] == 9);
    assert!(n == 2);
}
