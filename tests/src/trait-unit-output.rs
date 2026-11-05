//@ [!lean] skip
//! Trait methods whose output is generic, implemented with a unit output: the
//! calls through the trait and the direct calls to the implementation agree.
#![feature(register_tool)]
#![register_tool(verify)]

pub trait Step {
    type Out;
    fn step(&mut self, x: &mut u32) -> Self::Out;
}

pub struct Inc {
    pub n: u32,
}

impl Step for Inc {
    type Out = ();
    fn step(&mut self, x: &mut u32) {
        self.n += 1;
        *x += self.n;
    }
}

pub struct Acc {
    pub total: u32,
}

impl Step for Acc {
    type Out = u32;
    fn step(&mut self, x: &mut u32) -> u32 {
        self.total += *x;
        *x = 0;
        self.total
    }
}

fn run<S: Step>(s: &mut S, x: &mut u32) -> S::Out {
    s.step(x)
}

/// Direct calls and calls through the trait.
pub fn inc_twice(x: &mut u32) -> u32 {
    let mut i = Inc { n: 0 };
    i.step(x);
    run(&mut i, x);
    i.n
}

pub fn acc_twice(x: &mut u32, y: &mut u32) -> u32 {
    let mut a = Acc { total: 0 };
    a.step(x);
    run(&mut a, y)
}

#[verify::test]
pub fn test_inc_twice() {
    let mut x = 10;
    assert!(inc_twice(&mut x) == 2);
    assert!(x == 13);
}

#[verify::test]
pub fn test_acc_twice() {
    let mut x = 3;
    let mut y = 4;
    assert!(acc_twice(&mut x, &mut y) == 7);
    assert!(x == 0 && y == 0);
}
