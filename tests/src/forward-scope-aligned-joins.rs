//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins of the branches of a forward scope which expand differently a value
//! shared by an abstraction introduced in the scope, before the branching.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Known {
    pub zero: u32,
}

pub struct Engine<'a> {
    pub nats: &'a mut Vec<u32>,
    pub known: Known,
}

pub enum Val {
    Const(u32, u32),
    Nat(u32),
}

impl<'a> Engine<'a> {
    fn val(&self, v: u32) -> Val {
        if v < 2 {
            Val::Nat(v)
        } else {
            Val::Const(v, 0)
        }
    }

    /// Only the second branch expands [self.known]
    pub fn is_zero(&self, v: u32) -> bool {
        match self.val(v) {
            Val::Nat(i) => self.nats[i as usize] == 0,
            Val::Const(c, 0) => c == self.known.zero,
            _ => false,
        }
    }
}

#[verify::test]
pub fn test_is_zero() {
    let mut nats = vec![0, 1];
    let e = Engine { nats: &mut nats, known: Known { zero: 2 } };
    assert!(e.is_zero(0));
    assert!(!e.is_zero(1));
    assert!(e.is_zero(2));
    assert!(!e.is_zero(3));
}
