//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! Calls to functions taking shared borrows of values which contain borrows
//! (`&'b T<'a>`) and returning borrows with the inner lifetime, followed by
//! joins while the results are alive.
#![feature(register_tool)]
#![register_tool(verify)]

pub fn decl<'a>(e: &&'a u32) -> Option<&'a u32> {
    Some(*e)
}

pub fn known(e: &&u32, b: bool) -> u32 {
    let x = if b { 0 } else { *decl(e).unwrap() };
    x + 1
}

pub struct Engine<'a> {
    pub nodes: &'a [u32],
    pub log: &'a mut Vec<u32>,
}

impl<'a> Engine<'a> {
    fn node(&self, e: usize) -> Option<&'a u32> {
        self.nodes.get(e)
    }

    /// The node is read in one branch only, then the engine is mutated.
    pub fn peel(&mut self, e: usize, b: bool) -> u32 {
        let x = if b { 0 } else { *self.node(e).unwrap() };
        self.log.push(x);
        x + 1
    }

    /// The branch which doesn't read the node mutates the engine.
    pub fn peel_mut(&mut self, e: usize, b: bool) -> u32 {
        let x = if b {
            self.log.push(1);
            0
        } else {
            *self.node(e).unwrap()
        };
        self.log.push(x);
        x
    }

    /// Different nodes in the two branches, alive after the join.
    pub fn pick(&mut self, e: usize, b: bool) -> u32 {
        let r = if b { self.node(e) } else { self.node(e + 1) };
        let x = match r {
            Some(x) => *x,
            None => 0,
        };
        self.log.push(x);
        x
    }

    /// Calls in a loop.
    pub fn sum(&mut self, n: usize) -> u32 {
        let mut s = 0;
        let mut i = 0;
        while i < n {
            if let Some(x) = self.node(i) {
                s += *x;
            }
            i += 1;
        }
        self.log.push(s);
        s
    }
}

#[verify::test]
pub fn test_known() {
    let x = 5;
    let r = &x;
    assert!(known(&r, true) == 1);
    assert!(known(&r, false) == 6);
}

#[verify::test]
pub fn test_engine() {
    let nodes = [3, 4, 5];
    let mut log = Vec::new();
    let mut e = Engine { nodes: &nodes, log: &mut log };
    assert!(e.peel(1, false) == 5);
    assert!(e.peel(1, true) == 1);
    assert!(e.pick(0, true) == 3);
    assert!(e.pick(0, false) == 4);
    assert!(e.pick(2, false) == 0);
    assert!(e.sum(3) == 12);
    assert!(e.peel_mut(2, false) == 5);
    assert!(e.peel_mut(2, true) == 0);
    assert!(log.len() == 9 && log[0] == 4 && log[5] == 12 && log[6] == 5 && log[7] == 1);
}
