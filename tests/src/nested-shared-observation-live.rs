//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! A borrow returned by a call which observes a frozen mutable borrow in one
//! branch only, needed after the join.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Engine<'a> {
    pub nodes: &'a [u32],
    pub log: &'a mut Vec<u32>,
}

impl<'a> Engine<'a> {
    fn node(&self, e: usize) -> Option<&'a u32> {
        self.nodes.get(e)
    }

    pub fn maybe_node(&mut self, e: usize, b: bool) -> u32 {
        let r = if b { self.node(e) } else { None };
        let x = match r {
            Some(x) => *x,
            None => 0,
        };
        self.log.push(x);
        x
    }
}

#[verify::test]
pub fn test_maybe_node() {
    let nodes = [3, 4];
    let mut log = Vec::new();
    let mut e = Engine { nodes: &nodes, log: &mut log };
    assert!(e.maybe_node(1, true) == 4);
    assert!(e.maybe_node(1, false) == 0);
    assert!(log.len() == 2 && log[0] == 4);
}
