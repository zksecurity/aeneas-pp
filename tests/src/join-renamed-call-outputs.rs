//@ [!lean] skip
//@ charon-args=--no-code-duplication --monomorphize-mut=except-types
//@ aeneas-args=-strict-joins
//! A switch joins a branch which calls a closure capturing two mutable borrows with branches which don't: the join ends the region of the first borrow in the calling branch, and renames the closure the call outputs.
#![feature(register_tool)]
#![register_tool(verify)]
pub enum Node {
    One(u32),
    Name(u32),
    Lit,
    Leaf,
}

pub struct Input {
    pub node: Node,
    pub seen: u32,
    pub names: u32,
}

impl Input {
    fn get(&self, n: u32) -> Result<(), ()> {
        if n < self.names { Ok(()) } else { Err(()) }
    }

    fn literal(&mut self) -> Result<(), ()> {
        self.names += 1;
        Ok(())
    }

    pub fn reach(&mut self) -> Result<u32, ()> {
        let mut todo = 0;
        let mut visit = |e: u32| {
            self.seen += e;
            todo += 1;
        };
        match self.node {
            Node::One(a) => visit(a),
            Node::Name(n) => self.get(n)?,
            Node::Lit => self.literal()?,
            _ => {}
        }
        Ok(todo)
    }
}

#[verify::test]
fn test_reach() {
    let mut x = Input { node: Node::One(3), seen: 4, names: 0 };
    assert!(matches!(x.reach(), Ok(1)));
    assert!(x.seen == 7);
    let mut y = Input { node: Node::Name(1), seen: 4, names: 2 };
    assert!(matches!(y.reach(), Ok(0)));
    assert!(y.seen == 4);
    let mut z = Input { node: Node::Name(2), seen: 4, names: 2 };
    assert!(matches!(z.reach(), Err(())));
    let mut w = Input { node: Node::Lit, seen: 0, names: 2 };
    assert!(matches!(w.reach(), Ok(0)));
    assert!(w.names == 3);
}
