//@ [!lean] skip
//@ charon-args=--no-code-duplication --monomorphize-mut=except-types
//@ aeneas-args=-strict-joins
//! The joins and the loops output a structure whose fields all change as a
//! single value, and only the values which the code after them reads.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Eng<'a> {
    pub log: &'a mut Vec<u32>,
    nodes: &'a [u32],
    depth: u32,
    steps: u32,
}

pub struct View<'v> {
    nodes: &'v [u32],
}

impl<'v> View<'v> {
    fn node(&self, i: u32) -> Option<u32> {
        if (i as usize) < self.nodes.len() {
            Some(self.nodes[i as usize])
        } else {
            None
        }
    }
}

impl<'a> Eng<'a> {
    fn view(&self) -> View<'_> {
        View { nodes: self.nodes }
    }

    fn node(&self, i: u32) -> Option<u32> {
        if (i as usize) < self.nodes.len() {
            Some(self.nodes[i as usize])
        } else {
            None
        }
    }

    fn record(&mut self, x: u32) {
        self.log.push(x);
        self.steps += 1;
    }

    pub fn guarded(&mut self, x: u32) -> Result<u32, u32> {
        self.depth += 1;
        if self.depth > 2 {
            self.depth -= 1;
            return Err(x);
        }
        self.record(x);
        self.depth -= 1;
        Ok(x)
    }

    pub fn odd_node(&mut self, i: u32) -> bool {
        let Some(n) = self.view().node(i) else {
            return false;
        };
        self.steps += n;
        n % 2 == 1
    }

    pub fn walk(&mut self, mut i: u32) -> Result<u32, u32> {
        loop {
            let Some(n) = self.node(i) else {
                return Err(i);
            };
            self.record(n);
            if n == 0 {
                return Ok(self.steps);
            }
            i = n;
        }
    }
}

#[verify::test]
pub fn test_guarded() {
    let mut log = Vec::new();
    let nodes = [1, 2, 0];
    let mut e = Eng { log: &mut log, nodes: &nodes, depth: 0, steps: 0 };
    assert!(matches!(e.guarded(5), Ok(5)));
    e.depth = 2;
    assert!(matches!(e.guarded(6), Err(6)));
    assert!(e.depth == 2);
    assert!(e.steps == 1);
    assert!(e.odd_node(0));
    assert!(!e.odd_node(1));
    assert!(!e.odd_node(5));
    assert!(e.steps == 4);
}

#[verify::test]
pub fn test_walk() {
    let mut log = Vec::new();
    let nodes = [1, 2, 0];
    let mut e = Eng { log: &mut log, nodes: &nodes, depth: 0, steps: 0 };
    assert!(matches!(e.walk(0), Ok(3)));
    assert!(matches!(e.walk(7), Err(7)));
}
