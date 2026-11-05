//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins inside the arguments of a call taking a two-phase borrow: the
//! reserved borrow is live in both branches.
#![feature(register_tool)]
#![register_tool(verify)]

pub fn push_flag(v: &mut Vec<u32>, b: Option<u32>) {
    v.push(if matches!(b, Some(_)) { 1 } else { 0 });
}

#[derive(Clone, Copy)]
pub enum Node {
    Lam(u32, u32),
    Pi(u32, u32),
}

pub struct Terms {
    pub nodes: Vec<Node>,
}

impl Terms {
    pub fn node(&mut self, n: Node) -> u32 {
        self.nodes.push(n);
        self.nodes.len() as u32
    }
}

pub struct Binder<'a> {
    pub t: &'a mut Terms,
    pub types: Vec<u32>,
}

impl<'a> Binder<'a> {
    /// The reserved borrow of `self.t` is live in the branches of each
    /// iteration.
    pub fn bind(&mut self, lambda: bool, mut body: u32) -> u32 {
        let mut i = 0;
        while i < self.types.len() {
            let ty = self.types[i];
            body = self.t.node(if lambda {
                Node::Lam(ty, body)
            } else {
                Node::Pi(ty, body)
            });
            i += 1;
        }
        body
    }
}

#[verify::test]
pub fn test_push_flag() {
    let mut v = Vec::new();
    push_flag(&mut v, Some(3));
    push_flag(&mut v, None);
    assert!(v.len() == 2 && v[0] == 1 && v[1] == 0);
}

#[verify::test]
pub fn test_bind() {
    let mut t = Terms { nodes: Vec::new() };
    let mut b = Binder { t: &mut t, types: vec![7, 8] };
    assert!(b.bind(true, 0) == 2);
    assert!(matches!(t.nodes[1], Node::Lam(8, 1)));
}
