//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins of branches where the region abstractions of the two indexing calls
//! hold instances of the same shared borrow of [nodes]: collapsing the join
//! merges those abstractions.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Node {
    Bound(u32),
    Free(u32),
    Sort(u32),
    Const(u32, u32),
    App(u32, u32),
    Lam(u32, u32),
    Pi(u32, u32),
    Let(u32, u32, u32),
    Proj(u32, u32, u32),
    Nat(u64),
    Str(u64),
}

fn node_eq(a: &Node, b: &Node) -> bool {
    match (a, b) {
        (Node::Bound(a), Node::Bound(b)) | (Node::Free(a), Node::Free(b)) | (Node::Sort(a), Node::Sort(b)) => a == b,
        _ => false,
    }
}

pub fn same(nodes: &Vec<Node>, a: u32, b: u32) -> bool {
    if a == b {
        return true;
    }
    let left = &nodes[a as usize];
    let right = &nodes[b as usize];
    match (left, right) {
        (Node::App(x, y), Node::App(u, v)) | (Node::Lam(x, y), Node::Lam(u, v)) | (Node::Pi(x, y), Node::Pi(u, v)) => {
            same(nodes, *x, *u) && same(nodes, *y, *v)
        }
        (Node::Let(x, y, z), Node::Let(u, v, w)) => {
            same(nodes, *x, *u) && same(nodes, *y, *v) && same(nodes, *z, *w)
        }
        (Node::Proj(n, i, x), Node::Proj(m, j, y)) => n == m && i == j && same(nodes, *x, *y),
        _ => node_eq(left, right),
    }
}
