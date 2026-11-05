//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins of branches which share the region abstractions of the calls preceding
//! the branching inside the same scope.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Node {
    Const(u32),
    Other,
}

fn allowed(index: u32, params: &[u32]) -> bool {
    params.len() as u32 == index
}

/// [params] is a promoted constant converted to a slice by a call, used in one
/// branch only.
pub fn parameters(node: &Node) -> bool {
    let params: &[u32] = &[];
    match node {
        Node::Const(i) => allowed(*i, params),
        _ => false,
    }
}

#[verify::test]
pub fn test_parameters() {
    assert!(parameters(&Node::Const(0)));
    assert!(!parameters(&Node::Const(1)));
    assert!(!parameters(&Node::Other));
}
