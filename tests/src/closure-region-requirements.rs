//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Closures whose bodies require relations between the regions they receive from their creator.
#![feature(register_tool)]
#![register_tool(verify)]
pub enum Kind {
    Definition(u32),
    Axiom,
}

pub struct Decl {
    pub kind: Kind,
}

pub fn class(decls: &[Decl], n: usize) -> u32 {
    match decls.get(n).map(|d| &d.kind) {
        Some(Kind::Definition(x)) => *x,
        _ => 0,
    }
}

pub fn first(x: &u32) -> Option<&u32> {
    Some(x).map(|r| r)
}

#[verify::test]
fn test_class() {
    let decls = [Decl { kind: Kind::Axiom }, Decl { kind: Kind::Definition(7) }];
    assert!(class(&decls, 1) == 7);
    assert!(class(&decls, 0) == 0);
    assert!(class(&decls, 2) == 0);
    assert!(matches!(first(&3), Some(&3)));
}
