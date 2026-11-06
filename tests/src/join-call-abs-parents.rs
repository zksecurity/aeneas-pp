//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! A branch which keeps the abstractions of a call alive orders the ending of
//! its arguments' abstractions after its result's, while a branch which ended
//! the call doesn't: the join keeps the ordering.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Hints {
    Opaque,
    Regular(u32),
}

pub enum Kind {
    Axiom,
    Definition(Hints),
}

pub struct Decl {
    pub kind: Kind,
}

pub fn rank(d: Option<&Decl>) -> u32 {
    match d.map(|d| &d.kind) {
        Some(Kind::Definition(hints)) => match hints {
            Hints::Opaque => 0,
            Hints::Regular(h) => *h,
        },
        _ => 1,
    }
}

#[verify::test]
pub fn test_rank() {
    assert!(rank(None) == 1);
    assert!(rank(Some(&Decl { kind: Kind::Axiom })) == 1);
    assert!(rank(Some(&Decl { kind: Kind::Definition(Hints::Opaque) })) == 0);
    assert!(rank(Some(&Decl { kind: Kind::Definition(Hints::Regular(3)) })) == 3);
}
