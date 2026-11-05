//@ [!lean] skip
//! Names which collide with Lean's name resolution.
#![feature(register_tool)]
#![register_tool(verify)]

pub mod env {
    pub enum Kind {
        Axiom,
        Definition(u32),
    }

    pub struct Environment {
        pub kind: Kind,
    }
}

/// The variable `env` must not shadow the namespace `env` of `env::Kind`.
pub fn is_axiom(env: &env::Environment) -> bool {
    match env.kind {
        env::Kind::Axiom => true,
        env::Kind::Definition(_) => false,
    }
}

pub enum List {
    Nil,
    Cons(u32, Box<List>),
}

impl List {
    /// Lean generates `List.below` and `List.rec` for the inductive `List`.
    pub fn below(&self, n: u32) -> bool {
        match self {
            List::Nil => true,
            List::Cons(x, tl) => *x < n && tl.below(n),
        }
    }

    pub fn rec(&self) -> u32 {
        match self {
            List::Nil => 0,
            List::Cons(_, tl) => 1 + tl.rec(),
        }
    }
}

#[verify::test]
pub fn test_collisions() {
    assert!(is_axiom(&env::Environment { kind: env::Kind::Axiom }));
    assert!(!is_axiom(&env::Environment { kind: env::Kind::Definition(0) }));
    let l = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
    assert!(l.below(3) && !l.below(2) && l.rec() == 2);
}
