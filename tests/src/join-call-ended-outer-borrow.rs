//@ [!lean] skip
//@ aeneas-args=-strict-joins
//@ charon-args=--no-code-duplication
//! The branches of the short-circuit `||` hold the call abstraction of `find`
//! in different forms, so the join turns it into a join abstraction, which the
//! branches give back from the continuation of the call: its output holds the
//! ended borrow of the iterator, which gives back nothing. `Iterator::find`
//! and `String::from` are opaque in the Lean library: the test only checks the
//! translation.
pub enum Kind {
    Rec { rules: Vec<u32>, k: bool },
    Other,
}

pub struct Decl {
    pub name: u32,
    pub ty: u32,
    pub kind: Kind,
}

pub fn verify(actual: &Decl, generated: &[Decl]) -> Result<u32, String> {
    let expected = generated
        .iter()
        .find(|d| d.name == actual.name)
        .ok_or("unexpected")?;
    let (Kind::Rec { rules: ar, k: ak }, Kind::Rec { rules: er, k: ek }) =
        (&actual.kind, &expected.kind)
    else {
        return Err("kind".into());
    };
    if ak != ek || ar.len() != er.len() {
        return Err("metadata".into());
    }
    if expected.ty == actual.ty {
        return Ok(expected.name);
    }
    Err("type".into())
}
