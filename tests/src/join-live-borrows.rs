//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins of paths on which borrows are live in one branch only.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Value {
    Num(u64),
    Obj(Vec<(u32, Value)>),
}

/// The loop returns a borrow of an element early: the borrows of the iterator
/// are live on this path, while the other paths ended them.
pub fn field(v: &Value, k: u32) -> Result<&Value, u32> {
    match v {
        Value::Obj(fields) => {
            for (key, val) in fields {
                if *key == k {
                    return Ok(val);
                }
            }
            Err(0)
        }
        _ => Err(1),
    }
}

/// The same, with an index: the borrow returned by the indexing is live on this
/// path only.
pub fn field_at(v: &Value, k: u32) -> Result<&Value, u32> {
    match v {
        Value::Obj(fields) => {
            let mut i = 0;
            while i < fields.len() {
                let (key, val) = &fields[i];
                if *key == k {
                    return Ok(val);
                }
                i += 1;
            }
            Err(0)
        }
        _ => Err(1),
    }
}

pub fn number(v: &Value) -> Result<u64, u32> {
    match v {
        Value::Num(n) => Ok(*n),
        _ => Err(2),
    }
}

pub fn field_number(v: &Value, k: u32) -> Result<u64, u32> {
    number(field(v, k)?)
}

pub fn field_at_number(v: &Value, k: u32) -> Result<u64, u32> {
    number(field_at(v, k)?)
}

#[verify::test]
pub fn test_field_at_number() {
    let mut fields = Vec::new();
    fields.push((1, Value::Num(10)));
    fields.push((2, Value::Num(20)));
    let v = Value::Obj(fields);
    assert!(matches!(field_at_number(&v, 2), Ok(20)));
    assert!(matches!(field_at_number(&v, 3), Err(0)));
    assert!(matches!(field_at_number(&Value::Num(5), 1), Err(1)));
}

// The input is projected at the region of the call in one branch only: the join
// renames that region, not the input.
pub fn exit_code(v: &Value) -> u32 {
    match v {
        Value::Num(_) => 1,
        _ => 2,
    }
}

pub fn status(v: Option<&Value>) -> u32 {
    match v {
        None => 0,
        Some(v) => exit_code(v),
    }
}

#[verify::test]
pub fn test_status() {
    assert!(status(None) == 0);
    assert!(status(Some(&Value::Num(3))) == 1);
}

// One branch reads a field of a value shared by the input abstraction, which
// the other branch never expands.
pub struct Store {
    pub nats: Vec<u64>,
}

pub enum Slot {
    Nat(usize),
    Other,
}

pub struct Engine<'a> {
    pub s: &'a mut Store,
    pub slots: Vec<Slot>,
}

impl<'a> Engine<'a> {
    fn slot(&self, v: usize) -> &Slot {
        &self.slots[v]
    }

    pub fn nat_value(&self, v: usize) -> Option<&u64> {
        match self.slot(v) {
            Slot::Nat(i) => Some(&self.s.nats[*i]),
            _ => None,
        }
    }
}

impl<'a> Engine<'a> {
    // The closure's input abstractions hold meta-values which differ between
    // the branches of its match.
    pub fn both_nat(&mut self, x: usize, y: usize) -> bool {
        let is_nat = |en: &Self, v: usize| matches!(en.slot(v), Slot::Nat(_));
        is_nat(self, x) && is_nat(self, y)
    }
}

pub fn nat_or_zero(n: Option<&u64>) -> u64 {
    match n {
        Some(n) => *n,
        None => 0,
    }
}

#[verify::test]
pub fn test_nat_value() {
    let mut store = Store { nats: Vec::new() };
    store.nats.push(7);
    let mut slots = Vec::new();
    slots.push(Slot::Nat(0));
    slots.push(Slot::Other);
    let mut e = Engine { s: &mut store, slots };
    let a = nat_or_zero(e.nat_value(0));
    let b = nat_or_zero(e.nat_value(1));
    assert!(a == 7 && b == 0);
    assert!(e.both_nat(0, 0) && !e.both_nat(0, 1));
}
