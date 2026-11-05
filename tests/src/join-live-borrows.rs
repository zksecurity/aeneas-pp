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
