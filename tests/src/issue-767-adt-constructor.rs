//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

struct Struct(u32);

enum Enum {
    Unit,
    Tuple(u32),
}

impl Enum {
    /// Mentions the unit type in the namespace of [Enum], which has a variant [Unit]
    fn check(&self) {}
}

fn make_tuple_struct_with_constructor<T>(x: Option<u32>) -> Option<Struct> {
    x.map(Struct)
}

fn make_enum_with_constructor(x: Option<u32>) -> Option<Enum> {
    x.map(Enum::Tuple)
}

#[verify::test]
fn test_tuple_struct_constructor() {
    let _ = Struct(42);
}

#[verify::test]
fn test_enum_constructor() {
    let _ = Enum::Tuple(42);
}
