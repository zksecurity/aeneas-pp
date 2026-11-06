//@ [!lean] skip
//@ charon-args=--opaque crate::Prim::to_u32 --opaque crate::Prim::pick
//! Implementations using opaque default methods: in the implementations, the
//! defaults become opaque methods of the implementations.

pub trait Prim {
    fn to_u64(&self) -> Option<u64>;

    fn to_u32(&self) -> Option<u32> {
        match self.to_u64() {
            Some(x) if x <= u32::MAX as u64 => Some(x as u32),
            _ => None,
        }
    }

    fn pick<U: Copy>(&self, a: U, b: U) -> U {
        if self.to_u64().is_some() { a } else { b }
    }
}

pub struct Big(u64);

impl Prim for Big {
    fn to_u64(&self) -> Option<u64> {
        Some(self.0)
    }
}

pub struct Wrap<T>(T);

impl<T: Copy + Into<u64>> Prim for Wrap<T> {
    fn to_u64(&self) -> Option<u64> {
        Some(self.0.into())
    }
}

pub fn small(b: &Big) -> bool {
    b.to_u32().is_some()
}

pub fn pick_wrap(w: &Wrap<u32>) -> u8 {
    w.pick(1, 2)
}

pub fn generic<T: Prim>(x: &T) -> Option<u32> {
    x.to_u32()
}
