//@ [!lean] skip
//@ [lean] known-failure
//@ charon-args=--no-code-duplication
//! A closure whose output borrows from its arguments, which we don't support
//! yet: here a function item with an early-bound region.

fn ident<'a>(x: &'a mut u32) -> &'a mut u32
where
    'a: 'a,
{
    x
}

fn with<'b, F: FnOnce(&'b mut u32) -> &'b mut u32>(x: &'b mut u32, f: F) -> &'b mut u32 {
    f(x)
}

pub fn bump(v: &mut u32) {
    let r = with(v, ident);
    *r += 1;
}
