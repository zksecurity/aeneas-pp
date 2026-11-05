//@ [!lean] skip
//! Functions which are mutually recursive with closures through an opaque
//! generic helper.
#![feature(register_tool)]
#![register_tool(verify)]

#[verify::opaque]
fn apply<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

pub fn sum_to(n: u32) -> u32 {
    if n == 0 { 0 } else { n + apply(|k| sum_to(k), n - 1) }
}
