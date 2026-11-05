//@ [!lean] skip
//@ charon-args=--no-code-duplication --monomorphize-mut=except-types
//! Two closures capturing mutable borrows, passed to the same trait method: each
//! specialization of the method gets its own name.

fn has_repeat(xs: &[u32], seen: &mut Vec<u32>) -> bool {
    xs.iter().any(|n| {
        let dup = seen.contains(n);
        seen.push(*n);
        dup
    })
}

fn count_until(xs: &[u32], count: &mut u32, stop: u32) -> bool {
    xs.iter().any(|n| {
        *count += 1;
        *n == stop
    })
}
