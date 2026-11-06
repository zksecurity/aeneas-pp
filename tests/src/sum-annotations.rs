//@ [!lean] skip
//! The sums which encode the early returns of a switch are annotated with the
//! parts of their types which the values they deliver don't determine: the
//! early return delivers `None`, whose type Lean doesn't infer, and the join
//! delivers variables.
#![feature(register_tool)]
#![register_tool(verify)]

pub fn first_large(x: u32, y: u32, z: u32) -> Option<u32> {
    let (a, b) = if x > 10 {
        if y > 10 { return None } else { (x, y) }
    } else {
        (z, x)
    };
    Some(a + b)
}

#[verify::test]
fn test_first_large() {
    assert!(matches!(first_large(11, 11, 0), None));
    assert!(matches!(first_large(11, 1, 0), Some(12)));
    assert!(matches!(first_large(1, 1, 5), Some(6)));
}
