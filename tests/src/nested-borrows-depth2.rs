//@ [!lean] skip
//! Mutable borrows nested two levels deep, with distinct lifetimes.

pub struct E<'a> {
    pub t: &'a mut u32,
}

pub fn incr3(x: &mut &mut &mut u32) {
    ***x += 1;
}

pub fn read_e(e: &mut &mut E<'_>) -> u32 {
    *e.t
}

pub fn incr_e(e: &mut &mut E<'_>) {
    *e.t += 1;
}

/// Makes the innermost reference point to `z`: the original referent keeps its value.
pub fn retarget<'a, 'b, 'c>(x: &'a mut &'b mut &'c mut u32, z: &'c mut u32) {
    **x = z;
}
