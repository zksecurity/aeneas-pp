//@ [!lean] skip
//! Joins of contexts where a struct holding mutable borrows is itself
//! mutably borrowed (`&'b mut S<'a>` with `S<'a>` holding `&'a mut T`), in
//! one branch only, in both, or a different number of times.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Ck<'a> {
    pub t: &'a mut Vec<u32>,
    pub e: &'a Vec<u32>,
    pub s: &'a mut Vec<u32>,
}

impl<'a> Ck<'a> {
    pub fn push_t(&mut self, x: u32) -> u32 {
        self.t.push(x);
        x
    }

    pub fn push_both(&mut self, x: u32) -> u32 {
        self.t.push(x);
        self.s.push(x + self.e.len() as u32);
        x
    }

    pub fn swap(&mut self) {
        std::mem::swap(self.t, self.s);
    }
}

fn helper(ck: &mut Ck<'_>, x: u32) -> u32 {
    ck.push_both(x)
}

/// No shared field.
pub struct Mk<'a> {
    pub t: &'a mut Vec<u32>,
    pub s: &'a mut Vec<u32>,
}

fn mk_helper(mk: &mut Mk<'_>, x: u32) {
    mk.t.push(x);
    mk.s.push(x);
}

pub fn helper_in_one_branch(t: &mut Vec<u32>, e: &Vec<u32>, s: &mut Vec<u32>, k: u32) -> u32 {
    let mut ck = Ck { t, e, s };
    let r = if k == 0 { helper(&mut ck, 1) } else { 2 };
    helper(&mut ck, r)
}

pub fn method_in_one_branch(t: &mut Vec<u32>, e: &Vec<u32>, s: &mut Vec<u32>, k: u32) -> u32 {
    let mut ck = Ck { t, e, s };
    let r = if k == 0 { ck.push_both(1) } else { 2 };
    ck.push_both(r)
}

pub fn helper_counts_differ(t: &mut Vec<u32>, e: &Vec<u32>, s: &mut Vec<u32>, k: u32) -> u32 {
    let mut ck = Ck { t, e, s };
    let r = if k == 0 {
        helper(&mut ck, 1)
    } else {
        let a = helper(&mut ck, 2);
        helper(&mut ck, a)
    };
    helper(&mut ck, r)
}

pub fn methods_counts_differ(t: &mut Vec<u32>, e: &Vec<u32>, s: &mut Vec<u32>, k: u32) -> u32 {
    let mut ck = Ck { t, e, s };
    let r = if k == 0 {
        ck.push_t(1)
    } else {
        let a = ck.push_both(2);
        ck.push_t(a)
    };
    ck.push_both(r)
}

pub fn swap_in_one_branch(t: &mut Vec<u32>, e: &Vec<u32>, s: &mut Vec<u32>, k: u32) {
    let mut ck = Ck { t, e, s };
    if k == 0 {
        ck.swap();
    }
    ck.push_t(7);
}

pub fn no_shared_field(t: &mut Vec<u32>, s: &mut Vec<u32>, k: u32) {
    let mut mk = Mk { t, s };
    if k == 0 {
        mk_helper(&mut mk, 1);
    }
    mk_helper(&mut mk, 2);
}

#[verify::test]
pub fn test_helper_in_one_branch() {
    let (mut t, e, mut s) = (Vec::new(), Vec::new(), Vec::new());
    assert!(helper_in_one_branch(&mut t, &e, &mut s, 0) == 1);
    assert!(t.len() == 2 && t[0] == 1 && t[1] == 1);
    assert!(s.len() == 2);
    let (mut t, mut s) = (Vec::new(), Vec::new());
    assert!(helper_in_one_branch(&mut t, &e, &mut s, 1) == 2);
    assert!(t.len() == 1 && t[0] == 2 && s.len() == 1 && s[0] == 2);
}

#[verify::test]
pub fn test_methods_counts_differ() {
    let e = Vec::new();
    let (mut t, mut s) = (Vec::new(), Vec::new());
    methods_counts_differ(&mut t, &e, &mut s, 0);
    assert!(t.len() == 2 && s.len() == 1);
    let (mut t, mut s) = (Vec::new(), Vec::new());
    methods_counts_differ(&mut t, &e, &mut s, 1);
    assert!(t.len() == 3 && s.len() == 2);
}

#[verify::test]
pub fn test_swap_in_one_branch() {
    let e = Vec::new();
    let (mut t, mut s) = (Vec::new(), Vec::new());
    s.push(5);
    swap_in_one_branch(&mut t, &e, &mut s, 0);
    assert!(t.len() == 2 && t[0] == 5 && t[1] == 7 && s.len() == 0);
    let (mut t, mut s) = (Vec::new(), Vec::new());
    swap_in_one_branch(&mut t, &e, &mut s, 1);
    assert!(t.len() == 1 && s.len() == 0);
}

#[verify::test]
pub fn test_no_shared_field() {
    let (mut t, mut s) = (Vec::new(), Vec::new());
    no_shared_field(&mut t, &mut s, 0);
    assert!(t.len() == 2 && s.len() == 2);
}
