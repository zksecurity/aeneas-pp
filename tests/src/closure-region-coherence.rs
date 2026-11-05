//@ [!lean] skip
//@ [lean] known-failure
//@ charon-args=--no-code-duplication
//! A function relating the regions of the arguments of a closure which the
//! closure itself keeps apart: the closure gives back the borrowed values in a
//! different way than the function expects, which we don't support yet.

pub struct Eng<'a> {
    pub t: &'a mut Vec<u32>,
}

impl<'a> Eng<'a> {
    fn pair<T>(&mut self, other: &mut Eng<'a>, f: impl FnOnce(&mut Self, &mut Eng<'a>) -> T) -> T {
        f(self, other)
    }

    pub fn push_both(&mut self, other: &mut Eng<'a>, x: u32) -> usize {
        self.pair(other, |a, b| {
            a.t.push(x);
            b.t.push(x);
            a.t.len() + b.t.len()
        })
    }
}
