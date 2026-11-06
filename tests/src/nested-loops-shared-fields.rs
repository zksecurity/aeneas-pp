//@ [!lean] skip
//@ aeneas-args=-strict-joins
//! Nested loops reading a structure of shared borrows: the loops don't reborrow
//! the shared slices (their values never change), so the abstractions of the
//! fixed point of the inner loop list the shared borrows in another order than
//! the abstraction of the call which borrows the structure's fields.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Node {
    Bound(u32),
    App(u32, u32),
    Let(u32, u32, u32),
    Str(std::sync::Arc<String>),
}

pub struct Terms {
    pub nodes: Vec<Node>,
}

pub struct Env {
    pub decls: Vec<u32>,
}

#[derive(Clone, Copy)]
pub struct View<'v, 'a: 'v> {
    t: &'v Terms,
    nodes: &'a [Node],
    env: &'a Env,
    locals: &'a [(u32, Option<u32>)],
}

const SPINE: usize = 4;

impl<'v, 'a> View<'v, 'a> {
    fn node(self, e: u32) -> &'v Node {
        match self.nodes.get(e as usize) {
            Some(n) => n,
            None => &self.t.nodes[e as usize],
        }
    }

    pub fn peel_apps<'b>(
        self,
        mut e: u32,
        buf: &'b mut [u32; SPINE],
        spill: &'b mut Vec<u32>,
    ) -> (u32, &'b [u32]) {
        let mut n = 0;
        while let Node::App(f, a) = *self.node(e) {
            if n == SPINE {
                spill.extend_from_slice(buf);
                while let Node::App(f, a) = *self.node(e) {
                    spill.push(a);
                    e = f;
                }
                return (e, spill);
            }
            buf[n] = a;
            n += 1;
            e = f;
        }
        (e, &buf[..n])
    }
}
