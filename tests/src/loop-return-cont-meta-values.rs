//@ [!lean] skip
//@ aeneas-args=-strict-joins
//@ charon-args=--no-code-duplication
//! A loop over `&mut self`, where `self` holds mutable borrows, which returns
//! through `?` and from a match on a node read through a shared borrow of
//! `self`: the code after the join of the match ends the abstraction of the
//! first call of the iteration, whose continuation reads the fields of `self`
//! expanded before the match.
#![feature(register_tool)]
#![register_tool(verify)]

#[derive(Clone, Copy)]
pub enum Node {
    Var(u32),
    Let(u32, u32),
    App(u32, u32),
}

pub struct Terms {
    pub nodes: Vec<Node>,
}

pub struct Store {
    pub envs: Vec<u32>,
}

pub struct Engine<'a> {
    pub t: &'a mut Terms,
    pub nodes: &'a [Node],
    pub s: &'a mut Store,
    pub d: u32,
}

#[derive(Clone, Copy)]
pub struct View<'v, 'a: 'v> {
    pub t: &'v Terms,
    pub nodes: &'a [Node],
}

impl<'v, 'a> View<'v, 'a> {
    pub fn node(self, e: u32) -> &'v Node {
        match self.nodes.get(e as usize) {
            Some(n) => n,
            None => &self.t.nodes[e as usize - self.nodes.len()],
        }
    }
}

impl<'a> Engine<'a> {
    pub fn view(&self) -> View<'_, 'a> {
        View {
            t: &*self.t,
            nodes: self.nodes,
        }
    }

    pub fn eval(&mut self, env: u32, e: u32) -> Result<u32, ()> {
        if e > 100 || e == 3 {
            return Err(());
        }
        self.d += 1;
        Ok(env + e)
    }

    pub fn extend(&mut self, parent: u32, v: u32) -> u32 {
        self.s.envs.push(parent + v);
        self.s.envs.len() as u32
    }

    pub fn eval_let(&mut self, mut env: u32, mut value: u32, mut body: u32) -> Result<u32, ()> {
        loop {
            let v = self.eval(env, value)?;
            env = self.extend(env, v);
            match *self.view().node(body) {
                Node::Let(v, b) => (value, body) = (v, b),
                _ => return self.eval(env, body),
            }
        }
    }
}

pub fn run(value: u32, nodes: &[Node]) -> (Result<u32, ()>, u32, usize) {
    let mut t = Terms {
        nodes: vec![Node::Var(5), Node::App(0, 200)],
    };
    let mut s = Store { envs: Vec::new() };
    let mut e = Engine {
        t: &mut t,
        nodes,
        s: &mut s,
        d: 0,
    };
    let r = e.eval_let(1, value, 0);
    let d = e.d;
    (r, d, s.envs.len())
}

#[verify::test]
pub fn test_eval_let() {
    // Let(2, 1), then node 1 (App) returns from the loop
    let nodes = [Node::Let(2, 1), Node::App(0, 7)];
    assert!(matches!(run(1, &nodes), (Ok(3), 3, 2)));
    // Let(2, 1), Let(4, 2), then node 2 (Var, in the terms)
    let nodes = [Node::Let(2, 1), Node::Let(4, 2)];
    assert!(matches!(run(1, &nodes), (Ok(5), 4, 3)));
    // The evaluation in the loop fails
    let nodes = [Node::Let(101, 1), Node::App(0, 7)];
    assert!(matches!(run(1, &nodes), (Err(()), 1, 1)));
    // The evaluation after the loop fails
    let nodes = [Node::Let(2, 3), Node::Var(0)];
    assert!(matches!(run(1, &nodes), (Err(()), 2, 2)));
}
