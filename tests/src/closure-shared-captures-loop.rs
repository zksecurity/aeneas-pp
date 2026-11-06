//@ [!lean] skip
//@ charon-args=--no-code-duplication --monomorphize-mut=except-types
//@ aeneas-args=-strict-joins
//! A loop calls a closure which captures shared borrows next to a mutable one.
//! Joining the closure state across iterations projects it on the regions of
//! its shared captures, where nothing is given back; the projectors of the
//! state and of the checker are paired by the values the variables relate.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Node {
    Pi(u32, u32),
    Other,
}

pub struct Terms {
    pub nodes: Vec<Node>,
}

pub struct Checker<'a> {
    pub t: &'a mut Terms,
    pub locals: Vec<u32>,
}

impl<'a> Checker<'a> {
    pub fn local(&mut self, a: u32) -> u32 {
        self.locals.push(a);
        self.locals.len() as u32
    }

    pub fn telescope(
        &mut self,
        e: u32,
        mut next: impl FnMut(&mut Self, usize, u32) -> Result<Option<u32>, ()>,
    ) -> Result<(Vec<u32>, u32), ()> {
        let mut values = Vec::new();
        let mut body = e;
        while let Node::Pi(a, b) = self.t.nodes[body as usize] {
            let domain = a + values.len() as u32;
            let Some(v) = next(self, values.len(), domain)? else {
                break;
            };
            values.push(v);
            body = b;
        }
        Ok((values, body))
    }
}

pub fn generate(ck: &mut Checker<'_>, ty: u32, np: usize, params: &Vec<u32>) -> Result<bool, ()> {
    let mut reflexive = false;
    let (values, _ty) = ck.telescope(ty, |ck, count, a| {
        if count < np {
            return Ok(Some(params[count]));
        }
        if a == 3 {
            reflexive = true;
        }
        Ok(Some(ck.local(a)))
    })?;
    Ok(reflexive && values.len() > 1)
}

#[verify::test]
pub fn test_generate() {
    let mut t = Terms { nodes: vec![Node::Pi(5, 1), Node::Pi(1, 2), Node::Pi(1, 3), Node::Other] };
    let mut ck = Checker { t: &mut t, locals: Vec::new() };
    assert!(matches!(generate(&mut ck, 0, 1, &vec![7]), Ok(true)));
    assert!(ck.locals.len() == 2);
    assert!(matches!(generate(&mut ck, 2, 0, &vec![]), Ok(false)));
    assert!(matches!(generate(&mut ck, 3, 0, &vec![]), Ok(false)));
}
