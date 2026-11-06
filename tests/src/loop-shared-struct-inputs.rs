//@ [!lean] skip
//! A loop reading the fields of a structure behind a shared borrow, which the
//! function expands before the loop: the loop takes the structure as one
//! input, rather than one input per field.

pub struct EnvNode {
    pub parent: u32,
    pub value: u32,
    pub frame: u32,
}

pub struct Store {
    pub envs: Vec<EnvNode>,
    pub frames: Vec<u64>,
    pub values: Vec<u32>,
}

#[derive(Clone, Copy)]
pub struct View<'v, 'a: 'v> {
    s: &'v Store,
    nodes: &'a [u32],
}

impl<'v, 'a> View<'v, 'a> {
    pub fn lookup(self, mut env: u32, mut i: u32) -> Result<u32, u32> {
        if i >= self.s.envs[env as usize].value {
            return Err(i);
        }
        loop {
            let node = &self.s.envs[env as usize];
            if node.frame != 0 {
                return Ok(self.s.values[node.frame as usize] + self.nodes.len() as u32);
            }
            if i == 0 {
                return Ok(node.value);
            }
            i -= 1;
            env = node.parent;
        }
    }
}
