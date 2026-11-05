//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins of a value expanded in one branch, where a loan below one of its
//! borrows is still live, with the unexpanded value of the other branch.
#![feature(register_tool)]
#![register_tool(verify)]

pub struct Table {
    pub keys: Vec<u64>,
}

impl Table {
    pub fn contains(&self, key: u64) -> bool {
        let mut i = 0;
        while i < self.keys.len() {
            if self.keys[i] == key {
                return true;
            }
            i += 1;
        }
        false
    }

    pub fn insert(&mut self, key: u64) {
        self.keys.push(key)
    }
}

pub struct Store {
    pub equal: [Table; 2],
    pub unequal: [Table; 2],
}

pub struct Engine<'a> {
    pub s: &'a mut Store,
    pub eager: bool,
}

impl<'a> Engine<'a> {
    fn step(&mut self, x: u32, y: u32) -> Result<bool, u32> {
        if x > 100 {
            Err(x)
        } else if x == y {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// The branch which records an equality leaves the loan of the indexed
    /// table live, while the other branch keeps `self` as returned by `step`.
    pub fn equal(&mut self, x: u32, y: u32, budget: u32) -> Result<bool, u32> {
        let key = x as u64;
        let eager = usize::from(self.eager);
        if self.s.equal[eager].contains(key) {
            return Ok(true);
        }
        let r = match self.step(x, y) {
            Ok(r) => r,
            Err(e) => return Err(e),
        };
        if r {
            self.s.equal[eager].insert(key);
        } else if budget > 0 {
            self.s.unequal[eager].insert(key);
        }
        Ok(r)
    }
}

#[verify::test]
pub fn test_equal() {
    let mut s = Store {
        equal: [Table { keys: Vec::new() }, Table { keys: Vec::new() }],
        unequal: [Table { keys: Vec::new() }, Table { keys: Vec::new() }],
    };
    let mut e = Engine { s: &mut s, eager: true };
    assert!(matches!(e.equal(3, 3, 1), Ok(true)));
    assert!(matches!(e.equal(3, 4, 1), Ok(true)));
    assert!(matches!(e.equal(4, 5, 1), Ok(false)));
    assert!(matches!(e.equal(200, 5, 1), Err(200)));
    assert!(s.equal[1].keys.len() == 1 && s.unequal[1].keys.len() == 1);
}
