//@ [!lean] skip
//@ charon-args=--no-code-duplication
//! Loops reading through the shared borrow of an input.
#![feature(register_tool)]
#![register_tool(verify)]

const EMPTY: u64 = u64::MAX;

pub struct Table {
    slots: Vec<(u64, u32)>,
    len: usize,
}

impl Table {
    /// Open addressing lookup: the loop reads the slots of [self] at each iteration.
    pub fn get(&self, key: u64) -> Option<u32> {
        if self.len == 0 {
            return None;
        }
        let mask = self.slots.len() - 1;
        let mut i = (key as usize) & mask;
        loop {
            let (k, v) = self.slots[i];
            if k == key {
                return Some(v);
            }
            if k == EMPTY {
                return None;
            }
            i = (i + 1) & mask;
        }
    }
}

#[verify::test]
pub fn test_get() {
    let mut slots = Vec::new();
    slots.push((4, 40));
    slots.push((1, 10));
    slots.push((5, 50));
    slots.push((EMPTY, 0));
    let t = Table { slots, len: 3 };
    assert!(matches!(t.get(1), Some(10)));
    assert!(matches!(t.get(5), Some(50)));
    assert!(matches!(t.get(3), None));
}
