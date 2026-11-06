//@ [!lean] skip
//! `Arc` is modeled as the value it points to.
#![feature(register_tool)]
#![register_tool(verify)]
use std::sync::Arc;

/// A recursive type nesting through `Arc`.
pub struct Bucket {
    id: u32,
    rest: Option<Arc<Bucket>>,
}

pub fn push(b: Arc<Bucket>, id: u32) -> Arc<Bucket> {
    Arc::new(Bucket { id, rest: Some(b) })
}

pub fn second(b: &Arc<Bucket>) -> Option<u32> {
    match &b.rest {
        Some(r) => Some(r.id),
        None => None,
    }
}

pub fn shared_len(v: Vec<u32>) -> usize {
    let s: Arc<[u32]> = Arc::from(v);
    let t = s.clone();
    t.len()
}

pub fn same(a: &Arc<u32>, b: &Arc<u32>) -> bool {
    a == b
}

/// `Arc::as_ref` as a function item.
pub fn get(o: Option<&Arc<u32>>) -> Option<&u32> {
    o.map(Arc::as_ref)
}

#[verify::test]
pub fn test_arc() {
    let b = push(Arc::new(Bucket { id: 1, rest: None }), 2);
    assert!(b.id == 2);
    assert!(matches!(second(&b), Some(1)));
    assert!(shared_len(vec![1, 2, 3]) == 3);
    assert!(same(&Arc::new(3), &Arc::new(3)));
}
