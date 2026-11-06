//@ [!lean] skip
//! `Arc` is modeled as the value it points to.
#![feature(register_tool)]
#![register_tool(verify)]
use std::borrow::Borrow;
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

/// `Arc<T>: Borrow<T>` used through a generic bound.
pub fn via_borrow<B: Borrow<u32>>(b: &B) -> u32 {
    *b.borrow()
}

pub fn borrowed(a: Arc<u32>) -> u32 {
    via_borrow(&a)
}

/// `Arc<[T]>: From<Vec<T>>` used through a generic bound.
pub fn via_from<S: From<Vec<u32>>>(v: Vec<u32>) -> S {
    S::from(v)
}

pub fn first(v: Vec<u32>) -> Option<u32> {
    let s: Arc<[u32]> = via_from(v);
    if s.len() == 0 { None } else { Some(s[0]) }
}

#[verify::test]
pub fn test_arc() {
    let b = push(Arc::new(Bucket { id: 1, rest: None }), 2);
    assert!(b.id == 2);
    assert!(matches!(second(&b), Some(1)));
    assert!(shared_len(vec![1, 2, 3]) == 3);
    assert!(same(&Arc::new(3), &Arc::new(3)));
    assert!(borrowed(Arc::new(5)) == 5);
    assert!(matches!(first(vec![7, 8]), Some(7)));
    assert!(matches!(first(vec![]), None));
}
