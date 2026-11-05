//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Joins of paths on which locals are dead, and the call abstractions only they keep alive.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Error {
    Invalid,
}

/// The error paths of `?` jump to the end: `hex` still borrows from `bytes` on the second one.
pub fn unicode_escape(bytes: &[u8], at: usize) -> Result<u32, Error> {
    let invalid = || Error::Invalid;
    if bytes.get(at..at + 2) != Some(b"\\u") {
        return Err(invalid());
    }
    let hex = bytes.get(at + 2..at + 6).ok_or_else(invalid)?;
    let hex = std::str::from_utf8(hex).map_err(|_| invalid())?;
    u32::from_str_radix(hex, 16).map_err(|_| invalid())
}

fn pick(o: Option<&[u8]>) -> Option<&[u8]> {
    o
}

/// Two calls borrow from the same shared value.
pub fn two_borrowers(bytes: &[u8], at: usize) -> Result<u8, ()> {
    let s = bytes.get(at..at + 2);
    let a = pick(s).ok_or(())?;
    let b = pick(s).ok_or(())?;
    Ok(a[0] + b[1])
}

/// A local with drop glue, initialized on one path only.
pub fn maybe_owned(v: &[u8], b: bool) -> usize {
    let s: Vec<u8>;
    if b {
        s = v.to_vec();
        if s.len() > 2 {
            return s.len();
        }
    }
    0
}
