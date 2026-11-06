//@ [!lean] skip
//! `?` on `Result` and `Option` is translated to a match on the value it is
//! applied to, converting the error with its `From` instance when it is not
//! the identity.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Error {
    Message(u32),
    Code(u8),
}

impl From<u8> for Error {
    fn from(c: u8) -> Self {
        Error::Code(c)
    }
}

fn half(x: u32) -> Result<u32, u8> {
    if x % 2 == 0 { Ok(x / 2) } else { Err(1) }
}

fn checked(x: u32) -> Result<u32, Error> {
    if x < 100 { Ok(x) } else { Err(Error::Message(x)) }
}

/// The identity conversion, and an output type which differs from the type of
/// the value `?` is applied to.
pub fn same_error(x: u32) -> Result<bool, Error> {
    let y = checked(x)?;
    Ok(y > 10)
}

/// A conversion with the `From` instance.
pub fn converted_error(x: u32) -> Result<u32, Error> {
    let y = half(x)?;
    let z = checked(y)?;
    Ok(z + 1)
}

pub fn first_some(v: &[u32]) -> Option<u32> {
    let x = v.first()?;
    Some(*x + 1)
}

#[verify::test]
fn test_try() {
    assert!(matches!(same_error(20), Ok(true)));
    assert!(matches!(same_error(200), Err(Error::Message(200))));
    assert!(matches!(converted_error(20), Ok(11)));
    assert!(matches!(converted_error(21), Err(Error::Code(1))));
    assert!(matches!(converted_error(400), Err(Error::Message(200))));
}
