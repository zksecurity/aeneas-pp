//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Loops comparing against promoted constants holding shared references
//! (`Some(&b'"')`): each iteration borrows a fresh instance of the constant,
//! whose shared value contains shared borrows.

pub fn first_quote(bytes: &[u8], cursor: &mut usize) -> Result<u32, ()> {
    loop {
        if bytes.get(*cursor) != Some(&b'"') {
            return Err(());
        }
        *cursor += 1;
        if *cursor > 3 {
            break;
        }
    }
    Ok(0)
}

pub fn count_until(bytes: &[u8], c: u8) -> usize {
    let mut i = 0;
    while bytes.get(i) != Some(&c) && i < bytes.len() {
        i += 1;
    }
    i
}
