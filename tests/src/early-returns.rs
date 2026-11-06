//@ [!lean] skip
//@ charon-args=--no-code-duplication
//@ aeneas-args=-strict-joins
//! Early returns (`?`, `let ... else { return ... }`) in control flow
//! reconstructed without duplicating code: the code after a branch which
//! returns continues in the other branch, and loops only take and output what
//! they modify.
#![feature(register_tool)]
#![register_tool(verify)]

pub enum Head {
    Const(u32),
    Var(u32),
    Sort,
}

pub enum Val {
    Neutral(Head, u32),
    Lam(u32),
    Pi(u32),
}

fn check(x: u32) -> Result<u32, u32> {
    if x > 100 { Err(x) } else { Ok(x + 1) }
}

pub fn chain(x: u32) -> Result<u32, u32> {
    let a = check(x)?;
    let b = check(a)?;
    Ok(b)
}

/// The failing patterns share their `else` block.
pub fn let_else(v: &Val, n: u32) -> Result<u32, u32> {
    let Val::Neutral(Head::Const(c), sp) = v else {
        return Err(0);
    };
    if *c != n || *sp > 10 {
        return Err(1);
    }
    let d = check(*c)?;
    Ok(d + *sp)
}

pub struct Ctx<'a> {
    pub xs: &'a [u32],
    pub ys: &'a [u32],
    pub count: u32,
}

impl<'a> Ctx<'a> {
    /// The loop doesn't modify [xs] and [ys]: it doesn't output them.
    pub fn sum(&mut self, k: u32) -> Result<u32, u32> {
        let mut acc = 0;
        for i in 0..k {
            let x = check(self.xs[i as usize])?;
            acc = check(acc + x + self.ys.len() as u32)?;
            self.count += 1;
        }
        Ok(acc)
    }
}

#[verify::test]
fn test_early_returns() {
    assert!(matches!(chain(1), Ok(3)));
    assert!(matches!(chain(100), Err(101)));
    assert!(matches!(let_else(&Val::Neutral(Head::Const(3), 2), 3), Ok(6)));
    assert!(matches!(let_else(&Val::Neutral(Head::Const(3), 2), 4), Err(1)));
    assert!(matches!(let_else(&Val::Neutral(Head::Var(3), 2), 3), Err(0)));
    assert!(matches!(let_else(&Val::Lam(3), 3), Err(0)));
    let xs = [1, 2, 3];
    let ys = [0];
    let mut ctx = Ctx { xs: &xs, ys: &ys, count: 0 };
    assert!(matches!(ctx.sum(3), Ok(15)));
    assert!(ctx.count == 3);
    let xs = [1, 200];
    let mut ctx = Ctx { xs: &xs, ys: &ys, count: 0 };
    assert!(matches!(ctx.sum(2), Err(200)));
    assert!(ctx.count == 1);
}
