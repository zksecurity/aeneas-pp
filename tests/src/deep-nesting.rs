//@ [!lean] skip
//! Code nested deeper than the default indentation limit of the formatter.
#![feature(register_tool)]
#![register_tool(verify)]

pub fn deep(x: u32) -> u32 {
if x > 1 {
 let meta = x - 1;
 meta + (if x > 2 {
 let meta = x - 2;
 meta + (if x > 3 {
 let meta = x - 3;
 meta + (if x > 4 {
 let meta = x - 4;
 meta + (if x > 5 {
 let meta = x - 5;
 meta + (if x > 6 {
 let meta = x - 6;
 meta + (if x > 7 {
 let meta = x - 7;
 meta + (if x > 8 {
 let meta = x - 8;
 meta + (if x > 9 {
 let meta = x - 9;
 meta + (if x > 10 {
 let meta = x - 10;
 meta + (if x > 11 {
 let meta = x - 11;
 meta + (if x > 12 {
 let meta = x - 12;
 meta + (if x > 13 {
 let meta = x - 13;
 meta + (if x > 14 {
 let meta = x - 14;
 meta + (if x > 15 {
 let meta = x - 15;
 meta + (if x > 16 {
 let meta = x - 16;
 meta + (if x > 17 {
 let meta = x - 17;
 meta + (if x > 18 {
 let meta = x - 18;
 meta + (if x > 19 {
 let meta = x - 19;
 meta + (if x > 20 {
 let meta = x - 20;
 meta + (if x > 21 {
 let meta = x - 21;
 meta + (if x > 22 {
 let meta = x - 22;
 meta + (if x > 23 {
 let meta = x - 23;
 meta + (if x > 24 {
 let meta = x - 24;
 meta + (if x > 25 {
 let meta = x - 25;
 meta + (if x > 26 {
 let meta = x - 26;
 meta + (if x > 27 {
 let meta = x - 27;
 meta + (if x > 28 {
 let meta = x - 28;
 meta + (if x > 29 {
 let meta = x - 29;
 meta + (if x > 30 {
 let meta = x - 30;
 meta + (if x > 31 {
 let meta = x - 31;
 meta + (if x > 32 {
 let meta = x - 32;
 meta + (if x > 33 {
 let meta = x - 33;
 meta + (if x > 34 {
 let meta = x - 34;
 meta + (if x > 35 {
 let meta = x - 35;
 meta + (if x > 36 {
 let meta = x - 36;
 meta + (if x > 37 {
 let meta = x - 37;
 meta + (if x > 38 {
 let meta = x - 38;
 meta + (if x > 39 {
 let meta = x - 39;
 meta + (if x > 40 {
 let meta = x - 40;
 meta + (x)
 } else {
 40
 })
 } else {
 39
 })
 } else {
 38
 })
 } else {
 37
 })
 } else {
 36
 })
 } else {
 35
 })
 } else {
 34
 })
 } else {
 33
 })
 } else {
 32
 })
 } else {
 31
 })
 } else {
 30
 })
 } else {
 29
 })
 } else {
 28
 })
 } else {
 27
 })
 } else {
 26
 })
 } else {
 25
 })
 } else {
 24
 })
 } else {
 23
 })
 } else {
 22
 })
 } else {
 21
 })
 } else {
 20
 })
 } else {
 19
 })
 } else {
 18
 })
 } else {
 17
 })
 } else {
 16
 })
 } else {
 15
 })
 } else {
 14
 })
 } else {
 13
 })
 } else {
 12
 })
 } else {
 11
 })
 } else {
 10
 })
 } else {
 9
 })
 } else {
 8
 })
 } else {
 7
 })
 } else {
 6
 })
 } else {
 5
 })
 } else {
 4
 })
 } else {
 3
 })
 } else {
 2
 })
 } else {
 1
 }
}

#[verify::test]
pub fn test_deep() {
    assert!(deep(0) == 1);
    assert!(deep(3) == 6);
}
