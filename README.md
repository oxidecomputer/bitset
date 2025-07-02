# Bitset

**This is an experimental crate.**

The goal of this crate is to develop a bitset type whose fields are statically
typed according to their length. The idea is for complex code that deals in
sub-byte fields, we have a way to pass such fields around in a type safe way.

For example:

```rust
// Create a bitset of width 8, with three fields a, b and c.
let mut x = BitSet::<8>::from(0b1_0101_111);
//                                  ^    ^   ^
//                                  c    b   a

// Extract individual fields. Note that the extracted field is statically
// typed according to width.
let a: BitSet<3> = x.get_field::<3, 0>().unwrap();
let b: BitSet<4> = x.get_field::<4, 3>().unwrap();
let c: BitSet<1> = x.get_field::<1, 7>().unwrap();
assert_eq!(u8::from(a), 0b111);
assert_eq!(u8::from(b), 0b0101);
assert_eq!(u8::from(c), 0b1);

// Now set a feild. Note that setting a field requires a bitset with the
// correct width.
let b = BitSet::<4>::from_int(0b1010).unwrap();
x.set_field::<4, 3>(b).unwrap();
assert_eq!(u8::from(a), 0b111);
assert_eq!(u8::from(b), 0b1010);
assert_eq!(u8::from(c), 0b1);
assert_eq!(u8::from(x), 0b1_1010_111);
```

This crate requires nightly Rust with the `generic_const_exprs` feature.
