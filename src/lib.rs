// Copyright Oxide Computer Company 2025

#![feature(generic_const_exprs)]
#![allow(incomplete_features)]
#![allow(clippy::unusual_byte_groupings)]

use seq_macro::seq;
use std::error::Error;
use std::fmt::Display;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct BitSet<const BITS: usize>(pub [u8; ((BITS - 1) >> 3) + 1])
where
    [(); ((BITS - 1) >> 3) + 1]:;

impl<const BITS: usize> Default for BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    fn default() -> Self {
        Self([0; ((BITS - 1) >> 3) + 1])
    }
}

impl<const BITS: usize> std::fmt::LowerHex for BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> Result<(), std::fmt::Error> {
        write!(f, "{:x?}", self.0)
    }
}

impl<const BITS: usize> std::fmt::UpperHex for BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
    ) -> Result<(), std::fmt::Error> {
        write!(f, "{:X?}", self.0)
    }
}

impl BitSet<1> {
    pub const TRUE: Self = Self::from_bool(true);
    pub const FALSE: Self = Self::from_bool(false);
}

impl From<bool> for BitSet<1> {
    fn from(value: bool) -> Self {
        Self::from_bool(value)
    }
}

pub const fn zero<const BITS: usize>() -> BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    BitSet::<BITS>::ZERO
}

impl<const BITS: usize> BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    pub const ZERO: Self = Self([0; ((BITS - 1) >> 3) + 1]);

    pub fn max() -> Result<Self, OutOfBounds> {
        let mut s = Self([0xff; ((BITS - 1) >> 3) + 1]);
        s.mask()?;
        Ok(s)
    }

    fn mask(&mut self) -> Result<(), OutOfBounds> {
        let mask = ((1 << (BITS % 8)) - 1) as u8;
        let pos = BITS >> 3;
        if pos > self.0.len() {
            return Err(OutOfBounds {});
        }
        if mask == 0 {
            return Ok(());
        }

        self.0[pos] &= mask;

        Ok(())
    }

    pub fn get_field<const FBITS: usize, const OFFSET: usize>(
        &self,
    ) -> Result<BitSet<FBITS>, OutOfBounds>
    where
        [(); ((FBITS - 1) >> 3) + 1]:,
        [(); BITS - FBITS]:,
    {
        assert!(FBITS <= BITS);
        let sub =
            &self.0[(OFFSET >> 3)..(OFFSET >> 3) + (((FBITS - 1) >> 3) + 1)];
        let mut result = BitSet::<FBITS>(sub.try_into().unwrap());
        result = result.shr(OFFSET % 8);
        result.mask()?;
        Ok(result)
    }

    pub fn extend_right<const XBITS: usize>(&self) -> BitSet<{ BITS + XBITS }>
    where
        [(); (((BITS + XBITS) - 1) >> 3) + 1]:,
        [(); BITS + XBITS]:,
    {
        let mut result = BitSet::<{ BITS + XBITS }>::default();
        for i in 0..((BITS - 1) >> 3) + 1 {
            result.0[i] = self.0[i];
        }
        result
    }

    pub fn extend_left<const XBITS: usize>(&self) -> BitSet<{ BITS + XBITS }>
    where
        [(); (((BITS + XBITS) - 1) >> 3) + 1]:,
    {
        let mut result = self.extend_right();
        result = result.shr(XBITS);
        result
    }

    pub fn set_field<const FBITS: usize, const OFFSET: usize>(
        &mut self,
        value: BitSet<FBITS>,
    ) -> Result<(), OutOfBounds>
    where
        [(); ((FBITS - 1) >> 3) + 1]:,
        [(); (((FBITS + OFFSET) - 1) >> 3) + 1]:,
        [(); BITS - FBITS]:,
    {
        let m = BitSet::<FBITS>::max().unwrap();
        let mut mask = BitSet::<BITS>::default();
        for (i, x) in m.0.iter().enumerate() {
            mask.0[i] = *x;
        }
        mask = mask.shl(OFFSET);
        mask = mask.not();
        *self = self.and(mask);

        let mut v = BitSet::<BITS>::default();
        for (i, x) in value.0.iter().enumerate() {
            v.0[i] = *x;
        }
        v = v.shl(OFFSET);
        *self = self.or(v);

        Ok(())
    }

    #[allow(clippy::should_implement_trait)]
    pub fn shr(mut self, count: usize) -> Self {
        // TODO: use integer ops for size <= 128
        for _ in 0..count {
            let mut carry = false;
            for x in self.0.iter_mut().rev() {
                let to_carry = (*x & 1) != 0;
                *x >>= 1;
                if carry {
                    *x |= 1 << 7;
                }
                carry = to_carry;
            }
        }
        self
    }

    #[allow(clippy::should_implement_trait)]
    pub fn shl(mut self, count: usize) -> Self {
        // TODO: use integer ops for size <= 128
        for _ in 0..count {
            let mut carry = false;
            for x in self.0.iter_mut() {
                let to_carry = (*x & (1 << 7)) != 0;
                *x <<= 1;
                if carry {
                    *x |= 1;
                }
                carry = to_carry;
            }
        }
        self
    }

    pub fn and(&self, other: Self) -> Self {
        let mut result = Self::default();
        for i in 0..((BITS - 1) >> 3) + 1 {
            result.0[i] = self.0[i] & other.0[i];
        }
        result
    }

    pub fn or(&self, other: Self) -> Self {
        let mut result = Self::default();
        for i in 0..((BITS - 1) >> 3) + 1 {
            result.0[i] = self.0[i] | other.0[i];
        }
        result
    }

    pub fn not(&self) -> Self {
        let mut result = *self;
        for x in &mut result.0 {
            *x = !*x;
        }
        result
    }
}

#[derive(Debug)]
pub struct OutOfBounds {}
impl Error for OutOfBounds {}
impl Display for OutOfBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "out of bounds")
    }
}

macro_rules! u8_roundtrip {
    ($width:expr) => {
        roundtrip!($width, u8, u16);
    };
}

macro_rules! u16_roundtrip {
    ($width:expr) => {
        roundtrip!($width, u16, u32);
    };
}

macro_rules! u32_roundtrip {
    ($width:expr) => {
        roundtrip!($width, u32, u64);
    };
}

macro_rules! u64_roundtrip {
    ($width:expr) => {
        roundtrip!($width, u64, u128);
    };
}

macro_rules! roundtrip {
    ($width:expr, $ty:tt, $overflow_ty:tt) => {
        impl BitSet<$width> {
            pub fn from_int(value: $ty) -> Result<Self, OutOfBounds> {
                if value as $overflow_ty >= (1 << $width) {
                    return Err(OutOfBounds {});
                }
                let v = &value.to_le_bytes()[0..(($width - 1) >> 3) + 1];
                Ok(Self(v.try_into().unwrap()))
            }

            pub fn to_int(&self) -> $ty {
                let mut x = [0u8; ($ty::BITS >> 3) as usize];
                x[0..(($width - 1) >> 3) + 1].copy_from_slice(&self.0);
                $ty::from_le_bytes(x)
            }
        }

        impl TryFrom<$ty> for BitSet<$width> {
            type Error = OutOfBounds;
            fn try_from(value: $ty) -> Result<Self, Self::Error> {
                Self::from_int(value)
            }
        }

        impl std::fmt::Display for BitSet<$width> {
            fn fmt(
                &self,
                f: &mut std::fmt::Formatter<'_>,
            ) -> Result<(), std::fmt::Error> {
                let i = self.to_int();
                write!(f, "{i}/0x{i:x}/0b{i:b}")
            }
        }
    };
}

impl BitSet<1> {
    pub const fn from_bool(value: bool) -> Self {
        Self([value as u8])
    }
    pub const fn to_bool(&self) -> bool {
        self.0[0] == 1
    }
}

seq!(N in 1..=8 { u8_roundtrip!(N); });
seq!(N in 9..=16 { u16_roundtrip!(N); });
seq!(N in 17..=32 { u32_roundtrip!(N); });
seq!(N in 33..=64 { u64_roundtrip!(N); });

#[test]
fn test_roundtrip() {
    let x = BitSet::<1>::from_int(0).unwrap();
    assert_eq!(x.to_int(), 0);

    let x = BitSet::<1>::from_int(1).unwrap();
    assert_eq!(x.to_int(), 1);

    assert!(BitSet::<1>::from_int(2).is_err());

    let x = BitSet::<2>::from_int(2).unwrap();
    assert_eq!(x.to_int(), 2);

    let x = BitSet::<8>::from_int(255).unwrap();
    assert_eq!(x.to_int(), 255);

    let x = BitSet::<9>::from_int(256).unwrap();
    assert_eq!(x.to_int(), 256);

    assert!(BitSet::<9>::from_int(512).is_err());

    let x = BitSet::<17>::from_int(512).unwrap();
    assert_eq!(x.to_int(), 512);

    let x = BitSet::<30>::from_int(474747).unwrap();
    assert_eq!(x.to_int(), 474747);

    let x = BitSet::<33>::from_int(474747).unwrap();
    assert_eq!(x.to_int(), 474747);

    let x = BitSet::<60>::from_int(474747).unwrap();
    assert_eq!(x.to_int(), 474747);

    let x = BitSet::<16>::from_int(0xabcd).unwrap();
    assert_eq!(x.to_int(), 0xabcd);

    let x0 = x.get_field::<8, 0>().unwrap();
    let x1 = x.get_field::<2, 8>().unwrap();

    assert_eq!(x0.to_int(), 0xcd);
    assert_eq!(x1.to_int(), 0x3);
}

#[test]
fn test_shr() {
    let mut i = u64::MAX;
    let mut x = BitSet::<64>::from_int(i).unwrap();
    for s in 0..64 {
        for p in 0..64 {
            i >>= s;
            x = x.shr(s);
            assert_eq!(
                i,
                x.to_int(),
                "shr position={p} shift={s}\n{i:064b}\n{:064b}",
                x.to_int()
            );
        }
    }
}

#[test]
fn test_shl() {
    let mut i = u64::MAX;
    let mut x = BitSet::<64>::from_int(i).unwrap();
    for s in 0..64 {
        for p in 0..64 {
            i <<= s;
            x = x.shl(s);
            assert_eq!(
                i,
                x.to_int(),
                "shl position={p} shift={s}\n{i:064b}\n{:064b}",
                x.to_int()
            );
        }
    }
}

#[test]
fn test_and() {
    let a = 1u64;
    let b = 1u64;
    let x = BitSet::<64>::from_int(1u64).unwrap();
    let y = BitSet::<64>::from_int(1u64).unwrap();

    for i in 0..64 {
        for j in 0..64 {
            let c = (a << i) & (b << j);
            let z = (x.shl(i)).and(y.shl(j));
            assert_eq!(c, z.to_int(), "and position ({i}, {j})");
        }
    }

    let x = BitSet::<64>::from_int(u64::MAX).unwrap();
    let y = BitSet::<64>::default();
    let z = x.and(y);
    assert_eq!(y, z);
}

#[test]
fn test_or() {
    let a = 1u64;
    let b = 1u64;
    let x = BitSet::<64>::from_int(1u64).unwrap();
    let y = BitSet::<64>::from_int(1u64).unwrap();

    for i in 0..64 {
        for j in 0..64 {
            let c = (a << i) | (b << j);
            let z = (x.shl(i)).or(y.shl(j));
            assert_eq!(c, z.to_int(), "or position ({i}, {j})");
        }
    }

    let x = BitSet::<64>::from_int(u64::MAX).unwrap();
    let y = BitSet::<64>::default();
    let z = x.or(y);
    assert_eq!(x, z);
}

#[test]
fn test_max() {
    seq!(I in 1..=7 {{
        let a = (1u8 << (I)) - 1;
        let b = BitSet::<I>::max().unwrap();
        assert_eq!(a, b.to_int(), "max count={}", I);
    }});
    let a = u8::MAX;
    let b = BitSet::<8>::max().unwrap();
    assert_eq!(a, b.to_int(), "max count={}", 8);

    seq!(I in 9..=15 {{
        let a = (1u16 << (I)) - 1;
        let b = BitSet::<I>::max().unwrap();
        assert_eq!(a, b.to_int(), "max count={}", I);
    }});
    let a = u16::MAX;
    let b = BitSet::<16>::max().unwrap();
    assert_eq!(a, b.to_int(), "max count={}", 16);

    seq!(I in 17..=31 {{
        let a = (1u32 << (I)) - 1;
        let b = BitSet::<I>::max().unwrap();
        assert_eq!(a, b.to_int(), "max count={}", I);
    }});
    let a = u32::MAX;
    let b = BitSet::<32>::max().unwrap();
    assert_eq!(a, b.to_int(), "max count={}", 32);

    seq!(I in 33..=63 {{
        let a = (1u64 << (I)) - 1;
        let b = BitSet::<I>::max().unwrap();
        assert_eq!(a, b.to_int(), "max count={}", I);
    }});
    let a = u64::MAX;
    let b = BitSet::<64>::max().unwrap();
    assert_eq!(a, b.to_int(), "max count={}", 64);
}

#[test]
fn test_extend_right() {
    let x = BitSet::<47>::max().unwrap();
    let y = x.extend_right::<5>();
    let z = BitSet::<52>::from_int((1u64 << 47) - 1).unwrap();
    assert_eq!(y, z);
}

#[test]
fn test_extend_left() {
    let x = BitSet::<47>::max().unwrap();
    let y = x.extend_left::<5>();
    let z = BitSet::<52>::from_int(((1u64 << 47) - 1) >> 5).unwrap();
    assert_eq!(y, z);
}

#[test]
fn test_not() {
    let a =
        0b1010101010101010101010101010101010101010101010101010101010101010u64;
    let b = !a;

    let x = BitSet::<64>::from_int(a).unwrap();
    let y = x.not();

    assert_eq!(y.to_int(), b);
}

#[test]
fn test_set_field() {
    let a =
        0b1111111100000000111111110000000011111111000000001111111100000000u64;
    let x = BitSet::<64>::from_int(a).unwrap();

    let b = 0b10101010u8;
    let y = BitSet::<8>::from_int(b).unwrap();

    let mut z = x;
    z.set_field::<8, 0>(y).unwrap();
    let expected =
        0b1111111100000000111111110000000011111111000000001111111110101010u64;

    assert_eq!(
        z.to_int(),
        expected,
        "\n{:064b}\n{:064b}",
        z.to_int(),
        expected,
    );

    let mut z = x;
    z.set_field::<8, 48>(y).unwrap();
    let expected =
        0b1111111110101010111111110000000011111111000000001111111100000000u64;

    assert_eq!(
        z.to_int(),
        expected,
        "\n{:064b}\n{:064b}",
        z.to_int(),
        expected,
    );
}

#[test]
fn readme_example() {
    // Create a bitset of width 8, with three fields a, b and c.
    let mut x = BitSet::<8>::from_int(0b1_0101_111).unwrap();
    //                                  ^    ^   ^
    //                                  c    b   a

    // Extract individual fields. Note that the extracted field is statically
    // typed according to width.
    let a: BitSet<3> = x.get_field::<3, 0>().unwrap();
    let b: BitSet<4> = x.get_field::<4, 3>().unwrap();
    let c: BitSet<1> = x.get_field::<1, 7>().unwrap();
    assert_eq!(a.to_int(), 0b111);
    assert_eq!(b.to_int(), 0b0101);
    assert_eq!(c.to_int(), 0b1);

    // Now set a feild. Note that setting a field requires a bitset with the
    // correct width.
    let b = BitSet::<4>::from_int(0b1010).unwrap();
    x.set_field::<4, 3>(b).unwrap();
    assert_eq!(a.to_int(), 0b111);
    assert_eq!(b.to_int(), 0b1010);
    assert_eq!(c.to_int(), 0b1);
    assert_eq!(x.to_int(), 0b1_1010_111);
}
