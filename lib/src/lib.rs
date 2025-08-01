// Copyright Oxide Computer Company 2025
#![no_std]
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]
#![allow(clippy::unusual_byte_groupings)]

extern crate alloc;

use alloc::vec::Vec;
use core::error::Error;
use core::fmt::Display;
use seq_macro::seq;

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

impl<const BITS: usize> core::fmt::LowerHex for BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> Result<(), core::fmt::Error> {
        write!(f, "{:x?}", self.0)
    }
}

impl<const BITS: usize> core::fmt::UpperHex for BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> Result<(), core::fmt::Error> {
        write!(f, "{:X?}", self.0)
    }
}

impl BitSet<1> {
    pub const TRUE: Self = Self([1u8]);
    pub const FALSE: Self = Self([0u8]);
}

impl<const BITS: usize> TryFrom<&Vec<u8>> for BitSet<BITS>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    type Error = OutOfBounds;
    fn try_from(value: &Vec<u8>) -> Result<Self, Self::Error> {
        let mut s = Self::ZERO;

        if value.len() > ((BITS - 1) >> 3) + 1 {
            Err(OutOfBounds {})
        } else {
            s.0[..value.len()].copy_from_slice(value);
            Ok(s)
        }
    }
}

impl<const BITS: usize> From<&BitSet<BITS>> for Vec<u8>
where
    [(); ((BITS - 1) >> 3) + 1]:,
{
    fn from(value: &BitSet<BITS>) -> Self {
        value.0.to_vec()
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
    pub const WIDTH: usize = BITS;

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
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "out of bounds")
    }
}

macro_rules! matching_int_bitset {
    ($width:expr, $ty:tt) => {
        impl From<$ty> for BitSet<$width> {
            fn from(value: $ty) -> Self {
                let data = value.to_le_bytes();
                Self(data.try_into().unwrap())
            }
        }

        impl From<BitSet<$width>> for $ty {
            fn from(value: BitSet<$width>) -> Self {
                $ty::from_le_bytes(value.0)
            }
        }
    };
}

macro_rules! small_int_large_bitset {
    ($width:expr, $ty:tt) => {
        impl From<$ty> for BitSet<$width> {
            fn from(value: $ty) -> Self {
                const BYTES: usize = (($width - 1) >> 3) + 1;
                let data = value.to_le_bytes();
                let mut padded = [0u8; BYTES];
                padded[0..data.len()].copy_from_slice(&data);
                Self(padded.try_into().unwrap())
            }
        }

        impl TryFrom<BitSet<$width>> for $ty {
            type Error = OutOfBounds;
            fn try_from(value: BitSet<$width>) -> Result<Self, Self::Error> {
                const BYTES: usize = (($width - 1) >> 3) + 1;
                let mut padded = [0u8; 16];
                padded[0..BYTES].copy_from_slice(&value.0);
                let tmp = u128::from_le_bytes(padded);
                if tmp > $ty::MAX as u128 {
                    Err(OutOfBounds {})
                } else {
                    Ok(tmp as $ty)
                }
            }
        }
    };
}

macro_rules! large_int_small_bitset {
    ($width:expr, $ty:tt) => {
        impl TryFrom<$ty> for BitSet<$width> {
            type Error = OutOfBounds;
            fn try_from(value: $ty) -> Result<Self, Self::Error> {
                let max = (1 << $width) - 1;
                if value > max {
                    Err(OutOfBounds {})
                } else {
                    const BYTES: usize = (($width - 1) >> 3) + 1;
                    let data = value.to_le_bytes();
                    Ok(Self(data[0..BYTES].try_into().unwrap()))
                }
            }
        }

        impl From<BitSet<$width>> for $ty {
            fn from(value: BitSet<$width>) -> Self {
                const BYTES: usize = (($width - 1) >> 3) + 1;
                let mut padded = [0u8; 8];
                padded[0..BYTES].copy_from_slice(&value.0);
                let tmp = u64::from_le_bytes(padded);
                $ty::try_from(tmp).unwrap()
            }
        }
    };
}

macro_rules! display {
    ($width:expr) => {
        impl core::fmt::Display for BitSet<$width> {
            fn fmt(
                &self,
                f: &mut core::fmt::Formatter<'_>,
            ) -> Result<(), core::fmt::Error> {
                let i = u64::from(*self);
                write!(f, "{i}/0x{i:x}/0b{i:b}")
            }
        }
    };
}

impl From<BitSet<1>> for bool {
    fn from(value: BitSet<1>) -> Self {
        value.0[0] == 1
    }
}

impl From<bool> for BitSet<1> {
    fn from(value: bool) -> Self {
        Self([value as u8])
    }
}

// Build From functions for integers and BitSets that are of matching sizes
matching_int_bitset!(8, u8);
matching_int_bitset!(16, u16);
matching_int_bitset!(32, u32);
matching_int_bitset!(64, u64);

// Build From functions that allow integers to be converted to larger BitSets,
// and TryFrom functions allow larger BitSets to attempt to squeeze into smaller
// integers.
seq!(N in 9..=64 { small_int_large_bitset!(N, u8); });
seq!(N in 17..=64 { small_int_large_bitset!(N, u16); });
seq!(N in 33..=64 { small_int_large_bitset!(N, u32); });

// Build From functions that allow smaller BitSets to be exported to larger
// integers  and TryFrom functions that attempt to squeeze larger integers into
// smaller BitSets.
seq!(N in 1..=7 { large_int_small_bitset!(N, u8); });
seq!(N in 1..=15 { large_int_small_bitset!(N, u16); });
seq!(N in 1..=31 { large_int_small_bitset!(N, u32); });
seq!(N in 1..=63 { large_int_small_bitset!(N, u64); });

// Implement fmt::std::Display for all BitSet sizes up to 64
seq!(N in 1..=64 { display!(N); });

#[cfg(test)]
mod test {
    use super::*;
    use alloc::vec;
    use bitset_macro::bitset;

    #[test]
    // Test conversions when the integer type is capable of handling larger
    // numbers than the BitSet.
    fn test_large_int() {
        let x = bitset!(4, 7);
        assert_eq!(u8::from(x), 7);
        let y: u8 = x.into();
        assert_eq!(y, 7u8);

        let x = bitset!(4, 7);
        assert_eq!(u16::from(x), 7);
        let y: u16 = x.into();
        assert_eq!(y, 7);

        let x = bitset!(12, 1111);
        assert_eq!(u16::from(x), 1111);
        let y: u16 = x.into();
        assert_eq!(y, 1111);

        let x = bitset!(24, 0x123456);
        assert_eq!(u32::from(x), 0x123456);
        let y: u32 = x.into();
        assert_eq!(y, 0x123456);

        let x = bitset!(33, 0x12345678);
        assert_eq!(u64::from(x), 0x12345678);
        let y: u64 = x.into();
        assert_eq!(y, 0x12345678);

        let x = BitSet::<4>::try_from(7u8).unwrap();
        assert_eq!(x, bitset!(4, 7));

        let x = BitSet::<4>::try_from(7u16).unwrap();
        assert_eq!(x, bitset!(4, 7));

        let x = BitSet::<12>::try_from(1111u16).unwrap();
        assert_eq!(x, bitset!(12, 1111));

        let x = BitSet::<24>::try_from(0x123456u32).unwrap();
        assert_eq!(x, bitset!(24, 0x123456));

        let x = BitSet::<33>::try_from(0x12345678u64).unwrap();
        assert_eq!(x, bitset!(33, 0x12345678));

        assert!(BitSet::<4>::try_from(0x123u16).is_err());
        assert!(BitSet::<12>::try_from(0x1234u32).is_err());
        assert!(BitSet::<24>::try_from(0x1234567u32).is_err());
        assert!(BitSet::<33>::try_from(0x123456789abu64).is_err());
    }

    #[test]
    // Test conversions when the BitSet type is capable of handling larger
    // numbers than the integer type.
    fn test_small_int() {
        let x = bitset!(9, 7);
        assert_eq!(u8::try_from(x).unwrap(), 7);

        let x = bitset!(19, 0x1234);
        assert_eq!(u16::try_from(x).unwrap(), 0x1234);
        assert!(u8::try_from(x).is_err());

        let x = bitset!(33, 0x1234567);
        assert_eq!(u32::try_from(x).unwrap(), 0x1234567);
        assert!(u16::try_from(x).is_err());

        let x = bitset!(33, 0x1234567);
        assert_eq!(u32::try_from(x).unwrap(), 0x1234567);
        assert!(u16::try_from(x).is_err());

        let x = BitSet::<32>::from(0x1234u16);
        assert_eq!(x, bitset!(32, 0x1234));
    }

    #[test]
    fn test_shr() {
        let mut i = u64::MAX;
        let mut x = BitSet::<64>::from(i);
        for s in 0..64 {
            for p in 0..64 {
                i >>= s;
                x = x.shr(s);
                assert_eq!(
                    i,
                    u64::from(x),
                    "shr position={p} shift={s}\n{i:064b}\n{:064b}",
                    u64::from(x)
                );
            }
        }
    }

    #[test]
    fn test_shl() {
        let mut i = u64::MAX;
        let mut x = BitSet::<64>::from(i);
        for s in 0..64 {
            for p in 0..64 {
                i <<= s;
                x = x.shl(s);
                assert_eq!(
                    i,
                    u64::from(x),
                    "shl position={p} shift={s}\n{i:064b}\n{:064b}",
                    u64::from(x)
                );
            }
        }
    }

    #[test]
    fn test_and() {
        let a = 1u64;
        let b = 1u64;
        let x = bitset!(64, 1);
        let y = bitset!(64, 1);

        for i in 0..64 {
            for j in 0..64 {
                let c = (a << i) & (b << j);
                let z = (x.shl(i)).and(y.shl(j));
                assert_eq!(c, u64::from(z), "and position ({i}, {j})");
            }
        }

        let x = BitSet::<64>::from(u64::MAX);
        let y = BitSet::<64>::default();
        let z = x.and(y);
        assert_eq!(y, z);
    }

    #[test]
    fn test_or() {
        let a = 1u64;
        let b = 1u64;
        let x = bitset!(64, 1);
        let y = bitset!(64, 1);

        for i in 0..64 {
            for j in 0..64 {
                let c = (a << i) | (b << j);
                let z = (x.shl(i)).or(y.shl(j));
                assert_eq!(c, u64::from(z), "or position ({i}, {j})");
            }
        }

        let x = BitSet::<64>::from(u64::MAX);
        let y = BitSet::<64>::default();
        let z = x.or(y);
        assert_eq!(x, z);
    }

    #[test]
    fn test_max() {
        seq!(I in 1..=7 {{
            let a = (1u8 << (I)) - 1;
            let b = BitSet::<I>::max().unwrap();
            assert_eq!(a, u8::from(b), "max count={}", I);
        }});
        let a = u8::MAX;
        let b = BitSet::<8>::max().unwrap();
        assert_eq!(a, u8::from(b), "max count={}", 8);

        seq!(I in 9..=15 {{
            let a = (1u16 << (I)) - 1;
            let b = BitSet::<I>::max().unwrap();
            assert_eq!(a, u16::from(b), "max count={}", I);
        }});
        let a = u16::MAX;
        let b = BitSet::<16>::max().unwrap();
        assert_eq!(a, u16::from(b), "max count={}", 16);

        seq!(I in 17..=31 {{
            let a = (1u32 << (I)) - 1;
            let b = BitSet::<I>::max().unwrap();
            assert_eq!(a, u32::from(b), "max count={}", I);
        }});
        let a = u32::MAX;
        let b = BitSet::<32>::max().unwrap();
        assert_eq!(a, u32::from(b), "max count={}", 32);

        seq!(I in 33..=63 {{
            let a = (1u64 << (I)) - 1;
            let b = BitSet::<I>::max().unwrap();
            assert_eq!(a, u64::from(b), "max count={}", I);
        }});
        let a = u64::MAX;
        let b = BitSet::<64>::max().unwrap();
        assert_eq!(a, u64::from(b), "max count={}", 64);
    }

    #[test]
    fn test_extend_right() {
        let x = BitSet::<47>::max().unwrap();
        let y = x.extend_right::<5>();
        let z = BitSet::<52>::try_from((1u64 << 47) - 1).unwrap();
        assert_eq!(y, z);
    }

    #[test]
    fn test_extend_left() {
        let x = BitSet::<47>::max().unwrap();
        let y = x.extend_left::<5>();
        let z = BitSet::<52>::try_from(((1u64 << 47) - 1) >> 5).unwrap();
        assert_eq!(y, z);
    }

    #[test]
    fn test_not() {
        let a =
        0b1010101010101010101010101010101010101010101010101010101010101010u64;
        let b = !a;

        let x = BitSet::<64>::from(a);
        let y = x.not();

        assert_eq!(u64::from(y), b);
    }

    #[test]
    fn test_to_bytes() {
        let a =
        0b1010101010101010101010101010101010101010101010101010101010101010u64;

        let x = BitSet::<64>::from(a);
        let y = Vec::<u8>::from(&x);

        assert_eq!(y, [0xaa; 8]);
    }

    #[test]
    fn test_try_from_bytes() {
        let bytes = vec![0x01u8, 0x23, 0x45, 0x67, 0x89, 0xab];
        let x = BitSet::<48>::try_from(&bytes).unwrap();
        let y = BitSet::<48>::try_from(0xab8967452301u64).unwrap();
        assert_eq!(x, y);

        let x = BitSet::<64>::try_from(&bytes).unwrap();
        let y = BitSet::<64>::from(0xab8967452301u64);
        assert_eq!(x, y);

        assert!(BitSet::<32>::try_from(&bytes).is_err());

        let long = vec![0xaa; 64];
        let x = BitSet::<512>::try_from(&long).unwrap();
        let y = Vec::<u8>::from(&x);
        assert_eq!(long, y);
    }

    #[test]
    fn test_set_field() {
        let a =
        0b1111111100000000111111110000000011111111000000001111111100000000u64;
        let x = BitSet::<64>::from(a);

        let b = 0b10101010u8;
        let y = BitSet::<8>::from(b);

        let mut z = x;
        z.set_field::<8, 0>(y).unwrap();
        let expected =
        0b1111111100000000111111110000000011111111000000001111111110101010u64;

        assert_eq!(
            u64::from(z),
            expected,
            "\n{:064b}\n{:064b}",
            u64::from(z),
            expected,
        );

        let mut z = x;
        z.set_field::<8, 48>(y).unwrap();
        let expected =
        0b1111111110101010111111110000000011111111000000001111111100000000u64;

        assert_eq!(
            u64::from(z),
            expected,
            "\n{:064b}\n{:064b}",
            u64::from(z),
            expected,
        );
    }

    #[test]
    fn readme_example() {
        // Create a bitset of width 8, with three fields a, b and c.
        let mut x = bitset!(8, 0b1_0101_111);
        //                       ^    ^   ^
        //                       c    b   a

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
        let b = bitset!(4, 0b1010);
        x.set_field::<4, 3>(b).unwrap();
        assert_eq!(u8::from(a), 0b111);
        assert_eq!(u8::from(b), 0b1010);
        assert_eq!(u8::from(c), 0b1);
        assert_eq!(u8::from(x), 0b1_1010_111);
    }

    #[test]
    fn macro_test() {
        let a = bitset!(47, 0x1701);
        let b = BitSet::<47>::from(0x1701u16);

        assert_eq!(a, b);
    }
}

pub mod legacy {
    use super::*;
    #[cfg(test)]
    use bitset_macro::bitset;

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
        };
    }

    seq!(N in 1..=8 { u8_roundtrip!(N); });
    seq!(N in 9..=16 { u16_roundtrip!(N); });
    seq!(N in 17..=32 { u32_roundtrip!(N); });
    seq!(N in 33..=64 { u64_roundtrip!(N); });

    #[test]
    fn test_roundtrip() {
        let x = bitset!(1, 0);
        assert_eq!(x.to_int(), 0);

        let x = bitset!(1, 1);
        assert_eq!(x.to_int(), 1);

        assert!(BitSet::<1>::from_int(2).is_err());

        let x = bitset!(2, 2);
        assert_eq!(x.to_int(), 2);

        let x = bitset!(8, 255);
        assert_eq!(x.to_int(), 255);

        let x = bitset!(9, 256);
        assert_eq!(x.to_int(), 256);

        assert!(BitSet::<9>::from_int(512).is_err());

        let x = bitset!(17, 512);
        assert_eq!(x.to_int(), 512);

        let x = bitset!(30, 474747);
        assert_eq!(x.to_int(), 474747);

        let x = bitset!(33, 474747);
        assert_eq!(x.to_int(), 474747);

        let x = bitset!(60, 474747);
        assert_eq!(x.to_int(), 474747);

        let x = bitset!(16, 0xabcd);
        assert_eq!(x.to_int(), 0xabcd);

        let x0 = x.get_field::<8, 0>().unwrap();
        let x1 = x.get_field::<2, 8>().unwrap();

        assert_eq!(x0.to_int(), 0xcd);
        assert_eq!(x1.to_int(), 0x3);
    }
}
