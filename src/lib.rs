use std::fmt::Debug;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOrAssign, BitXorAssign, Not, Shl, Shr};

/// The operations a storage type needs to support for use with [BitStore]
pub trait BitStoreBaseOps:
    Sized
    + Default
    + Ones
    + Add<Output = Self>
    + AddAssign
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + Not<Output = Self>
    + Shl<Output = Self>
    + Shr<Output = Self>
    + PartialEq
{
}

/// Returns an object with all bits set to one
pub trait Ones: Shr<Output = Self> + Sized {
    fn all_ones() -> Self;

    fn one() -> Self;
}

/// Implementation assumes T has at most 256 bits
///
///
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct BitStore<T: Sized, const BITS: u8>(T);

impl<T, const BITS: u8> BitStore<T, BITS>
where
    T: BitStoreBaseOps + Clone + From<u8>,
{
    pub fn new() -> BitStore<T, BITS> {
        BitStore(T::default())
    }

    /// Gets the value stored in the index position
    ///
    /// The value is shifted to the least significant bit
    pub fn get(&self, index: u8) -> T {
        let mask = Self::mask(index);
        (self.0.clone() & mask) >> T::from(index * BITS)
    }

    /// Assumes value uses the lowest BITS.
    ///
    /// Applies mask to input value to prevent the other bits from being polluted
    pub fn set(&mut self, index: u8, value: T) {
        let masked_value = (value & Self::mask(0)) << T::from(index * BITS);
        self.clear(index);
        self.0 |= masked_value;
    }

    /// Toggles all of the bits in the index
    pub fn toggle(&mut self, index: u8) {
        let mask = Self::mask(index);
        self.0 ^= mask;
    }

    /// Sets all the bits to zero in the index position
    pub fn clear(&mut self, index: u8) {
        let mask = !Self::mask(index);
        self.0 &= mask;
    }

    /// Increments the position by one
    ///
    /// Returns the new value at index t
    ///
    /// Overflows do not result in a state change
    pub fn increment(&mut self, index: u8) -> Option<T> {
        let mut value = self.get(index);
        value += T::one();
        let masked_value = value.clone() & Self::mask(index);

        if masked_value != value {
            return None;
        }

        self.set(index, value);
        Some(masked_value)
    }

    /// Increments the position by one
    ///
    /// Overflows will pollute the next index
    pub fn increment_unchecked(&mut self, index: u8) {
        self.0 += T::one() << T::from(index * BITS);
    }

    /// Generates the mask to interact with the bucket
    fn mask(index: u8) -> T {
        let size_of_t = 8 * std::mem::size_of::<T>() as u8;
        (T::all_ones() >> T::from(size_of_t - BITS)) << T::from(index * BITS)
    }
}

impl<T: Add<Output = T>, const BITS: u8> Add for BitStore<T, BITS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl<T: AddAssign, const BITS: u8> AddAssign for BitStore<T, BITS> {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl BitStoreBaseOps for u8 {}
impl BitStoreBaseOps for u16 {}
impl BitStoreBaseOps for u32 {}
impl BitStoreBaseOps for u64 {}

macro_rules! uints_for_bitstore {
   ( $($t: ty), *) => {
        $(impl Ones for $t {
            fn all_ones() -> Self {
                Self::MAX
            }

            fn one() -> Self {
                1
            }
        })*
    }
}

uints_for_bitstore! { u8, u16, u32, u64 }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let bits = BitStore::<u32, 5>::new();
    }

    #[test]
    fn increment() {
        let mut bits = BitStore::<u8, 1>::new();
        bits.increment(0);
        assert_eq!(bits.0, 1);
        bits.increment(7);
        assert_eq!(bits.0, 129);
    }

    #[test]
    fn sets() {
        let mut bits = BitStore::<u16, 3>::new();
        bits.set(0, 1);
        assert_eq!(bits.get(0), 1);
        bits.set(0, 2);
        assert_eq!(bits.get(0), 2);
        bits.set(4, 15);
        // Max value for 3 bits
        assert_eq!(bits.get(4), 7);
    }

    #[test]
    fn increment_and_read() {
        let mut bits = BitStore::<u8, 2>::new();

        bits.increment(3);
        bits.increment(3);
        bits.increment(3);
        // Shouldn't affect value read out
        bits.increment(2);
        bits.increment(1);
        bits.increment(0);

        let pos_three_val = bits.get(3);
        assert_eq!(pos_three_val, 3);
    }

    #[test]
    fn increment_and_clear() {
        let mut bits = BitStore::<u8, 2>::new();

        bits.increment(3);
        bits.increment(3);
        bits.increment(3);
        // Shouldn't affect value read out
        bits.increment(2);
        bits.increment(1);
        bits.increment(0);

        let pos_three_val = bits.get(3);
        assert_eq!(pos_three_val, 3);
        bits.clear(3);
        assert_eq!(bits.get(3), 0);
        assert_eq!(bits.get(2), 1);
        assert_eq!(bits.get(1), 1);
        assert_eq!(bits.get(0), 1);
        bits.clear(0);
        assert_eq!(bits.get(3), 0);
        assert_eq!(bits.get(2), 1);
        assert_eq!(bits.get(1), 1);
        assert_eq!(bits.get(0), 0);
    }

    #[test]
    fn add() {
        let bits_1 = BitStore::<u32, 5>::new();
        let bits_2 = BitStore::<u32, 5>::new();
        let bits_3 = bits_1.clone() + bits_2.clone();
        assert_eq!(bits_3, bits_1);
        assert_eq!(bits_3, bits_2);
    }
}
