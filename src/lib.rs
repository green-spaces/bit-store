use std::fmt::Debug;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOrAssign, Not, Shl, Shr};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct BitStore<T: Sized, const BITS: usize>(T);

impl<T: Default, const BITS: usize> BitStore<T, BITS> {
    pub fn new() -> BitStore<T, BITS> {
        BitStore(T::default())
    }
}

impl<T, const BITS: usize> BitStore<T, BITS>
where
    T: Shl<Output = T> + TryFrom<usize> + AddAssign,
    <T as TryFrom<usize>>::Error: Debug,
{
    pub fn increment(&mut self, index: usize) {
        self.0 += T::try_from(1_usize << index * BITS).expect("index * BITS exceeded sizeof<T>");
    }
}

impl<T, const BITS: usize> BitStore<T, BITS>
where
    T: Shl<Output = T> + Shr<Output = T> + BitAnd<Output = T> + Copy,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    /// Gets the value stored in the index position
    ///
    /// The value is shifted to the least significant bit
    pub fn get(&self, index: usize) -> T {
        let mask = Self::mask(index);
        (self.0 & mask) >> T::try_from(index * BITS).unwrap()
    }

    pub fn toggle(&mut self, index: usize) {
        todo!()
    }
}

impl<T, const BITS: usize> BitStore<T, BITS>
where
    T: Shl<Output = T>
        + Shr<Output = T>
        + BitAnd<Output = T>
        + Not<Output = T>
        + BitOrAssign
        + BitAndAssign
        + Copy,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    /// Assumes value uses the lowest BITS.
    ///
    /// Applies mask to input value to prevent the other bits from being polluted
    pub fn set(&mut self, index: usize, value: T) {
        let maked_value = (value & Self::mask(0)) << T::try_from(index * BITS).unwrap();
        self.clear(index);
        self.0 |= maked_value;
    }
}

impl<T, const BITS: usize> BitStore<T, BITS>
where
    T: BitAndAssign + Not<Output = T>,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    pub fn clear(&mut self, index: usize) {
        let mask = !Self::mask(index);
        self.0 &= mask;
    }
}

impl<T, const BITS: usize> BitStore<T, BITS>
where
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    fn mask(index: usize) -> T {
        T::try_from((usize::MAX >> (64 - BITS)) << index * BITS).unwrap()
    }
}

impl<T: Add<Output = T>, const BITS: usize> Add for BitStore<T, BITS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl<T: AddAssign, const BITS: usize> AddAssign for BitStore<T, BITS> {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

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
