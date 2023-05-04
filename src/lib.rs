#![doc = include_str!("../README.md")]
#![no_std]
#![forbid(unsafe_code)]
#![warn(missing_docs, clippy::pedantic)]

extern crate alloc;

/// An ordered collection of values, accessible by [`LotId`] or index.
pub mod ordered;
/// An unordered collection of values, accessible by [`LotId`].
pub mod unordered;

use core::fmt::{Debug, Write};
use core::num::{NonZeroU16, NonZeroUsize};

pub use ordered::OrderedLots;
pub use unordered::Lots;

/// A `LotId` is a single `usize`, encoding generation information in the top
/// 1/4 of the bits, and index information in the remaining bits. This table
/// shows the breakdown for supported target platforms:
///
/// | `target_pointer_width` | generation bits | index bits |
/// |------------------------|-----------------|------------|
/// | 16                     | 4               | 12         |
/// | 32                     | 8               | 24         |
/// | 64                     | 16              | 48         |
///
/// Each time a lot is allocated, its generation is incremented. When retrieving
/// values using a `LotId`, the generation is validated as a safe guard against
/// returning a value. Because the generation isn't significantly wide, the
/// generation can wrap and is not a perfect protection against stale data,
/// although the likelihood of improper access is greatly reduced.
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct LotId(NonZeroUsize);

impl Debug for LotId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("LotId(")?;
        self.index().fmt(f)?;
        f.write_char('g')?;
        self.generation().fmt(f)?;
        f.write_char(')')
    }
}

#[test]
fn lot_id_debug() {
    let lot = LotId::new(Generation::first(), 0).unwrap();
    assert_eq!(alloc::format!("{lot:?}"), "LotId(0g1)");
}

#[cfg(not(any(
    target_pointer_width = "16",
    target_pointer_width = "32",
    target_pointer_width = "64"
)))]
compile_error!("LotId currently only supports 16, 32 and 64 bit architectures.");

impl LotId {
    #[allow(clippy::cast_possible_truncation)]
    const GENERATION_MAX: u16 = (usize::MAX >> Self::INDEX_BITS) as u16;
    const INDEX_BITS: u32 = usize::BITS / 4 * 3;
    const INDEX_MASK: usize = 2_usize.pow(Self::INDEX_BITS) - 1;

    #[cfg_attr(target_pointer_width = "64", allow(clippy::absurd_extreme_comparisons))]
    #[inline]
    fn new(generation: Generation, index: usize) -> Option<Self> {
        if index <= Self::INDEX_MASK && generation.get() <= Self::GENERATION_MAX {
            Some(Self(
                NonZeroUsize::new((generation.0.get() as usize) << Self::INDEX_BITS | index)
                    .expect("generation is non-zero"),
            ))
        } else {
            None
        }
    }

    #[inline]
    #[must_use]
    const fn index(self) -> usize {
        self.0.get() & Self::INDEX_MASK
    }

    #[inline]
    #[must_use]
    #[allow(clippy::cast_possible_truncation)]
    fn generation(self) -> Generation {
        Generation(
            NonZeroU16::new((self.0.get() >> Self::INDEX_BITS) as u16).expect("invalid Lot id"),
        )
    }

    /// Returns this ID as bytes. To decode the resulting bytes, use
    /// [`from_bytes()`](Self::from_bytes).
    ///
    /// The result of this fuction changes size based on the width of `usize`.
    #[must_use]
    pub const fn as_bytes(self) -> [u8; (usize::BITS / 8) as usize] {
        self.0.get().to_be_bytes()
    }

    /// Decodes `bytes` that were previously encoded with
    /// [`as_bytes()`](Self::as_bytes) and returns a `LotId` if it appears to be
    /// a valid ID.
    ///
    /// This function will "upgrade" previously encoded `LotId`s from
    /// architectures where `usize` is smaller than the current architecture.
    #[must_use]
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let usize = match bytes.try_into() {
            Ok(bytes) => usize::from_be_bytes(bytes),
            Err(_) => match bytes.len() {
                2 if usize::BITS >= 16 => expand_from_shorter::<16>(u16::from_be_bytes(
                    bytes.try_into().expect("u16 is 2 bytes"),
                ) as usize),
                4 if usize::BITS >= 32 => expand_from_shorter::<32>(u32::from_be_bytes(
                    bytes.try_into().expect("u32 is 4 bytes"),
                ) as usize),
                _ => return None,
            },
        };
        #[allow(clippy::cast_possible_truncation)]
        let _generation = NonZeroU16::new((usize >> Self::INDEX_BITS) as u16)?;
        Some(Self(NonZeroUsize::new(usize).expect("generation checked")))
    }
}

#[inline]
fn expand_from_shorter<const BITS: usize>(value: usize) -> usize {
    let index_bits = BITS / 4 * 3;
    let generation = value >> index_bits;
    let index = value & ((1 << index_bits) - 1);

    (generation << LotId::INDEX_BITS) | index
}

#[test]
fn invalid_ids() {
    assert!(LotId::new(Generation::first(), usize::MAX).is_none());
}

#[test]
fn lot_id_bytes() {
    let decoded =
        LotId::from_bytes(&LotId::new(Generation::first(), 2).unwrap().as_bytes()).unwrap();
    assert_eq!(decoded.generation().get(), 1);
    assert_eq!(decoded.index(), 2);

    let expanded = LotId::from_bytes(&0xF001_u16.to_be_bytes()).unwrap();
    assert_eq!(expanded.generation().get(), 15);
    assert_eq!(expanded.index(), 1);
    let expanded = LotId::from_bytes(&0xFF00_0001_u32.to_be_bytes()).unwrap();
    assert_eq!(expanded.generation().get(), 255);
    assert_eq!(expanded.index(), 1);

    assert_eq!(LotId::from_bytes(&[]), None);
    assert_eq!(LotId::from_bytes(&[0; (usize::BITS / 8) as usize]), None);
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct Generation(NonZeroU16);

impl Generation {
    #[cfg(test)]
    const MAX: Self = Self(match NonZeroU16::new(LotId::GENERATION_MAX) {
        Some(nz) => nz,
        None => unreachable!(),
    });

    #[inline]
    #[must_use]
    pub const fn first() -> Self {
        Self(match NonZeroU16::new(1) {
            Some(one) => one,
            None => unreachable!(),
        })
    }

    #[inline]
    #[must_use]
    #[cfg_attr(target_pointer_width = "64", allow(clippy::absurd_extreme_comparisons))]
    pub const fn next(self) -> Self {
        match self.0.checked_add(1) {
            Some(next) if next.get() <= LotId::GENERATION_MAX => Self(next),
            _ => Self::first(),
        }
    }

    #[inline]
    #[must_use]
    pub const fn get(self) -> u16 {
        self.0.get()
    }
}

impl Debug for Generation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

#[test]
fn generation_wrapping() {
    let max = Generation::MAX;
    assert_eq!(max.next(), Generation::first());
}
