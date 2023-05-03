#![doc = include_str!("../README.md")]
#![no_std]
#![forbid(unsafe_code)]

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
/// 1/4 of the bits, and index information in the remaining bits. When compiling
/// for a 64-bit platform, this equates to:
///
/// - u16: generation
/// - u48: lot index
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
    pub const fn index(self) -> usize {
        self.0.get() & Self::INDEX_MASK
    }

    #[inline]
    pub fn generation(self) -> Generation {
        Generation(
            NonZeroU16::new((self.0.get() >> Self::INDEX_BITS) as u16).expect("invalid Lot id"),
        )
    }
}

#[test]
fn invalid_ids() {
    assert!(LotId::new(Generation::first(), usize::MAX).is_none());
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct Generation(NonZeroU16);

impl Generation {
    #[cfg(test)]
    const MAX: Self = Self(match NonZeroU16::new(LotId::GENERATION_MAX) {
        Some(nz) => nz,
        None => unreachable!(),
    });

    #[inline]
    pub const fn first() -> Self {
        Self(match NonZeroU16::new(1) {
            Some(one) => one,
            None => unreachable!(),
        })
    }

    #[inline]
    #[cfg_attr(target_pointer_width = "64", allow(clippy::absurd_extreme_comparisons))]
    pub const fn next(self) -> Self {
        match self.0.checked_add(1) {
            Some(next) if next.get() <= LotId::GENERATION_MAX => Self(next),
            _ => Self::first(),
        }
    }

    #[inline]
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
