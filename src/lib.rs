//! A library for getting aligned vectors, slices, and arrays of bytes or any other type
//!
//! The `A*` structs are aligned as indicated and hold a single array of bytes of the same size.
//! These implement the [Alignment](align::Alignment) trait that can be used for always aligned byte arrays for faster
//! memory copies or copies by hardware. The arrays are accessible as slices using [as_bytes()](align::AsBytes::as_bytes) or
//! [as_bytes_mut()](align::AsBytesMut::as_bytes_mut) or by dereferencing the struct.
//! ```
//! # use maligned::*;
//! let alignment_256 = A256::default();
//!
//! assert_eq!(std::mem::size_of::<A256>(), std::mem::size_of_val(alignment_256.as_bytes()));
//! assert_eq!(alignment_256.as_bytes().as_ptr() as usize % std::mem::size_of::<A256>(), 0);
//! ```
//!
//! If you need more than a single [Alignment](align::Alignment) of bytes you can create a vector of them
//! and that can be converted into a normal byte slice that always has the first byte aligned.
//!
//! ```
//! # use maligned::*;
//! let mut v = vec![A512::default(); 100];
//! assert_eq!(v.as_bytes().len(), std::mem::size_of::<A512>() * 100);
//! assert_eq!(v.as_bytes().as_ptr() as usize % std::mem::align_of::<A512>(), 0);
//!
//! v.as_bytes_mut()[512] = 42;
//! assert_eq!(v[1][0], 42);
//! ```
//!
//! There is also a wrapper [Aligned](align::Aligned) that aligns any type to a specified alignment
//! ```
//! # use maligned::*;
//! // aligned() is an alias for Aligned::new()
//! let a: Aligned<A32, [u8; 24]> = aligned([0; 24]);
//! assert_eq!(std::mem::align_of_val(&a), 32);
//! assert_eq!(&*a as *const u8 as usize % std::mem::align_of::<A32>(), 0);
//! ```
//!
//! If the `alloc` feature is enabled (it is by default) then there are a few more functions available.
//! [align_first](heap::align_first) returns an empty Vec with a capacity of at least `capacity` bytes.
//! Two type parameters are currently required, though the first can be set to `_`, because of the current
//! interaction between impl traits and generics.
//! ```
//! # use maligned::*;
//! let v: Vec<u8> = align_first::<u8, A256>(1009);
//! assert_eq!(v.as_ptr() as usize % 256, 0);
//! assert_eq!(v.capacity(), 1009);
//! ```
//!
//! [align_first_boxed](heap::align_first_boxed), [align_first_boxed_default](heap::align_first_boxed_default),
//! and [align_first_boxed_cloned](heap::align_first_boxed_cloned) all return a [Box<\[T\]>](alloc::boxed::Box) with the
//! first element aligned to at least [Alignment](align::Alignment) bytes.
//! ```
//! # use maligned::*;
//! // 3 type parameters. The last one should always be _ until impl traits and generics interact better
//! let boxed: Box<[Option<u128>]> = align_first_boxed::<_, A512, _>(101, |_|Some(42));
//! let defaulted: Box<[Option<u128>]> = align_first_boxed_default::<_, A128>(101);
//! let cloned: Box<[Option<u128>]> = align_first_boxed_cloned::<_, Bit512>(101, Some(42));
//!
//! assert_eq!(&*boxed, &vec![Some(42); 101][..]);
//! assert_eq!(&boxed, &cloned);
//! assert_eq!(boxed.len(), 101);
//! assert_eq!(defaulted.len(), 101);
//! assert_eq!(cloned.len(), 101);
//! assert_eq!(&*defaulted, &vec![None; 101][..]);
//! ```

#![no_std]
#![cfg_attr(all(not(test), feature = "clippy"), deny(warnings, clippy::all, clippy::pedantic))]
#![deny(unsafe_code, missing_docs)]
#![allow(clippy::doc_markdown)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(test)]
#[macro_use]
extern crate std;

mod align;
pub use align::*;

#[cfg(feature = "alloc")]
mod heap;
#[cfg(feature = "alloc")]
pub use heap::*;

/// allow * imports
pub mod prelude {
  pub use super::*;
}
