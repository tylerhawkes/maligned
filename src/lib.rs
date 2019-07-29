//! Crate docs
#![cfg_attr(not(test), no_std, deny(warnings, clippy::pedantic, missing_docs))]
#![deny(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(test)]
extern crate std;

mod align;
pub use align::*;

#[cfg(feature = "alloc")]
mod heap;
#[cfg(feature = "alloc")]
pub use heap::*;
