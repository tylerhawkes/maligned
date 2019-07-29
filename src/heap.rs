use super::*;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::mem::{align_of, forget, size_of};

/// Aligns the first element in a `Vec<T>` to `A`. If the alignment of `A` is less than the alignment of `T` then a `Vec<T>`
/// with capacity `t_capacity` is returned. This method is safe because structs are always aligned to a power of two so
/// aligning the first item in a `Vec<T>` to a higher alignment will always be aligned correctly.
///
/// This method is useful for getting byte arrays that need to be copied so that an efficient memory copy can be used instead
/// of a byte by byte copy. It is also useful when working on some devices that can do hardware copies but require 128, 256,
/// or higher bit alignments to be efficient.
#[allow(unsafe_code)]
pub fn align_first<T, A: Alignment>(t_capacity: usize) -> Vec<T> {
  if align_of::<A>() <= align_of::<T>() {
    return Vec::<T>::with_capacity(t_capacity);
  }
  let min_bytes_to_allocate = size_of::<T>() * t_capacity;
  let alignments_to_allocate = min_bytes_to_allocate / size_of::<A>() + if min_bytes_to_allocate % size_of::<A>() == 0 { 0 } else { 1 };
  let mut alignment_vec = Vec::<A>::with_capacity(alignments_to_allocate);
  let bytes_allocated = alignment_vec.capacity() * size_of::<A>();
  // return bytes to the allocator that aren't needed.
  if min_bytes_to_allocate < bytes_allocated {
    let mut byte_vec = unsafe { Vec::<u8>::from_raw_parts(alignment_vec.as_mut_ptr() as *mut _, min_bytes_to_allocate, bytes_allocated) };
    byte_vec.shrink_to_fit();
    forget(byte_vec);
  }
  let type_vec = unsafe { Vec::<T>::from_raw_parts(alignment_vec.as_mut_ptr() as *mut _, 0, t_capacity) };
  forget(alignment_vec);
  debug_assert_eq!(type_vec.as_ptr() as usize % align_of::<A>(), 0);
  type_vec
}

#[cfg(test)]
macro_rules! assert_alignment {
  ($l:ty, $s:ty) => {
    println!(
      "Aligning types: l: ({}, {}), s: ({}, {})",
      align_of::<$l>(),
      size_of::<$l>(),
      align_of::<$s>(),
      size_of::<$s>()
    );
    std::io::stdout().flush().ok().expect("Could not flush stdout");
    let v = align_first::<$l, $s>(17);
    assert_eq!(v.len(), 0);
    assert_eq!(v.as_ptr() as usize % align_of::<$l>(), 0);
    assert_eq!(v.capacity(), 17);
  };
}

#[cfg(test)]
#[allow(unused)]
#[repr(C)]
struct NonPowerOf2Size {
  a: u8,
  b: u8,
  c: u32,
}

#[test]
fn test_align_first() {
  use std::io::Write;
  assert_alignment!(Bit8, u8);
  assert_alignment!(Bit16, u16);
  assert_alignment!(Bit32, u32);
  assert_alignment!(Bit64, u64);
  assert_alignment!(Bit128, u128);
  assert_alignment!([u64; 4], Bit256);
  assert_alignment!(u64, A8);
  assert_alignment!([u32; 2], u64);
  assert_alignment!([u8; 8], u64);
  assert_alignment!([u8; 16], A16);
  assert_alignment!([u8; 1024], A1024);
  assert_alignment!([u8; 97], u8);
  assert_alignment!([u64; 101], u64);
  assert_alignment!([u8; 103], u8);
  assert_alignment!([u64; 107], u64);
  assert_alignment!([u32; 109], u16);
  assert_alignment!([A32; 139], A8);
  assert_alignment!([u32; 19], u16);
  assert_alignment!([A32; 31], A8);
  assert_alignment!(NonPowerOf2Size, A32);
  assert_alignment!([NonPowerOf2Size; 3], Bit1024);
  assert_alignment!([u16; 197], u32);
  assert_alignment!([A8; 191], A32);
  assert_alignment!([u16; 131], u32);
}

/// Aligns types and initializes memory to the return value provided by the closure.
/// Since boxed slices can never re-allocate the first item will always be aligned.
/// ```
/// # use maligned::*;
/// let f = |i|(i & u8::max_value() as usize) as u8;
/// let s = align_first_boxed::<u8, A128, _>(1023, f);
/// assert_eq!(s.len(), 1023);
/// s.iter().for_each(|b| assert_eq!(*b, f(*b as usize)));
/// ```
pub fn align_first_boxed<T, A: Alignment, F: FnMut(usize) -> T>(s_capacity: usize, mut f: F) -> Box<[T]> {
  let mut v = align_first::<T, A>(s_capacity);
  (0..s_capacity).for_each(|i| v.push(f(i)));
  v.into_boxed_slice()
}

/// Aligns types and initializes memory to default then returns a boxed
/// slice. Since boxed slices can never re-allocate the first item will always be aligned.
/// ```
/// # use maligned::*;
/// let s = align_first_boxed_default::<u8, A128>(2047);
/// assert_eq!(s.len(), 2047);
/// s.iter().for_each(|b| assert_eq!(*b, 0));
/// ```
pub fn align_first_boxed_default<T: Default, A: Alignment>(s_capacity: usize) -> Box<[T]> {
  align_first_boxed::<T, A, _>(s_capacity, |_| T::default())
}

/// Aligns types and initializes all values to clones of `initial` then returns a boxed
/// slice. Since boxed slices can never re-allocate the first item will always be aligned.
/// ```
/// # use maligned::*;
/// let initial = 42;
/// let s = align_first_boxed_cloned::<u8, A128>(1023, initial);
/// assert_eq!(s.len(), 1023);
/// s.iter().for_each(|b| assert_eq!(*b, initial));
/// ```
pub fn align_first_boxed_cloned<T: Clone, A: Alignment>(s_capacity: usize, initial: T) -> Box<[T]> {
  align_first_boxed::<T, A, _>(s_capacity, |_| initial.clone())
}
