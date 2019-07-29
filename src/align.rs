use core::mem::size_of;
#[cfg(test)]
use core::mem::{align_of, size_of_val};

mod sealed_traits {
  pub trait SealedAlignment {}

  pub trait SealedAsBytes {}

  pub trait SealedAsBytesMut: SealedAsBytes {}
}

/// Marker trait used for bounds. Public so that it can be extended if necessary.
/// All structs that implement this trait in `maligned` have their size and alignment equal.
pub trait Alignment: sealed_traits::SealedAlignment + Sized + Clone + Default + Send + Sync {}

/// Trait that allows re-interpretation of a struct as bytes. This is unsafe since the
/// returned slice must always have a length equal to the size of the struct and because
/// every bit pattern must be valid.
#[allow(unsafe_code)]
pub unsafe trait AsBytes: sealed_traits::SealedAsBytes + Sized {
  /// Turn a reference to self to a byte slice. Useful when dealing with serialization.
  fn as_bytes(&self) -> &[u8];
}

/// Trait that allows re-interpretation of a mutable struct as mutable bytes. This is unsafe since the
/// returned slice must always have a length equal to the size of the struct and because
/// every bit pattern must be valid.
#[allow(unsafe_code)]
pub unsafe trait AsBytesMut: sealed_traits::SealedAsBytesMut + AsBytes {
  /// Turn a mutable reference to self to a mutable byte slice. Useful when dealing with serialization.
  fn as_bytes_mut(&mut self) -> &mut [u8];
}

macro_rules! impl_alignment_traits {
  ($t:ident, $c:literal, $bit:ident, $test:ident) => {
    impl sealed_traits::SealedAlignment for $t {}
    impl Alignment for $t {}
    /// Type alias for an Alignment in bits
    pub type $bit = $t;
    // Not a trait since const generics aren't stable yet
    #[doc(hidden)]
    impl $t {
      pub fn as_array(&self) -> &[u8; size_of::<Self>()] {
        &self.0
      }
      pub fn as_array_mut(&mut self) -> &mut [u8; size_of::<Self>()] {
        &mut self.0
      }
      pub fn into_array(self) -> [u8; size_of::<Self>()] {
        self.0
      }
    }
    impl sealed_traits::SealedAsBytes for $t {}
    #[allow(unsafe_code)]
    unsafe impl AsBytes for $t {
      fn as_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(&self.0 as *const [u8; size_of::<Self>()] as *const u8, size_of::<Self>()) }
      }
    }
    impl sealed_traits::SealedAsBytesMut for $t {}
    #[allow(unsafe_code)]
    unsafe impl AsBytesMut for $t {
      fn as_bytes_mut(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(&mut self.0 as *mut [u8; size_of::<Self>()] as *mut u8, size_of::<Self>()) }
      }
    }
    impl Default for $t {
      fn default() -> Self {
        Self([0; size_of::<Self>()])
      }
    }
    impl Clone for $t {
      fn clone(&self) -> Self {
        let mut clone = Self::default();
        self.0.iter().zip(clone.as_bytes_mut()).for_each(|(orig, new)| *new = *orig);
        clone
      }
    }
    impl core::ops::Deref for $t {
      type Target = [u8];
      fn deref(&self) -> &Self::Target {
        self.as_bytes()
      }
    }
    impl core::ops::DerefMut for $t {
      fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_bytes_mut()
      }
    }
    impl From<[u8; size_of::<$t>()]> for $t {
      fn from(a: [u8; size_of::<Self>()]) -> Self {
        Self(a)
      }
    }
    impl AsRef<[u8]> for $t {
      fn as_ref(&self) -> &[u8] {
        self.as_bytes()
      }
    }
    impl AsMut<[u8]> for $t {
      fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
      }
    }
    impl Ord for $t {
      fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_bytes().cmp(other.as_bytes())
      }
    }
    impl PartialOrd for $t {
      fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_bytes().partial_cmp(other.as_bytes())
      }
    }
    impl Eq for $t {}
    impl PartialEq for $t {
      fn eq(&self, other: &Self) -> bool {
        self.as_bytes().eq(other.as_bytes())
      }
    }
    impl core::hash::Hash for $t {
      fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state)
      }
    }
    #[test]
    fn $test() {
      assert_eq!(align_of::<$t>(), $c);
      assert_eq!(size_of::<$t>(), $c);
      assert_eq!(align_of::<$t>(), size_of::<$t>());
      assert_eq!(size_of_val(&*<$t>::default()), size_of::<$t>());
      assert_eq!(align_of::<$t>(), size_of::<$bit>());
      assert_eq!(size_of::<$t>(), size_of::<$bit>());
      assert_eq!(size_of_val(&*<$t>::default()), size_of_val(&*<$bit>::default()));
      assert_eq!(<$t>::default().as_bytes().len(), $c);
      assert_eq!(<$t>::default().as_bytes_mut().len(), $c);
      let vec_length = 17;
      let mut v = vec![<$t>::default(); vec_length];
      assert_eq!(v.len(), vec_length);
      let mut v_ref: &mut [$t] = &mut v;
      assert_eq!(v_ref.as_bytes().len(), $c * vec_length);
      assert_eq!(v_ref.as_bytes_mut().len(), $c * vec_length);
    }
  };
}

macro_rules! impl_primitive {
  ($t:ident) => {
    impl sealed_traits::SealedAlignment for $t {}
    impl Alignment for $t {}
    impl sealed_traits::SealedAsBytes for $t {}
    #[allow(unsafe_code)]
    #[allow(clippy::use_self)]
    unsafe impl AsBytes for $t {
      fn as_bytes(&self) -> &[u8] {
        // allow use_self because of the warning for u8
        unsafe { core::slice::from_raw_parts(self as *const Self as *const u8, size_of::<Self>()) }
      }
    }
    impl sealed_traits::SealedAsBytesMut for $t {}
    #[allow(unsafe_code)]
    #[allow(clippy::use_self)]
    unsafe impl AsBytesMut for $t {
      fn as_bytes_mut(&mut self) -> &mut [u8] {
        // allow use_self because of the warning for u8
        unsafe { core::slice::from_raw_parts_mut(self as *mut Self as *mut u8, size_of::<Self>()) }
      }
    }
  };
}

#[allow(clippy::use_self)]
impl_primitive! {u8}
impl_primitive! {i8}
impl_primitive! {u16}
impl_primitive! {i16}
impl_primitive! {u32}
impl_primitive! {i32}
impl_primitive! {u64}
impl_primitive! {i64}
impl_primitive! {u128}
impl_primitive! {i128}
impl_primitive! {usize}
impl_primitive! {isize}
impl_primitive! {f32}
impl_primitive! {f64}

/// Struct representing an alignment of 1
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of [u8; 1]. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A1]`
/// can be used as a buffer of bytes that will always be aligned to at least 1 byte.
///
/// This struct isn't really that useful and is here for completeness.
#[repr(align(1))]
pub struct A1(pub [u8; 1]);
impl_alignment_traits! {A1, 1, Bit8, test_a1}

/// Struct representing an alignment of 2
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of` [u8; 2]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A2]`
/// can be used as a buffer of bytes that will always be aligned to at least 2 bytes.
#[repr(align(2))]
pub struct A2(pub [u8; 2]);
impl_alignment_traits! {A2, 2, Bit16, test_a2}

/// Struct representing an alignment of 4
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of` [u8; 4]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A4]`
/// can be used as a buffer of bytes that will always be aligned to at least 4 bytes.
#[repr(align(4))]
pub struct A4(pub [u8; 4]);
impl_alignment_traits! {A4, 4, Bit32, test_a4}

/// Struct representing an alignment of 8
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of` [u8; 8]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A8]`
/// can be used as a buffer of bytes that will always be aligned to at least 8 bytes.
#[repr(align(8))]
pub struct A8(pub [u8; 8]);
impl_alignment_traits! {A8, 8, Bit64, test_a8}

/// Struct representing an alignment of 16
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of `[u8; 16]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A16]`
/// can be used as a buffer of bytes that will always be aligned to at least 16 bytes.
#[repr(align(16))]
pub struct A16(pub [u8; 16]);
impl_alignment_traits! {A16, 16, Bit128, test_a16}

/// Struct representing an alignment of 32
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of `[u8; 32]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A32]`
/// can be used as a buffer of bytes that will always be aligned to at least 32 bytes.
#[repr(align(32))]
pub struct A32(pub [u8; 32]);
impl_alignment_traits! {A32, 32, Bit256, test_a32}

/// Struct representing an alignment of 64
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// o`f [u8; 64]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A64]`
/// can be used as a buffer of bytes that will always be aligned to at least 64 bytes.
#[repr(align(64))]
pub struct A64(pub [u8; 64]);
impl_alignment_traits! {A64, 64, Bit512, test_a64}

/// Struct representing an alignment of 128
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of` [u8; 128]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A128]`
/// can be used as a buffer of bytes that will always be aligned to at least 128 bytes.
#[repr(align(128))]
pub struct A128(pub [u8; 128]);
impl_alignment_traits! {A128, 128, Bit1024, test_a128}

/// Struct representing an alignment of 256
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of` [u8; 256]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A256]`
/// can be used as a buffer of bytes that will always be aligned to at least 256 bytes.
#[repr(align(256))]
pub struct A256(pub [u8; 256]);
impl_alignment_traits! {A256, 256, Bit2048, test_a256}

/// Struct representing an alignment of 512
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of` [u8; 512]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A512]`
/// can be used as a buffer of bytes that will always be aligned to at least 512 bytes.
#[repr(align(512))]
pub struct A512(pub [u8; 512]);
impl_alignment_traits! {A512, 512, Bit4096, test_a512}

/// Struct representing an alignment of 1024
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of `[u8; 1024]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A1024]`
/// can be used as a buffer of bytes that will always be aligned to at least 1024 bytes.
#[repr(align(1024))]
pub struct A1024(pub [u8; 1024]);
impl_alignment_traits! {A1024, 1024, Bit8192, test_a1024}

/// Struct representing an alignment of 2048
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of `[u8; 2048]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A2048]`
/// can be used as a buffer of bytes that will always be aligned to at least 2048 bytes.
#[repr(align(2048))]
pub struct A2048(pub [u8; 2048]);
impl_alignment_traits! {A2048, 2048, Bit16384, test_a2048}

/// Struct representing an alignment of 4096
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of `[u8; 4096]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A4096]`
/// can be used as a buffer of bytes that will always be aligned to at least 4096 bytes.
#[repr(align(4096))]
pub struct A4096(pub [u8; 4096]);
impl_alignment_traits! {A4096, 4096, Bit32768, test_a4096}

/// Struct representing an alignment of 8192
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of `[u8; 8192]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A8192]`
/// can be used as a buffer of bytes that will always be aligned to at least 8192 bytes.
#[repr(align(8192))]
pub struct A8192(pub [u8; 8192]);
impl_alignment_traits! {A8192, 8192, Bit65536, test_a8192}

/// Struct representing an alignment of 16384
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of [`u8; 16384]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A16384]`
/// can be used as a buffer of bytes that will always be aligned to at least 16384 bytes.
#[repr(align(16384))]
pub struct A16384(pub [u8; 16384]);
impl_alignment_traits! {A16384, 16384, Bit131072, test_a16384}

/// Struct representing an alignment of 32768
///
/// This implements the `Alignment` trait and can also be used as a byte buffer
/// of `[u8; 32768]`. Since `AsBytes` is implemented for a `&[T: AsBytes]` a `&[A32768]`
/// can be used as a buffer of bytes that will always be aligned to at least 32768 bytes.
#[repr(align(32768))]
pub struct A32768(pub [u8; 32768]);
impl_alignment_traits! {A32768, 32768, Bit262144, test_a32768}

/// Wrapper type that aligns `T` to `Alignment`
/// It adds no size to the layout of the struct if the size is a multiple of the alignment,
/// otherwise the size is rounded up to the next multiple of the alignment
/// ```
/// # use maligned::*;
/// # use std::mem::*;
/// assert_eq!(size_of::<Aligned<A1024, [u8; 1024]>>(), size_of::<[u8; 1024]>());
/// assert_eq!(size_of::<Aligned<A2048, [u8; 81920]>>(), size_of::<[u8; 81920]>());
/// ```
#[derive(Clone, Copy, Default, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Aligned<A: Alignment, T> {
  _alignment: [A; 0],
  t: T,
}

impl<A: Alignment, T> Aligned<A, T> {
  /// Creates a new instance of Aligned
  pub fn new(t: T) -> Self {
    Self { _alignment: [], t }
  }
  /// Consumes Aligned and returns the wrapped value
  pub fn into_inner(self) -> T {
    self.t
  }
}

/// Convenience function for creating a new Aligned
/// Because of the current interaction between generics and impl arguments
/// the function requires both types to be given, though the second one can
/// be given the default `_`
/// To align a byte array to a 256 bit boundary
/// ```
/// # use maligned::*;
/// let a = aligned::<Bit256, _>([0_u8; 1024]);
/// assert_eq!(&a[0] as *const u8 as usize % std::mem::align_of::<Bit256>(), 0);
/// ```
pub fn aligned<A: Alignment, T>(t: T) -> Aligned<A, T> {
  Aligned::new(t)
}

impl<A: Alignment, T> core::ops::Deref for Aligned<A, T> {
  type Target = T;

  fn deref(&self) -> &Self::Target {
    &self.t
  }
}

impl<A: Alignment, T> core::ops::DerefMut for Aligned<A, T> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.t
  }
}

impl<A: Alignment, T> From<T> for Aligned<A, T> {
  fn from(t: T) -> Self {
    Self::new(t)
  }
}

impl<A: Alignment, T> AsRef<T> for Aligned<A, T> {
  fn as_ref(&self) -> &T {
    &self.t
  }
}

impl<A: Alignment, T> AsMut<T> for Aligned<A, T> {
  fn as_mut(&mut self) -> &mut T {
    &mut self.t
  }
}

impl<T: AsBytes> sealed_traits::SealedAsBytes for &[T] {}
#[allow(unsafe_code)]
unsafe impl<T: AsBytes> AsBytes for &[T] {
  fn as_bytes(&self) -> &[u8] {
    unsafe { core::slice::from_raw_parts(self.as_ptr() as *const T as *const u8, self.len() * size_of::<T>()) }
  }
}

impl<T: AsBytes> sealed_traits::SealedAsBytes for &mut [T] {}
#[allow(unsafe_code)]
unsafe impl<T: AsBytes> AsBytes for &mut [T] {
  fn as_bytes(&self) -> &[u8] {
    unsafe { core::slice::from_raw_parts(self.as_ptr() as *const T as *const u8, self.len() * size_of::<T>()) }
  }
}

impl<T: AsBytesMut> sealed_traits::SealedAsBytesMut for &mut [T] {}
#[allow(unsafe_code)]
unsafe impl<T: AsBytesMut> AsBytesMut for &mut [T] {
  fn as_bytes_mut(&mut self) -> &mut [u8] {
    unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr() as *mut T as *mut u8, self.len() * size_of::<T>()) }
  }
}
