#![allow(dead_code)]

use std::ops::{Add, Sub, Mul, Div};
use std::cmp::PartialEq;
pub use num::{Zero, One};
use super::float::Float;
use std::fmt;

/// Vec4 is a generic four-component (3D) vector type.
///
/// The equality operator (==) on a vector is defined differently depending on
/// the type. If the type T is a floating-point number type; equality is defined
/// as near-equality via the almost_equal function. Otherwise if the type is a
/// signed or unsigned integer type, equality is defined as a binary (i.e. 1:1
/// identical) comparison.
#[derive(Copy, Clone, Debug)]
pub struct Vec4<T>{
    x: T,
    y: T,
    z: T,
    w: T
}

impl<T> Vec4<T>{
    /// new returns a new vector with the given parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = fiz_math::Vec4::new(4.0f32, 8.0f32, 2.0f32, 3.0f32);
    /// ```
    ///
    /// ```
    /// let x = fiz_math::Vec4::new(1u8, 5u8, 2u8, 3u8);
    /// ```
    pub fn new(x: T, y: T, z: T, w: T) -> Vec4<T> {
        Vec4{x: x, y: y, z: z, w: w}
    }
}

impl<T: fmt::Display> fmt::Display for Vec4<T> {
    /// fmt formats the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = fiz_math::Vec4::new(1u8, 5u8, 2u8, 3u8);
    /// assert_eq!(format!("{}", x), "Vec3(1, 5, 2, 3)");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Vec3({}, {}, {}, {})", self.x, self.y, self.z, self.w)
    }
}

impl<T: One> One for Vec4<T>{
    /// one returns the one value for a vector whose component type implements the
    /// num::One trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::One;
    ///
    /// let x = fiz_math::Vec4::<f32>::one();
    /// ```
    ///
    /// ```
    /// use fiz_math::One;
    ///
    /// let x = fiz_math::Vec4::<i64>::one();
    /// ```
    fn one() -> Self {
        Vec4{x: T::one(), y: T::one(), z: T::one(), w: T::one()}
    }
}

impl<T: Float> Vec4<T>{
    /// almost_equal tells if this vector is equal to the other given an absolute
    /// tolerence value (see the almost_equal function for more details).
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::<f32>::new(1.0, 1.0, 1.0, 1.0);
    /// let b = Vec4::<f32>::new(0.9, 0.9, 0.9, 0.9);
    /// assert!(a.almost_equal(b, 0.1000001));
    /// assert!(!a.almost_equal(b, 0.1));
    /// ```
    pub fn almost_equal(self, other: Vec4<T>, abs_tol: T) -> bool {
        self.x.almost_equal(other.x, abs_tol) &&
        self.y.almost_equal(other.y, abs_tol) &&
        self.z.almost_equal(other.z, abs_tol) &&
        self.w.almost_equal(other.w, abs_tol)
    }
}

impl<T: Add<Output = T>> Add for Vec4<T>{
    type Output = Vec4<T>;

    /// add performs component-wise addition of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::new(1, 2, 3, 3);
    /// let b = Vec4::new(4, 5, 6, 6);
    /// assert_eq!(a + b, Vec4::new(5, 7, 9, 9));
    /// ```
    fn add(self, _rhs: Vec4<T>) -> Vec4<T> {
        Vec4{
            x: self.x + _rhs.x,
            y: self.y + _rhs.y,
            z: self.z + _rhs.z,
            w: self.w + _rhs.w,
        }
    }
}

impl<T: Add<Output = T> + Copy> Vec4<T> {
    /// add_scalar performs scalar addition on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::new(1, 2, 3, 4);
    /// assert_eq!(a.add_scalar(1), Vec4::new(2, 3, 4, 5));
    /// ```
    pub fn add_scalar(self, _rhs: T) -> Vec4<T> {
        Vec4{
            x: self.x + _rhs,
            y: self.y + _rhs,
            z: self.z + _rhs,
            w: self.w + _rhs,
        }
    }
}

impl<T: Sub<Output = T>> Sub for Vec4<T>{
    type Output = Vec4<T>;

    /// sub performs component-wise subtraction of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::new(1, 2, 3, 3);
    /// let b = Vec4::new(4, 5, 6, 6);
    /// assert_eq!(a - b, Vec4::new(-3, -3, -3, -3));
    /// ```
    fn sub(self, _rhs: Vec4<T>) -> Vec4<T> {
        Vec4{
            x: self.x - _rhs.x,
            y: self.y - _rhs.y,
            z: self.z - _rhs.z,
            w: self.w - _rhs.w,
        }
    }
}

impl<T: Sub<Output = T> + Copy> Vec4<T> {
    /// sub_scalar performs scalar subtraction on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::new(2, 3, 4, 5);
    /// assert_eq!(a.sub_scalar(1), Vec4::new(1, 2, 3, 4));
    /// ```
    pub fn sub_scalar(self, _rhs: T) -> Vec4<T> {
        Vec4{
            x: self.x - _rhs,
            y: self.y - _rhs,
            z: self.z - _rhs,
            w: self.w - _rhs,
        }
    }
}

impl<T: Mul<Output = T>> Mul for Vec4<T>{
    type Output = Vec4<T>;

    /// mul performs component-wise multiplication of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::new(1, 2, 3, 3);
    /// let b = Vec4::new(4, 5, 6, 6);
    /// assert_eq!(a * b, Vec4::new(4, 10, 18, 18));
    /// ```
    fn mul(self, _rhs: Vec4<T>) -> Vec4<T> {
        Vec4{
            x: self.x * _rhs.x,
            y: self.y * _rhs.y,
            z: self.z * _rhs.z,
            w: self.w * _rhs.w,
        }
    }
}

impl<T: Mul<Output = T> + Copy> Vec4<T> {
    /// mul_scalar performs scalar multiplication on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::new(1, 2, 3, 4);
    /// assert_eq!(a.mul_scalar(2), Vec4::new(2, 4, 6, 8));
    /// ```
    pub fn mul_scalar(self, _rhs: T) -> Vec4<T> {
        Vec4{
            x: self.x * _rhs,
            y: self.y * _rhs,
            z: self.z * _rhs,
            w: self.w * _rhs,
        }
    }
}

impl<T: Div<Output = T>> Div for Vec4<T>{
    type Output = Vec4<T>;

    /// div performs component-wise division of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec4;
    ///
    /// let a = Vec4::new(4, 5, 9, 9);
    /// let b = Vec4::new(1, 2, 3, 3);
    /// assert_eq!(a / b, Vec4::new(4, 2, 3, 3));
    /// ```
    fn div(self, _rhs: Vec4<T>) -> Vec4<T> {
        Vec4{
            x: self.x / _rhs.x,
            y: self.y / _rhs.y,
            z: self.z / _rhs.z,
            w: self.w / _rhs.w,
        }
    }
}

// Different implementations are needed for PartialEq for float (relative
// equality) vs integer types (binary equality). For this reason we must use a
// macro for the separate implementations for each concrete type.

macro_rules! impl_floats {
    ($($ty:ty),*) => ($(
        impl PartialEq for Vec4<$ty> {
            /// eq tests for component-wise equality of two vectors, using the
            /// equal function (i.e. almost_equal with the EPSILON constant).
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Vec4;
            ///
            /// let a = Vec4::new(4.0, 5.0, 5.0, 9.0);
            /// let b = Vec4::new(4.0, 5.0, 5.0, 9.00000000000000000000001);
            /// assert_eq!(a, b);
            /// ```
            fn eq(&self, _rhs: &Vec4<$ty>) -> bool {
                self.x.equal(_rhs.x) &&
                self.y.equal(_rhs.y) &&
                self.z.equal(_rhs.z) &&
                self.w.equal(_rhs.w)
            }
        }

        impl Zero for Vec4<$ty>{
            /// zero returns the zero-value for the vector.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec4::<f32>::zero();
            /// ```
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec4::<f64>::zero();
            /// ```
            fn zero() -> Self {
                Vec4{x: 0.0, y: 0.0, z: 0.0, w: 0.0}
            }

            /// is_zero tests if the vector is equal to zero.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec4::new(1.0, 0.0, 0.0, 0.0);
            /// assert!(!x.is_zero())
            /// ```
            fn is_zero(&self) -> bool {
                *self == Vec4::<$ty>::zero()
            }
        }
    )*);
}

macro_rules! impl_ints {
    ($($ty:ty),*) => ($(
        impl PartialEq for Vec4<$ty> {
            /// eq tests for component-wise binary equality of two vectors.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Vec4;
            ///
            /// let a = Vec4::new(4, 5, 9, 9);
            /// let b = Vec4::new(4, 5, 9, 9);
            /// assert_eq!(a, b);
            /// ```
            ///
            fn eq(&self, _rhs: &Vec4<$ty>) -> bool {
                self.x == _rhs.x &&
                self.y == _rhs.y &&
                self.z == _rhs.z &&
                self.w == _rhs.w
            }
        }

        impl Zero for Vec4<$ty>{
            /// zero returns the zero-value for the vector.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec4::<u8>::zero();
            /// ```
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec4::<i64>::zero();
            /// ```
            fn zero() -> Self {
                Vec4{x: 0, y: 0, z: 0, w: 0}
            }

            /// is_zero tests if the vector is equal to zero.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec4::new(1, 0, 0, 0);
            /// assert!(!x.is_zero())
            /// ```
            fn is_zero(&self) -> bool {
                *self == Vec4::<$ty>::zero()
            }
        }
    )*);
}

impl_floats! { f32, f64 }
impl_ints! { i8, u8, i16, u16, i32, u32, i64, u64, isize, usize }
