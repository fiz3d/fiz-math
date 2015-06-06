#![allow(dead_code)]

use std::ops::{Add, Sub, Mul, Div};
use std::cmp::{PartialEq, PartialOrd, Ordering};
pub use num::{Zero, One};
use super::float::Float;
use std::fmt;

/// Vec2 is a generic two-component vector type.
///
/// The equality operator (==) on a vector is defined differently depending on
/// the type. If the type T is a floating-point number type; equality is defined
/// as near-equality via the almost_equal function. Otherwise if the type is a
/// signed or unsigned integer type, equality is defined as a binary (i.e. 1:1
/// identical) comparison.
#[derive(Copy, Clone, Debug)]
pub struct Vec2<T>{
    x: T,
    y: T,
}

impl<T> Vec2<T>{
    /// new returns a new vector with the given parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = fiz_math::Vec2::new(4.0f32, 8.0f32);
    /// println!("{:?}", x);
    /// ```
    ///
    /// ```
    /// let x = fiz_math::Vec2::new(1u8, 5u8);
    /// println!("{:?}", x);
    /// ```
    pub fn new(x: T, y: T) -> Self {
        Vec2{x: x, y: y}
    }
}

/// Point2 is a generic two-component (2D) point type.
///
/// # Examples
///
/// ```
/// use fiz_math::Point2;
///
/// let p = Point2::new(1.0, 2.0);
/// assert_eq!(p + p, Point2::new(2.0, 4.0))
/// ```
pub type Point2<T> = Vec2<T>;

impl<T: fmt::Display> fmt::Display for Vec2<T> {
    /// fmt formats the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = fiz_math::Vec2::new(1u8, 5u8);
    /// assert_eq!(format!("{}", x), "Vec2(1, 5)");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Vec2({}, {})", self.x, self.y)
    }
}

impl<T: One> One for Vec2<T>{
    /// one returns the one value for a vector whose component type implements the
    /// num::One trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::One;
    ///
    /// let x = fiz_math::Vec2::<f32>::one();
    /// ```
    ///
    /// ```
    /// use fiz_math::One;
    ///
    /// let x = fiz_math::Vec2::<i64>::one();
    /// ```
    fn one() -> Self {
        Vec2{x: T::one(), y: T::one()}
    }
}

impl<T: Float> Vec2<T>{
    /// almost_equal tells if this vector is equal to the other given an absolute
    /// tolerence value (see the almost_equal function for more details).
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::<f32>::new(1.0, 1.0);
    /// let b = Vec2::<f32>::new(0.9, 0.9);
    /// assert!(a.almost_equal(b, 0.1000001));
    /// assert!(!a.almost_equal(b, 0.1));
    /// ```
    pub fn almost_equal(self, other: Self, abs_tol: T) -> bool {
        self.x.almost_equal(other.x, abs_tol) &&
        self.y.almost_equal(other.y, abs_tol)
    }

    /// is_nan tells if all of this vectors components are NaN.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate num;
    /// # extern crate fiz_math;
    /// use num::traits::Float;
    /// use fiz_math::Vec2;
    ///
    /// # fn main() {
    /// let n:f32 = Float::nan();
    /// assert!(Vec2::new(n, n).is_nan());
    /// assert!(!Vec2::new(n, 0.0).is_nan());
    /// # }
    /// ```
    pub fn is_nan(self) -> bool {
        self.x.is_nan() &&
        self.y.is_nan()
    }
}

impl<T: Add<Output = T>> Add for Vec2<T>{
    type Output = Self;

    /// add performs component-wise addition of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(1, 2);
    /// let b = Vec2::new(4, 5);
    /// assert_eq!(a + b, Vec2::new(5, 7));
    /// ```
    fn add(self, _rhs: Self) -> Self {
        Vec2{
            x: self.x + _rhs.x,
            y: self.y + _rhs.y,
        }
    }
}

impl<T: Add<Output = T> + Copy> Vec2<T> {
    /// add_scalar performs scalar addition on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(1, 2);
    /// assert_eq!(a.add_scalar(1), Vec2::new(2, 3));
    /// ```
    pub fn add_scalar(self, _rhs: T) -> Self {
        Vec2{
            x: self.x + _rhs,
            y: self.y + _rhs,
        }
    }
}

impl<T: Sub<Output = T>> Sub for Vec2<T>{
    type Output = Self;

    /// sub performs component-wise subtraction of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(1, 2);
    /// let b = Vec2::new(4, 5);
    /// assert_eq!(a - b, Vec2::new(-3, -3));
    /// ```
    fn sub(self, _rhs: Self) -> Self {
        Vec2{
            x: self.x - _rhs.x,
            y: self.y - _rhs.y,
        }
    }
}

impl<T: Sub<Output = T> + Copy> Vec2<T> {
    /// sub_scalar performs scalar subtraction on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(2, 3);
    /// assert_eq!(a.sub_scalar(1), Vec2::new(1, 2));
    /// ```
    pub fn sub_scalar(self, _rhs: T) -> Self {
        Vec2{
            x: self.x - _rhs,
            y: self.y - _rhs,
        }
    }
}

impl<T: Mul<Output = T>> Mul for Vec2<T>{
    type Output = Self;

    /// mul performs component-wise multiplication of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(1, 2);
    /// let b = Vec2::new(4, 5);
    /// assert_eq!(a * b, Vec2::new(4, 10));
    /// ```
    fn mul(self, _rhs: Self) -> Self {
        Vec2{
            x: self.x * _rhs.x,
            y: self.y * _rhs.y,
        }
    }
}

impl<T: Mul<Output = T> + Copy> Vec2<T> {
    /// mul_scalar performs scalar multiplication on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(2, 3);
    /// assert_eq!(a.mul_scalar(2), Vec2::new(4, 6));
    /// ```
    pub fn mul_scalar(self, _rhs: T) -> Self {
        Vec2{
            x: self.x * _rhs,
            y: self.y * _rhs,
        }
    }
}

impl<T: Div<Output = T>> Div for Vec2<T>{
    type Output = Vec2<T>;

    /// div performs component-wise division of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(4, 5);
    /// let b = Vec2::new(1, 2);
    /// assert_eq!(a / b, Vec2::new(4, 2));
    /// ```
    fn div(self, _rhs: Self) -> Self {
        Vec2{
            x: self.x / _rhs.x,
            y: self.y / _rhs.y,
        }
    }
}

impl<T: Div<Output = T> + Copy> Vec2<T> {
    /// div_scalar performs scalar division on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(2, 4);
    /// assert_eq!(a.div_scalar(2), Vec2::new(1, 2));
    /// ```
    pub fn div_scalar(self, _rhs: T) -> Self {
        Vec2{
            x: self.x / _rhs,
            y: self.y / _rhs,
        }
    }
}

impl<T> AsRef<Vec2<T>> for Vec2<T> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T:PartialOrd> Vec2<T> {
    /// any_less tells if any component of the other vector is less than any
    /// component of this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(0, 1);
    /// assert!(a.any_less(Vec2::new(0, 2)));
    /// ```
    pub fn any_less<O:AsRef<Self>>(&self, other: O) -> bool {
        let o = other.as_ref();
        self.x < o.x || self.y < o.y
    }

    /// any_greater tells if any component of the other vector is greater than
    /// any component of this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(0, 2);
    /// assert!(a.any_greater(Vec2::new(0, 1)));
    /// ```
    pub fn any_greater<O:AsRef<Self>>(&self, other: O) -> bool {
        let o = other.as_ref();
        self.x > o.x || self.y > o.y
    }
}

// Different implementations are needed for PartialEq for float (relative
// equality) vs integer types (binary equality). For this reason we must use a
// macro for the separate implementations for each concrete type.

macro_rules! impl_floats {
    ($($ty:ty),*) => ($(
        impl PartialEq for Vec2<$ty> {
            /// eq tests for component-wise equality of two vectors, using the
            /// equal function (i.e. almost_equal with the EPSILON constant).
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Vec2;
            ///
            /// let a = Vec2::new(4.0, 9.0);
            /// let b = Vec2::new(4.0, 9.00000000000000000000001);
            /// assert_eq!(a, b);
            /// ```
            fn eq(&self, _rhs: &Self) -> bool {
                self.x.equal(_rhs.x) &&
                self.y.equal(_rhs.y)
            }
        }
    )*);
}

macro_rules! impl_ints {
    ($($ty:ty),*) => ($(
        impl PartialEq for Vec2<$ty> {
            /// eq tests for component-wise binary equality of two vectors.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Vec2;
            ///
            /// let a = Vec2::new(4, 5);
            /// let b = Vec2::new(4, 5);
            /// assert_eq!(a, b);
            /// ```
            ///
            fn eq(&self, _rhs: &Self) -> bool {
                self.x == _rhs.x &&
                self.y == _rhs.y
            }
        }
    )*);
}

macro_rules! impl_all {
    ($($ty:ty),*) => ($(
        impl PartialOrd for Vec2<$ty>{
            /// partial_cmp compares the two vectors component-wise.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Vec2;
            ///
            /// let a = Vec2::new(1.0, 2.0);
            /// assert!(a < Vec2::new(1.1, 2.1));
            /// ```
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                if self.x < other.x && self.y < other.y {
                    Some(Ordering::Less)
                } else if self.x > other.x && self.y > other.y {
                    Some(Ordering::Greater)
                } else if self == other {
                    Some(Ordering::Equal)
                } else {
                    None
                }
            }
        }

        impl Zero for Vec2<$ty>{
            /// zero returns the zero-value for the vector.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::{Zero, Vec2};
            ///
            /// let x = Vec2::<u8>::zero();
            /// let y = Vec2::<i64>::zero();
            /// let z = Vec2::<f32>::zero();
            /// let w = Vec2::<f64>::zero();
            /// ```
            fn zero() -> Self {
                Vec2{x: Zero::zero(), y: Zero::zero()}
            }

            /// is_zero tests if the vector is equal to zero.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::{Zero, Vec2};
            ///
            /// assert!(!Vec2::new(1i32, 0).is_zero());
            /// assert!(Vec2::new(0u8, 0).is_zero());
            /// assert!(!Vec2::new(1.0f32, 0.0).is_zero());
            /// assert!(Vec2::new(0.0f64, 0.0).is_zero());
            /// ```
            fn is_zero(&self) -> bool {
                *self == Vec2::<$ty>::zero()
            }
        }
    )*);
}

impl_floats! { f32, f64 }
impl_ints! { i8, u8, i16, u16, i32, u32, i64, u64, isize, usize }
impl_all! { f32, f64, i8, u8, i16, u16, i32, u32, i64, u64, isize, usize }
