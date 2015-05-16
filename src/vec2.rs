#![allow(dead_code)]

use std::ops::{Add, Sub, Mul, Div};
use std::cmp::PartialEq;
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
    pub fn new(x: T, y: T) -> Vec2<T> {
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
    pub fn almost_equal(self, other: Vec2<T>, abs_tol: T) -> bool {
        self.x.almost_equal(other.x, abs_tol) &&
        self.y.almost_equal(other.y, abs_tol)
    }
}

impl<T: Add<Output = T>> Add for Vec2<T>{
    type Output = Vec2<T>;

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
    fn add(self, _rhs: Vec2<T>) -> Vec2<T> {
        Vec2{
            x: self.x + _rhs.x,
            y: self.y + _rhs.y,
        }
    }
}

impl<T: Sub<Output = T>> Sub for Vec2<T>{
    type Output = Vec2<T>;

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
    fn sub(self, _rhs: Vec2<T>) -> Vec2<T> {
        Vec2{
            x: self.x - _rhs.x,
            y: self.y - _rhs.y,
        }
    }
}

impl<T: Mul<Output = T>> Mul for Vec2<T>{
    type Output = Vec2<T>;

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
    fn mul(self, _rhs: Vec2<T>) -> Vec2<T> {
        Vec2{
            x: self.x * _rhs.x,
            y: self.y * _rhs.y,
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
    fn div(self, _rhs: Vec2<T>) -> Vec2<T> {
        Vec2{
            x: self.x / _rhs.x,
            y: self.y / _rhs.y,
        }
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
            fn eq(&self, _rhs: &Vec2<$ty>) -> bool {
                self.x.equal(_rhs.x) &&
                self.y.equal(_rhs.y)
            }
        }

        impl Zero for Vec2<$ty>{
            /// zero returns the zero-value for the vector.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec2::<f32>::zero();
            /// ```
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec2::<f64>::zero();
            /// ```
            fn zero() -> Self {
                Vec2{x: 0.0, y: 0.0}
            }

            /// is_zero tests if the vector is equal to zero.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec2::new(1.0, 0.0);
            /// assert!(!x.is_zero())
            /// ```
            fn is_zero(&self) -> bool {
                *self == Vec2::<$ty>::zero()
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
            fn eq(&self, _rhs: &Vec2<$ty>) -> bool {
                self.x == _rhs.x &&
                self.y == _rhs.y
            }
        }

        impl Zero for Vec2<$ty>{
            /// zero returns the zero-value for the vector.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec2::<u8>::zero();
            /// ```
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec2::<i64>::zero();
            /// ```
            fn zero() -> Self {
                Vec2{x: 0, y: 0}
            }

            /// is_zero tests if the vector is equal to zero.
            ///
            /// # Examples
            ///
            /// ```
            /// use fiz_math::Zero;
            ///
            /// let x = fiz_math::Vec2::new(1, 0);
            /// assert!(!x.is_zero())
            /// ```
            fn is_zero(&self) -> bool {
                *self == Vec2::<$ty>::zero()
            }
        }
    )*);
}

impl_floats! { f32, f64 }
impl_ints! { i8, u8, i16, u16, i32, u32, i64, u64, isize, usize }
