#![allow(dead_code)]

use std::ops::{Add, Sub, Neg, Mul, Div};
use std::cmp::{PartialEq, PartialOrd, Ordering};
pub use num::{Zero, One};
use num;
use super::float::Float;
use std::fmt;
use clamp::Clamp;
use length::LengthSq;

/// Vec2 is a generic two-component vector type.
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
    ///
    /// ```
    /// use fiz_math::Vec2;
    /// use fiz_math::unit::MM;
    ///
    /// let x = Vec2::new(MM(1.0), MM(5.0));
    /// let y = Vec2::new(MM(1.0), MM(5.1));
    /// assert!(x.almost_equal(y, 0.1));
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
    pub fn almost_equal<N: num::Float>(self, other: Self, abs_tol: N) -> bool {
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

impl<T: Float> Vec2<T> {
    /// round returns the nearest integer to a number. Round half-way cases away
    /// from 0.0.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// assert_eq!(Vec2::new(0.3, 1.3).round(), Vec2::new(0.0, 1.0))
    /// ```
    pub fn round(&self) -> Self {
        Vec2::new(self.x.round(), self.y.round())
    }
}

impl<T: num::traits::Num + Copy> Vec2<T> {
    /// dot returns the dot product of self and b.
    pub fn dot(self, b: Self) -> T {
        self.x*b.x + self.y*b.y
    }
}

impl<T: num::traits::Num + Copy> LengthSq<T> for Vec2<T> {
    fn length_sq(self) -> T { self.dot(self) }
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

impl<T: Neg<Output = T>> Neg for Vec2<T>{
    type Output = Self;

    /// neg returns the negated (i.e. inversed) vector self.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// assert_eq!(-Vec2::new(1, 2), Vec2::new(-1, -2));
    /// ```
    fn neg(self) -> Self {
        Vec2{x: -self.x, y: -self.y}
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

impl<T: Clamp<Elem = T> + Copy> Clamp for Vec2<T>{
    type Elem = T;

    /// clamp returns the vector with each element clamped to the range of
    /// [min, max].
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::{Vec2, Clamp};
    ///
    /// let a = Vec2::new(-2, 4);
    /// assert_eq!(a.clamp(-1, 2), Vec2::new(-1, 2));
    /// ```
    fn clamp(self, min: T, max: T) -> Self {
        Vec2{
            x: self.x.clamp(min, max),
            y: self.y.clamp(min, max),
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

impl<T: PartialEq> PartialEq for Vec2<T> {
    /// eq tests for component-wise binary equality of two vectors.
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
    ///
    /// ```
    /// use fiz_math::Vec2;
    ///
    /// let a = Vec2::new(4, 5);
    /// let b = Vec2::new(4, 5);
    /// assert_eq!(a, b);
    /// ```
    fn eq(&self, _rhs: &Self) -> bool {
        self.x == _rhs.x &&
        self.y == _rhs.y
    }
}

impl<T: PartialOrd> PartialOrd for Vec2<T>{
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

impl<T: Zero> Zero for Vec2<T>{
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
        self.x.is_zero() &&
        self.y.is_zero()
    }
}
