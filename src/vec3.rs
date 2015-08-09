#![allow(dead_code)]

use std::ops::{Add, Sub, Mul, Div};
use std::cmp::{PartialEq, PartialOrd, Ordering};
pub use num::{Zero, One};
use num;
use super::float::Float;
use std::fmt;
use clamp::Clamp;

/// Vec3 is a generic three-component (3D) vector type.
#[derive(Copy, Clone, Debug)]
pub struct Vec3<T>{
    x: T,
    y: T,
    z: T
}

impl<T> Vec3<T>{
    /// new returns a new vector with the given parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = fiz_math::Vec3::new(4.0f32, 8.0f32, 2.0f32);
    /// println!("{:?}", x);
    /// ```
    ///
    /// ```
    /// let x = fiz_math::Vec3::new(1u8, 5u8, 2u8);
    /// println!("{:?}", x);
    /// ```
    ///
    /// ```
    /// use fiz_math::Vec3;
    /// use fiz_math::unit::MM;
    ///
    /// let x = Vec3::new(MM(1.0), MM(5.0), MM(2.0));
    /// let y = Vec3::new(MM(1.0), MM(5.1), MM(1.9));
    /// assert!(x.almost_equal(y, 0.1));
    /// ```
    pub fn new(x: T, y: T, z: T) -> Self {
        Vec3{x: x, y: y, z: z}
    }
}

/// Point3 is a generic three-component (3D) point type.
///
/// # Examples
///
/// ```
/// use fiz_math::Point3;
///
/// let p = Point3::new(1.0, 2.0, 3.0);
/// assert_eq!(p + p, Point3::new(2.0, 4.0, 6.0))
/// ```
pub type Point3<T> = Vec3<T>;

impl<T: fmt::Display> fmt::Display for Vec3<T> {
    /// fmt formats the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = fiz_math::Vec3::new(1u8, 5u8, 2u8);
    /// assert_eq!(format!("{}", x), "Vec3(1, 5, 2)");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Vec3({}, {}, {})", self.x, self.y, self.z)
    }
}

impl<T: One> One for Vec3<T>{
    /// one returns the one value for a vector whose component type implements the
    /// num::One trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::One;
    ///
    /// let x = fiz_math::Vec3::<f32>::one();
    /// ```
    ///
    /// ```
    /// use fiz_math::One;
    ///
    /// let x = fiz_math::Vec3::<i64>::one();
    /// ```
    fn one() -> Self {
        Vec3{x: T::one(), y: T::one(), z: T::one()}
    }
}

impl<T: Float> Vec3<T>{
    /// almost_equal tells if this vector is equal to the other given an absolute
    /// tolerence value (see the almost_equal function for more details).
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::<f32>::new(1.0, 1.0, 1.0);
    /// let b = Vec3::<f32>::new(0.9, 0.9, 0.9);
    /// assert!(a.almost_equal(b, 0.1000001));
    /// assert!(!a.almost_equal(b, 0.1));
    /// ```
    pub fn almost_equal<N: num::Float>(self, other: Self, abs_tol: N) -> bool {
        self.x.almost_equal(other.x, abs_tol) &&
        self.y.almost_equal(other.y, abs_tol) &&
        self.z.almost_equal(other.z, abs_tol)
    }

    /// is_nan tells if all of this vectors components are NaN.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate num;
    /// # extern crate fiz_math;
    /// use num::traits::Float;
    /// use fiz_math::Vec3;
    ///
    /// # fn main() {
    /// let n:f32 = Float::nan();
    /// assert!(Vec3::new(n, n, n).is_nan());
    /// assert!(!Vec3::new(n, 0.0, 0.0).is_nan());
    /// # }
    /// ```
    pub fn is_nan(self) -> bool {
        self.x.is_nan() &&
        self.y.is_nan() &&
        self.z.is_nan()
    }
}

impl<T: Add<Output = T>> Add for Vec3<T>{
    type Output = Vec3<T>;

    /// add performs component-wise addition of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(1, 2, 3);
    /// let b = Vec3::new(4, 5, 6);
    /// assert_eq!(a + b, Vec3::new(5, 7, 9));
    /// ```
    fn add(self, _rhs: Self) -> Self {
        Vec3{
            x: self.x + _rhs.x,
            y: self.y + _rhs.y,
            z: self.z + _rhs.z,
        }
    }
}

impl<T: Add<Output = T> + Copy> Vec3<T> {
    /// add_scalar performs scalar addition on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(1, 2, 3);
    /// assert_eq!(a.add_scalar(1), Vec3::new(2, 3, 4));
    /// ```
    pub fn add_scalar(self, _rhs: T) -> Self {
        Vec3{
            x: self.x + _rhs,
            y: self.y + _rhs,
            z: self.z + _rhs,
        }
    }
}

impl<T: Sub<Output = T>> Sub for Vec3<T>{
    type Output = Self;

    /// sub performs component-wise subtraction of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(1, 2, 3);
    /// let b = Vec3::new(4, 5, 6);
    /// assert_eq!(a - b, Vec3::new(-3, -3, -3));
    /// ```
    fn sub(self, _rhs: Self) -> Self {
        Vec3{
            x: self.x - _rhs.x,
            y: self.y - _rhs.y,
            z: self.z - _rhs.z,
        }
    }
}

impl<T: Sub<Output = T> + Copy> Vec3<T> {
    /// sub_scalar performs scalar subtraction on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(2, 3, 4);
    /// assert_eq!(a.sub_scalar(1), Vec3::new(1, 2, 3));
    /// ```
    pub fn sub_scalar(self, _rhs: T) -> Self {
        Vec3{
            x: self.x - _rhs,
            y: self.y - _rhs,
            z: self.z - _rhs,
        }
    }
}

impl<T: Mul<Output = T>> Mul for Vec3<T>{
    type Output = Self;

    /// mul performs component-wise multiplication of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(1, 2, 3);
    /// let b = Vec3::new(4, 5, 6);
    /// assert_eq!(a * b, Vec3::new(4, 10, 18));
    /// ```
    fn mul(self, _rhs: Self) -> Self {
        Vec3{
            x: self.x * _rhs.x,
            y: self.y * _rhs.y,
            z: self.z * _rhs.z,
        }
    }
}

impl<T: Mul<Output = T> + Copy> Vec3<T> {
    /// mul_scalar performs scalar multiplication on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(1, 2, 3);
    /// assert_eq!(a.mul_scalar(2), Vec3::new(2, 4, 6));
    /// ```
    pub fn mul_scalar(self, _rhs: T) -> Self {
        Vec3{
            x: self.x * _rhs,
            y: self.y * _rhs,
            z: self.z * _rhs,
        }
    }
}

impl<T: Div<Output = T>> Div for Vec3<T>{
    type Output = Vec3<T>;

    /// div performs component-wise division of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(4, 5, 9);
    /// let b = Vec3::new(1, 2, 3);
    /// assert_eq!(a / b, Vec3::new(4, 2, 3));
    /// ```
    fn div(self, _rhs: Self) -> Self {
        Vec3{
            x: self.x / _rhs.x,
            y: self.y / _rhs.y,
            z: self.z / _rhs.z,
        }
    }
}

impl<T: Div<Output = T> + Copy> Vec3<T> {
    /// div_scalar performs scalar division on a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(2, 4, 6);
    /// assert_eq!(a.div_scalar(2), Vec3::new(1, 2, 3));
    /// ```
    pub fn div_scalar(self, _rhs: T) -> Self {
        Vec3{
            x: self.x / _rhs,
            y: self.y / _rhs,
            z: self.z / _rhs,
        }
    }
}

impl<T: Clamp<Elem = T> + Copy> Clamp for Vec3<T>{
    type Elem = T;

    /// clamp returns the vector with each element clamped to the range of
    /// [min, max].
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::{Vec3, Clamp};
    ///
    /// let a = Vec3::new(-2, 4, -6);
    /// assert_eq!(a.clamp(-1, 2), Vec3::new(-1, 2, -1));
    /// ```
    fn clamp(self, min: T, max: T) -> Self {
        Vec3{
            x: self.x.clamp(min, max),
            y: self.y.clamp(min, max),
            z: self.z.clamp(min, max),
        }
    }
}

impl<T> AsRef<Vec3<T>> for Vec3<T> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T:PartialOrd> Vec3<T> {
    /// any_less tells if any component of the other vector is less than any
    /// component of this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(0, 0, 1);
    /// assert!(a.any_less(Vec3::new(0, 0, 2)));
    /// ```
    pub fn any_less<O:AsRef<Self>>(&self, other: O) -> bool {
        let o = other.as_ref();
        self.x < o.x || self.y < o.y || self.z < o.z
    }

    /// any_greater tells if any component of the other vector is greater than
    /// any component of this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(0, 0, 2);
    /// assert!(a.any_greater(Vec3::new(0, 0, 1)));
    /// ```
    pub fn any_greater<O:AsRef<Self>>(&self, other: O) -> bool {
        let o = other.as_ref();
        self.x > o.x || self.y > o.y || self.z > o.z
    }
}

impl<T: PartialEq> PartialEq for Vec3<T> {
    /// eq tests for component-wise binary equality of two vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(4.0, 5.0, 9.0);
    /// let b = Vec3::new(4.0, 5.0, 9.00000000000000000000001);
    /// assert_eq!(a, b);
    /// ```
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(4, 5, 9);
    /// let b = Vec3::new(4, 5, 9);
    /// assert_eq!(a, b);
    /// ```
    fn eq(&self, _rhs: &Self) -> bool {
        self.x == _rhs.x &&
        self.y == _rhs.y &&
        self.z == _rhs.z
    }
}

impl<T: PartialOrd> PartialOrd for Vec3<T>{
    /// partial_cmp compares the two vectors component-wise.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Vec3;
    ///
    /// let a = Vec3::new(1.0, 2.0, 3.0);
    /// assert!(a < Vec3::new(1.1, 2.1, 3.1));
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.x < other.x && self.y < other.y && self.z < other.z {
            Some(Ordering::Less)
        } else if self.x > other.x && self.y > other.y && self.z > other.z {
            Some(Ordering::Greater)
        } else if self == other {
            Some(Ordering::Equal)
        } else {
            None
        }
    }
}

impl<T: Zero> Zero for Vec3<T>{
    /// zero returns the zero-value for the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::{Zero, Vec3};
    ///
    /// let x = Vec3::<u8>::zero();
    /// let y = Vec3::<i64>::zero();
    /// let z = Vec3::<f32>::zero();
    /// let w = Vec3::<f64>::zero();
    /// ```
    fn zero() -> Self {
        Vec3{x: Zero::zero(), y: Zero::zero(), z: Zero::zero()}
    }

    /// is_zero tests if the vector is equal to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::{Zero, Vec3};
    ///
    /// assert!(!Vec3::new(1i32, 0, 0).is_zero());
    /// assert!(Vec3::new(0u8, 0, 0).is_zero());
    /// assert!(!Vec3::new(1.0f32, 0.0, 0.0).is_zero());
    /// assert!(Vec3::new(0.0f64, 0.0, 0.0).is_zero());
    /// ```
    fn is_zero(&self) -> bool {
        self.x.is_zero() &&
        self.y.is_zero() &&
        self.z.is_zero()
    }
}
