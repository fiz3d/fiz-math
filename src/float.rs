extern crate num;

use std::f64;
use clamp::Clamp;

/// The default epsilon value used for floating point comparisons.
pub static EPSILON:f64 = 1.0E-8;

pub trait Float: num::Float{
    /// Tells if the two floating-point values `self` and `y` are considered equal
    /// within the specified `absolute == relative` tolerence value.
    ///
    /// The method of comparison used is described at:
    ///
    /// http://realtimecollisiondetection.net/blog/?p=89
    ///
    /// Also consider using the `equal` method.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Float;
    ///
    /// assert!(0.9.almost_equal(1.0, 0.1000001));
    /// assert!(0.9.almost_equal(1.0, 0.1));
    /// ```
    fn almost_equal(self, y: Self, abs_tol: Self) -> bool;

    /// equal is short-hand for `self.almost_equal(y, fiz_math::EPSILON)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Float;
    ///
    /// assert!(1.00000001.equal(1.0));
    /// assert!(1.0.equal(1.0));
    /// assert!(!0.9.equal(1.0));
    /// ```
    fn equal(self, y: Self) -> bool;

    /// radians converts the value `self` (presumed to be in degrees) to radians.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Float;
    /// use std::f64::consts::PI;
    ///
    /// assert_eq!(180.0.radians(), PI);
    /// assert_eq!(360.0.radians(), PI * 2.0);
    /// ```
    fn radians(self) -> Self;

    /// degrees converts the value `self` (presumed to be in radians) to degrees.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Float;
    /// use std::f64::consts::PI;
    ///
    /// assert_eq!(PI.degrees(), 180.0);
    /// assert_eq!((PI*2.0).degrees(), 360.0);
    /// ```
    fn degrees(self) -> Self;

    /// lerp performs a linear interpolation between `self` and `b`. The `t`
    /// parameter is a number in the range 0.0 - 1.0.
    ///
    /// The interpolation method is precise, as such it is guaranteed that
    /// `a.lerp(b, 1.0) == a`.
    ///
    /// # Examples
    ///
    /// ```
    /// use fiz_math::Float;
    ///
    /// assert_eq!(0.0.lerp(10.0, 0.0), 0.0);
    /// assert_eq!(0.0.lerp(10.0, 0.5), 5.0);
    /// assert_eq!(0.0.lerp(10.0, 1.0), 10.0);
    /// ```
    fn lerp(self, b: Self, t: Self) -> Self;
}

impl<T: num::Float> Float for T {
    fn almost_equal(self, y: T, abs_tol: T) -> bool {
        let r = T::from(1.0).unwrap().max(self.abs().max(y.abs()));
        self == y || ((self-y).abs() <= abs_tol * r)
    }

    fn equal(self, y: T) -> bool {
        self.almost_equal(y, T::from(EPSILON).unwrap())
    }

    fn radians(self) -> Self {
        T::from(f64::consts::PI).unwrap() * self / T::from(180.0).unwrap()
    }

    fn degrees(self) -> Self {
        self * T::from(180.0 / f64::consts::PI).unwrap()
    }

    fn lerp(self, b: Self, t: Self) -> Self {
        (T::one()-t)*self + t*b
    }
}
