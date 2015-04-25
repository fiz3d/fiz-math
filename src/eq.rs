extern crate num;

use num::Float;

/// The default epsilon value used for floating point comparisons.
pub static EPSILON:f64 = 1.0E-8;

/// almost_equal tells if the two floating-point values x and y are considered
/// equal within the specified absolute == relative tolerence value.
///
/// This method of comparison used is described online at:
///
/// http://realtimecollisiondetection.net/blog/?p=89
///
/// Also see is_equal which uses a predefined EPSILON value for tolerence.
///
/// # Examples
///
/// ```
/// assert!(fiz_math::almost_equal(0.9, 1.0, 0.1000001));
/// assert!(fiz_math::almost_equal(0.9, 1.0, 0.1));
/// ```
pub fn almost_equal<T: Float>(x: T, y: T, abs_tol: T) -> bool {
  let r = T::from(1.0).unwrap().max(x.abs().max(y.abs()));
  x == y || ((x-y).abs() <= abs_tol * r)
}

/// equal tells if the two floating-point values x and y are considered equal
/// within the EPSILON absolute == relative tolerence value, via is_almost_equal.
///
/// # Examples
///
/// ```
/// use fiz_math::equal;
///
/// assert!(fiz_math::equal(1.00000001, 1.0));
/// assert!(fiz_math::equal(1.0, 1.0));
/// assert!(!fiz_math::equal(0.9, 1.0));
/// ```
pub fn equal<T: Float>(x: T, y: T) -> bool {
  almost_equal(x, y, T::from(EPSILON).unwrap())
}

#[cfg(test)]
mod test {
    #[test]
    fn equal() {
      assert!(super::equal(1.0_f32, 1.0_f32))
    }

    #[test]
    fn almost_equal() {
      assert!(super::almost_equal(1.0_f32, 1.0_f32, 0.01))
    }
}
