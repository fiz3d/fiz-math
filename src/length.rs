use num::traits::{Num, Float};

pub trait LengthSq<T: Num+Copy> {
	/// length_sq returns the magnitude squared of this vector, useful primarily
	/// for comparing distances.
	///
	/// # Examples
	///
	/// ```
	/// use fiz_math::{Vec4, LengthSq};
	///
	/// assert_eq!(Vec4::new(1, 2, 3, 4).length_sq(), 30);
	/// ```
	fn length_sq(self) -> T;
}

pub trait Length<T: Float> {
	/// length returns the magnitude of this vector. Use LengthSq instead when
	/// comparing distances, because it avoids the extra sqrt operation needed
	/// by this method.
	///
	/// # Examples
	///
	/// ```
	/// use fiz_math::{Vec4, Length, Float};
	///
	/// let l = Vec4::new(1.0, 2.0, 3.0, 4.0).length();
	/// assert!(l.equal(5.47722557));
	/// ```
	fn length(self) -> T;
}

impl<F, L> Length<F> for L where F: Float, L: LengthSq<F> {
	fn length(self) -> F { self.length_sq().sqrt() }
}
