use num::traits::Num;
use length::LengthSq;

pub trait Dot<T: Num> {
	/// dot returns the dot product of self and b. For length calculations use
	/// Length or LengthSq traits instead (for clarity).
	///
	/// # Examples
	///
	/// ```
	/// use fiz_math::{Vec4, Dot};
	///
	/// let x = Vec4::new(1, 2, 3, 4);
	/// assert_eq!(x.dot(x), 30);
	/// ```
	fn dot(self, b: Self) -> T;
}

impl<N, D> LengthSq<N> for D where N: Num+Copy, D: Dot<N>+Copy {
	fn length_sq(self) -> N { self.dot(self) }
}
