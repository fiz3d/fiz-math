/// unit creates a type representing a single unit.
///
/// # Examples
///
/// ```
/// #[macro_use(unit)]
/// extern crate fiz_math;
/// use std::fmt::Debug;
///
/// // GoldCoins are golden!
/// unit!(GoldCoins);
///
/// // SilverCoins are like gold coins, only worse!
/// unit!(SilverCoins);
///
/// fn collect<T: Debug>(coins: GoldCoins<T>) {
///     println!("We've collected {:?} golden coins!", coins.0);
/// }
///
/// fn main() {
///     let x = GoldCoins(5);
///     collect(x);
///
///     let y = SilverCoins(6);
///
///     // Try uncommenting the line below and see:
///     //
///     // error: mismatched types: expected `GoldCoins<_>`, found `SilverCoins<_>`"
///     //
///     //collect(y);
///
///     // add, subtract, multiply, divide:
///     assert_eq!(y + SilverCoins(4), SilverCoins(10));
///     assert_eq!(y - SilverCoins(3), SilverCoins(3));
///     assert_eq!(y * SilverCoins(3), SilverCoins(18));
///     assert_eq!(y / SilverCoins(2), SilverCoins(3));
///
///     // ordering and equality:
///     assert!(y < SilverCoins(7));
///     assert!(y > SilverCoins(5));
///     assert!(y <= SilverCoins(6));
///     assert!(y >= SilverCoins(6));
///     assert!(y == SilverCoins(6));
/// }
/// ```
///
#[macro_export]
macro_rules! unit {
    ( $ident:ident ) => {
        #[derive(Copy, Clone, Debug)]
        pub struct $ident<T>(pub T);

        unit!(impl_std_ops, $ident);
        unit!(impl_std_cmp, $ident);
        unit!(impl_num_traits, $ident);
    };

    (impl_std_ops, $ident:ident ) => {
        // addition
        impl<T: ::std::ops::Add<Output = T>> ::std::ops::Add for $ident<T> {
            type Output = Self;

            fn add(self, _rhs: Self) -> Self {
                $ident(self.0 + _rhs.0)
            }
        }

        // subtraction
        impl<T: ::std::ops::Sub<Output = T>> ::std::ops::Sub for $ident<T> {
            type Output = Self;

            fn sub(self, _rhs: Self) -> Self {
                $ident(self.0 - _rhs.0)
            }
        }

        // multiplication
        impl<T: ::std::ops::Mul<Output = T>> ::std::ops::Mul for $ident<T> {
            type Output = Self;

            fn mul(self, _rhs: Self) -> Self {
                $ident(self.0 * _rhs.0)
            }
        }

        // division
        impl<T: ::std::ops::Div<Output = T>> ::std::ops::Div for $ident<T> {
            type Output = Self;

            fn div(self, _rhs: Self) -> Self {
                $ident(self.0 / _rhs.0)
            }
        }

        // remainder
        impl<T: ::std::ops::Rem<Output = T>> ::std::ops::Rem for $ident<T> {
            type Output = Self;

            fn rem(self, rhs: Self) -> Self { $ident(self.0 % rhs.0) }
        }

        // negation
        impl<T: ::std::ops::Neg<Output = T>> ::std::ops::Neg for $ident<T> {
            type Output = Self;

            fn neg(self) -> Self::Output { $ident(-self.0) }
        }

        // not
        impl<T: ::std::ops::Not<Output = T>> ::std::ops::Not for $ident<T> {
            type Output = Self;

            fn not(self) -> Self::Output { $ident(!self.0) }
        }

        // bitwise and
        impl<T: ::std::ops::BitAnd<Output = T>> ::std::ops::BitAnd for $ident<T> {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self::Output { $ident(self.0 & rhs.0) }
        }

        // bitwise or
        impl<T: ::std::ops::BitOr<Output = T>> ::std::ops::BitOr for $ident<T> {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self::Output { $ident(self.0 | rhs.0) }
        }

        // bitwise xor
        impl<T: ::std::ops::BitXor<Output = T>> ::std::ops::BitXor for $ident<T> {
            type Output = Self;

            fn bitxor(self, rhs: Self) -> Self::Output { $ident(self.0 ^ rhs.0) }
        }

        // shift left
        impl<T: ::std::ops::Shl<usize>> ::std::ops::Shl<usize> for $ident<T> {
            type Output = $ident<T::Output>;

            fn shl(self, rhs: usize) -> Self::Output { $ident(self.0 << rhs) }
        }

        // shift right
        impl<T: ::std::ops::Shr<usize>> ::std::ops::Shr<usize> for $ident<T> {
            type Output = $ident<T::Output>;

            fn shr(self, rhs: usize) -> Self::Output { $ident(self.0 >> rhs) }
        }
    };

    (impl_std_cmp, $ident:ident ) => {
        // partial equality
        impl<T: ::std::cmp::PartialEq> ::std::cmp::PartialEq for $ident<T> {
            fn eq(&self, _rhs: &Self) -> bool {
                self.0 == _rhs.0
            }
        }

        // equality
        impl<T: ::std::cmp::Eq> ::std::cmp::Eq for $ident<T> {}

        // partial ordering
        impl<T: ::std::cmp::PartialOrd> ::std::cmp::PartialOrd for $ident<T> {
            fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
                if self.0 < other.0 {
                    Some(::std::cmp::Ordering::Less)
                } else if self.0 > other.0 {
                    Some(::std::cmp::Ordering::Greater)
                } else if self == other {
                    Some(::std::cmp::Ordering::Equal)
                } else {
                    None
                }
            }
        }

        // total ordering
        impl<T: ::std::cmp::Ord> ::std::cmp::Ord for $ident<T> {
            fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
                if self.0 < other.0 {
                    ::std::cmp::Ordering::Less
                } else if self.0 > other.0 {
                    ::std::cmp::Ordering::Greater
                } else {
                    ::std::cmp::Ordering::Equal
                }
            }
        }
    };

    (impl_num_traits, $ident:ident ) => {
        impl<T: $crate::num_export::traits::Zero> $crate::num_export::traits::Zero for $ident<T> {
            fn zero() -> Self { $ident(T::zero()) }
            fn is_zero(&self) -> bool { self.0.is_zero() }
        }

        impl<T: $crate::num_export::traits::One> $crate::num_export::traits::One for $ident<T> {
            fn one() -> Self { $ident(T::one()) }
        }

        impl<T: $crate::num_export::traits::Num> $crate::num_export::traits::Num for $ident<T> {
            type FromStrRadixErr = T::FromStrRadixErr;
            fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                match T::from_str_radix(str, radix) {
                    Ok(x) => { Ok($ident(x)) }
                    Err(e) => { Err(e) }
                }
            }
        }

        impl<T: $crate::num_export::traits::ToPrimitive> $crate::num_export::traits::ToPrimitive for $ident<T> {
            fn to_i64(&self) -> Option<i64> { self.0.to_i64() }
            fn to_u64(&self) -> Option<u64> { self.0.to_u64() }
            fn to_isize(&self) -> Option<isize> { self.0.to_isize() }
            fn to_i8(&self) -> Option<i8> { self.0.to_i8() }
            fn to_i16(&self) -> Option<i16> { self.0.to_i16() }
            fn to_i32(&self) -> Option<i32> { self.0.to_i32() }
            fn to_usize(&self) -> Option<usize> { self.0.to_usize() }
            fn to_u8(&self) -> Option<u8> { self.0.to_u8() }
            fn to_u16(&self) -> Option<u16> { self.0.to_u16() }
            fn to_u32(&self) -> Option<u32> { self.0.to_u32() }
            fn to_f32(&self) -> Option<f32> { self.0.to_f32() }
            fn to_f64(&self) -> Option<f64> { self.0.to_f64() }
        }

        impl<T: $crate::num_export::traits::NumCast> $crate::num_export::traits::NumCast for $ident<T> {
            fn from<X: $crate::num_export::traits::ToPrimitive>(n: X) -> Option<Self> {
                match T::from(n) {
                    Some(x) => { Some($ident(x)) }
                    None => { None }
                }
            }
        }
    };
}
