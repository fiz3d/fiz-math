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
}
