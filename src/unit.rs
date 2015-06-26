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
///     println!("We've collected {:?} golden coins!", coins.v);
/// }
///
/// fn main() {
///     let x = GoldCoins::new(5);
///     collect(x);
///
///     let y = SilverCoins::new(6);
///
///     // Try uncommenting the line below and see:
///     //
///     // error: mismatched types: expected `GoldCoins<_>`, found `SilverCoins<_>`"
///     //
///     //collect(y);
///
///     // add, subtract, multiply, divide:
///     assert_eq!(y + SilverCoins::new(4), SilverCoins::new(10));
///     assert_eq!(y - SilverCoins::new(3), SilverCoins::new(3));
///     assert_eq!(y * SilverCoins::new(3), SilverCoins::new(18));
///     assert_eq!(y / SilverCoins::new(2), SilverCoins::new(3));
///
///     // ordering and equality:
///     assert!(y < SilverCoins::new(7));
///     assert!(y > SilverCoins::new(5));
///     assert!(y <= SilverCoins::new(6));
///     assert!(y >= SilverCoins::new(6));
///     assert!(y == SilverCoins::new(6));
/// }
/// ```
///
#[macro_export]
macro_rules! unit {
    ( $ident:ident ) => {
        #[derive(Copy, Clone, Debug)]
        pub struct $ident<T>{
            pub v: T,
        }

        // new
        impl<T> $ident<T> {
            pub fn new(v: T) -> Self {
                $ident{v: v}
            }
        }

        // addition
        impl<T: ::std::ops::Add<Output = T>> ::std::ops::Add for $ident<T> {
            type Output = Self;

            fn add(self, _rhs: Self) -> Self {
                $ident{v: self.v + _rhs.v}
            }
        }

        // subtraction
        impl<T: ::std::ops::Sub<Output = T>> ::std::ops::Sub for $ident<T> {
            type Output = Self;

            fn sub(self, _rhs: Self) -> Self {
                $ident{v: self.v - _rhs.v}
            }
        }

        // multiplication
        impl<T: ::std::ops::Mul<Output = T>> ::std::ops::Mul for $ident<T> {
            type Output = Self;

            fn mul(self, _rhs: Self) -> Self {
                $ident{v: self.v * _rhs.v}
            }
        }

        // division
        impl<T: ::std::ops::Div<Output = T>> ::std::ops::Div for $ident<T> {
            type Output = Self;

            fn div(self, _rhs: Self) -> Self {
                $ident{v: self.v / _rhs.v}
            }
        }

        // partial equality
        impl<T: ::std::cmp::PartialEq> ::std::cmp::PartialEq for $ident<T> {
            fn eq(&self, _rhs: &Self) -> bool {
                self.v == _rhs.v
            }
        }

        // equality
        impl<T: ::std::cmp::Eq> ::std::cmp::Eq for $ident<T> {}

        // partial ordering
        impl<T: ::std::cmp::PartialOrd> ::std::cmp::PartialOrd for $ident<T> {
            fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
                if self.v < other.v {
                    Some(::std::cmp::Ordering::Less)
                } else if self.v > other.v {
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
                if self.v < other.v {
                    ::std::cmp::Ordering::Less
                } else if self.v > other.v {
                    ::std::cmp::Ordering::Greater
                } else {
                    ::std::cmp::Ordering::Equal
                }
            }
        }
    };
}
