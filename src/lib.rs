extern crate num;

// Must re-export num for the unit! macro.
#[doc(hidden)]pub use num as num_export;

mod vec2;
mod vec3;
mod vec4;
mod float;
mod clamp;
#[macro_use] pub mod unit;

pub use num::{Zero, One, Num};
pub use self::vec2::{Vec2, Point2};
pub use self::vec3::{Vec3, Point3};
pub use self::vec4::Vec4;
pub use self::float::{EPSILON, Float};
pub use self::clamp::Clamp;
