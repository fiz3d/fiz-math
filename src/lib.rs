extern crate num;

mod vec3;
mod vec4;
mod eq;

pub use num::{Zero, One};
pub use self::vec3::{Vec3};
pub use self::vec4::{Vec4};
pub use self::eq::*;
