use super::vec2::Point2;
use super::vec3::Vec3;

/*
package lmath

import (
	"fmt"
	"math"
)

// CoordSys represents an specific coordinate system.
type CoordSys uint8

// RightHanded tells whether this coordinate system is right-handed.
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) RightHanded() bool {
	switch c {
	case CoordSysZUpRight:
		return true
	case CoordSysYUpRight:
		return true

	case CoordSysZUpLeft:
		return false
	case CoordSysYUpLeft:
		return false
	}
	panic(fmt.Sprintf("RightHanded(): Invalid coordinate system %d", c))
}

// LeftHanded is short for:
//  !cs.RightHanded()
func (c CoordSys) LeftHanded() bool {
	return !c.RightHanded()
}

const (
	// Invalid coordinate system
	CoordSysInvalid CoordSys = iota

	// Z up axis, right handed coordinate system
	CoordSysZUpRight

	// Y up axis, right handed coordinate system
	CoordSysYUpRight

	// Z up axis, left handed coordinate system
	CoordSysZUpLeft

	// Y up axis, left handed coordinate system
	CoordSysYUpLeft
)

// Up returns the up vector for the given coordinate system
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) Up() Vec3 {
	switch c {
	case CoordSysZUpRight:
		return Vec3{0, 0, 1}
	case CoordSysZUpLeft:
		return Vec3{0, 0, 1}

	case CoordSysYUpRight:
		return Vec3{0, 1, 0}
	case CoordSysYUpLeft:
		return Vec3{0, 1, 0}
	}
	panic(fmt.Sprintf("Up(): Invalid coordinate system %d", c))
}

// Right returns the right vector for the given coordinate system
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) Right() Vec3 {
	return Vec3{1, 0, 0}
}

// Forward returns the forward vector for the given coordinate system
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) Forward() Vec3 {
	switch c {
	case CoordSysZUpRight:
		return Vec3{0, 1, 0}

	case CoordSysZUpLeft:
		return Vec3{0, -1, 0}

	case CoordSysYUpRight:
		return Vec3{0, 0, -1}

	case CoordSysYUpLeft:
		return Vec3{0, 0, 1}
	}
	panic(fmt.Sprintf("Forward(): Invalid coordinate system %d", c))
}

// Down returns the down vector for the given coordinate system
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) Down() Vec3 {
	return c.Up().Inverse()
}

// Left returns the left vector for the given coordinate system
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) Left() Vec3 {
	return c.Right().Inverse()
}

// Back returns the back vector for the given coordinate system
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) Back() Vec3 {
	return c.Forward().Inverse()
}

// RightFrontUp returns an vector that is described by it's right, forward, and
// up components in whatever way the specified coordinate system represents
// that vector.
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) RightFrontUp(right, forward, up float64) Vec3 {
	var vz, vy float64

	switch c {
	case CoordSysYUpRight:
		vz = -forward
		vy = up

	case CoordSysYUpLeft:
		vz = forward
		vy = up

	case CoordSysZUpRight:
		vy = forward
		vz = up

	case CoordSysZUpLeft:
		vy = -forward
		vz = up

	default:
		panic(fmt.Sprintf("Forward(): Invalid coordinate system %d", c))
	}
	return Vec3{right, vy, vz}
}

// ConvertMat3 returns a matrix that transforms from the indicated coordinate
// system, to the coordinate system specified.
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) ConvertMat3(to CoordSys) Mat3 {
	switch c {
	case CoordSysZUpLeft:
		switch to {
		case CoordSysZUpLeft:
			return Mat3Identity
		case CoordSysYUpLeft:
			return Mat3ZToYUp
		case CoordSysZUpRight:
			return Mat3FlipY
		case CoordSysYUpRight:
			return Mat3LZToRY
		}

	case CoordSysYUpLeft:
		switch to {
		case CoordSysZUpLeft:
			return Mat3YToZUp
		case CoordSysYUpLeft:
			return Mat3Identity
		case CoordSysZUpRight:
			return Mat3LYToRZ
		case CoordSysYUpRight:
			return Mat3FlipZ
		}

	case CoordSysZUpRight:
		switch to {
		case CoordSysZUpLeft:
			return Mat3FlipY
		case CoordSysYUpLeft:
			return Mat3LZToRY
		case CoordSysZUpRight:
			return Mat3Identity
		case CoordSysYUpRight:
			return Mat3ZToYUp
		}

	case CoordSysYUpRight:
		switch to {
		case CoordSysZUpLeft:
			return Mat3LYToRZ
		case CoordSysYUpLeft:
			return Mat3FlipZ
		case CoordSysZUpRight:
			return Mat3YToZUp
		case CoordSysYUpRight:
			return Mat3Identity
		}
	}
	panic(fmt.Sprintf("ConvertMat3(): Invalid coordinate system %d / %d", c, to))
}

// ConvertMat4 returns a matrix that transforms from the indicated coordinate
// system, to the coordinate system specified.
// A panic will occur if the coordinate system is invalid.
func (c CoordSys) ConvertMat4(to CoordSys) Mat4 {
	switch c {
	case CoordSysZUpLeft:
		switch to {
		case CoordSysZUpLeft:
			return Mat4Identity
		case CoordSysYUpLeft:
			return Mat4ZToYUp
		case CoordSysZUpRight:
			return Mat4FlipY
		case CoordSysYUpRight:
			return Mat4LZToRY
		}

	case CoordSysYUpLeft:
		switch to {
		case CoordSysZUpLeft:
			return Mat4YToZUp
		case CoordSysYUpLeft:
			return Mat4Identity
		case CoordSysZUpRight:
			return Mat4LYToRZ
		case CoordSysYUpRight:
			return Mat4FlipZ
		}

	case CoordSysZUpRight:
		switch to {
		case CoordSysZUpLeft:
			return Mat4FlipY
		case CoordSysYUpLeft:
			return Mat4LZToRY
		case CoordSysZUpRight:
			return Mat4Identity
		case CoordSysYUpRight:
			return Mat4ZToYUp
		}

	case CoordSysYUpRight:
		switch to {
		case CoordSysZUpLeft:
			return Mat4LYToRZ
		case CoordSysYUpLeft:
			return Mat4FlipZ
		case CoordSysZUpRight:
			return Mat4YToZUp
		case CoordSysYUpRight:
			return Mat4Identity
		}
	}
	panic(fmt.Sprintf("ConvertMat4(): Invalid coordinate system %d / %d", c, to))
}*/

/// sphere_to_cart converts the given (inclination, azimuth) point on a sphere
/// of the given radius to cartesian coordinates.
///
/// It is implemented according to:
///
/// http://en.wikipedia.org/wiki/Spherical_coordinate_system#Cartesian_coordinates
fn sphere_to_cart<T: Float>(r: T, p: Point2<T>) -> Vec3<T> {
    Vec3{
        x: r * p.x.sin() * p.y.cos(),
        y: r * p.x.sin() * p.y.sin(),
        z: r * p.x.cos(),
    }
}

/// cart_to_sphere converts the given point p in the cartesian coordinate space
/// into spherical coordinates in the form of (radius, inclination, azimuth).
///
/// It is implemented according to:
///
/// http://en.wikipedia.org/wiki/Spherical_coordinate_system#Cartesian_coordinates
fn cart_to_sphere<T: Float>(p: Vec3<T>) -> Vec3<T> {
    let r = p.length();
    let i = (p.z / r).acos();
    let a = (p.y / p.x).atan();
    Vec3::new(r, i, a)
}
