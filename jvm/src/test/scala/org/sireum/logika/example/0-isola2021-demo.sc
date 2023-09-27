// #Sireum #Logika
//@Logika: --background type
import org.sireum._


// @datatype is an immutable user-defined type
@datatype class WayPoint(val x: Z, val y: Z, val z: Z)

// MSZ is a mutable sequence indexed by Z (arbitrary-precision integer)
val s1 = MSZ(WayPoint(30, 30, 50), WayPoint(84, -20, 92))
val s2 = s1 // assigning a mutable type makes a deep copy
println("s1 = ", s1, ", s2 = ", s2)

s2(0) = WayPoint(1, 2, 3) // destructively updating s2's first element
println("s1 = ", s1, ", s2 = ", s2)

assert(s2(0) == WayPoint(1, 2, 3))
assert(s1(0) == WayPoint(30, 30, 50))
println("s1 = ", s1, ", s2 = ", s2)

@strictpure def inZone(wayPoint: WayPoint): B =
  -100 <= wayPoint.x & wayPoint.x <= 100 &
    -100 <= wayPoint.y & wayPoint.y <= 100 &
    -100 <= wayPoint.z & wayPoint.z <= 100

@strictpure def wpDiffX(wp1: WayPoint, wp2: WayPoint, xdiff: Z): B =
  wp1 == wp2(x = wp2.x + xdiff)

@pure def moveWayPointX(wayPoint: WayPoint, x: Z): WayPoint = {
  Contract(
    // require that we are given a waypoint "in the zone"
    Requires(inZone(wayPoint)),
    // ensure that the waypoint moves forward in x dimension
    Ensures(wpDiffX(Res, wayPoint, x))
  )
  return WayPoint(wayPoint.x + x, wayPoint.y, wayPoint.z)
}


val wayPoints = MSZ(s1(0), moveWayPointX(s1(0), 10), s1(1), moveWayPointX(s1(1), 10))
assert(wayPoints(1) == WayPoint(40, 30, 50))
assert(wayPoints(3) == WayPoint(94, -20, 92))
