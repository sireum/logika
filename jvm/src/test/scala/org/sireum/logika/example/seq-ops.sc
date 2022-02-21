// #Sireum #Logika
import org.sireum._

assert(ISZ(1, 2) :+ 3 == ISZ(1, 2, 3))
assert(ISZ(1, 2) ++ ISZ(3) == ISZ(1, 2, 3))
assert(1 +: ISZ(2, 3) == ISZ(1, 2, 3))
assert(ISZ[Z](1, 2, 3)(0 ~> 4) == ISZ(4, 2, 3))