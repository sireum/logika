// #Sireum
import org.sireum._

val x = Z.random
val y = Z.random

val z = (x, y)

assert(z._1 == x)
assert(z._2 == y)
assert(z == ((x, y)))