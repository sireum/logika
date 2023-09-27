// #Sireum #Logika
//@Logika: --background save
import org.sireum._

val x = Z.random

assert(if (x * x >= 0) T else F)
assert((if (x >= 0) if (x <= 0) x * x else x - x else -x + x) == 0)