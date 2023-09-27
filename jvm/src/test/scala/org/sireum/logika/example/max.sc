// #Sireum #Logika
//@Logika: --background save
import org.sireum._

val x = Z.random
val y = Z.random
var max = x
if (x < y) {
  max = y
}
assert(max >= x & max >= y & (max == x | max == y))