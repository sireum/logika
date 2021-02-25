// #Sireum #Logika
import org.sireum._

var x = Z.random
if (x < 0) {
  x = -x
}
assert(x >= 0)