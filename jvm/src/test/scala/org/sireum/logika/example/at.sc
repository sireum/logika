// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def foo(): Unit = {
  val x: Z = randomInt()
  val y: Z = randomInt()

  var z: Z = 0
  if (x < y) {
    z = y
  } else {
    z = x
  }
  Deduce(|-(z == x | z == y))
  z = z - x
  Deduce(|-(At(z, 1) == x | At(z, 1) == y))
  Deduce(|-(z == At(z, 1) - x))
  Deduce(|-(z + x == x | z + x == y))
  assert(z == 0 | z == y - x)
}