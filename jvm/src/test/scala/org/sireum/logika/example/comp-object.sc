// #Sireum

import org.sireum._

var z: Z = 0

def inc(n: Z): Z = {
  Contract(
    Modifies(z),
    Ensures(Res == n + 1, z == In(z) + 1)
  )
  z = z + 1
  return n + 1
}

def test(x: Z): Unit = {
  Contract(
    Modifies(z)
  )
  val preZ = z
  val r = inc(x)
  assert(r == x + 1 & z == preZ + 1)
}