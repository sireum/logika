// #Sireum

import org.sireum._

@spec var y: Z = 0

var z: Z = 0

def inc(n: Z): Z = {
  Contract(
    Modifies(y, z),
    Ensures(
      Res == n + 1,
      y == In(y) + 2,
      z == In(z) + 3
    )
  )
  Contract {
    y = y + 2
  }
  z = z + 3
  return n + 1
}

def test(x: Z): Unit = {
  Contract(
    Modifies(y, z),
    Ensures(y == In(y) + 2)
  )
  val preZ = z
  @spec val preY = y
  val r = inc(x)
  assert(r == x + 1 & z == preZ + 3)
  Contract {
    assert(y == preY + 2)
  }
}
