// #Sireum

import org.sireum._

@record class Foo {

  @spec var y: Z = $

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
}

def test(x: Z): Unit = {
  val foo = Foo()
  @spec val preY = foo.y
  val preZ = foo.z
  val r = foo.inc(x)
  assert(r == x + 1 & foo.z == preZ + 3)
  Contract {
    assert(foo.y == preY + 2)
  }
}
