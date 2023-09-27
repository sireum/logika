// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@record class Foo[A](var a: A) {

  @spec var y: Z = $

  var z: Z = 0

  def inc(n: Z): Z = {
    Contract(
      Modifies(y, z),
      Ensures(
        Res == n + 1,
        y == In(y) + 2,
        z == In(this).z + 3
      )
    )
    Spec {
      y = y + 2
    }
    z = z + 3
    return n + 1
  }

  def iteEq[B](a2: A, t: B, f: B): B = {
    Contract(
      Ensures(
        (a == a2) ->: (Res == t),
        (a != a2) ->: (Res == f)
      )
    )
    if (a == a2) {
      return t
    } else {
      return f
    }
  }
}

def test(x: Z): Unit = {
  val foo = Foo(0)
  @spec val preY = foo.y
  val preZ = foo.z
  val r = foo.inc(x)
  assert(r == x + 1 & foo.z == preZ + 3)
  Spec {
    assert(foo.y == preY + 2)
  }
  assert(foo.iteEq(0, 1, 2) == 1)
  assert(foo.iteEq(1, 1, 2) == 2)
}
