// #Sireum #Logika
import org.sireum._

var x: Z = 0

@pure def addX(n: Z): Z = {
  return x + n
}

def foo(): Unit = {
  Contract(Modifies(x))
  val oldX = x
  val m = addX(1)
  x = 0
  assert(oldX + 1 == m)
}

@helper def incX(n: Z): Unit = {
  x = x + n
}

def bar(): Unit = {
  Contract(Modifies(x))
  val oldX = x
  incX(3)
  assert(oldX + 3 == x)
}

@record class A(var x: Z) {
  @helper def incX(n: Z): Unit = {
    x = x + n
  }

  def foo(): Unit = {
    Contract(Modifies(x))
    val oldX = x
    incX(1)
    assert(oldX + 1 == x)
  }
}