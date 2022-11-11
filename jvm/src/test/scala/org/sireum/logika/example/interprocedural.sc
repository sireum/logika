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
