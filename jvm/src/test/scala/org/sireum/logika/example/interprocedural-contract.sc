// #Sireum #Logika
import org.sireum._

var x: Z = 0

@pure def addX(n: Z): Z = {
  Contract(
    Ensures(Res == x + n)
  )
  assert(F)
}

def foo(): Unit = {
  val oldX = x
  val m = addX(1)
  x = 0
  assert(oldX + 1 == m)
}
