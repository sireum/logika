// #Sireum #Logika
import org.sireum._

var x: Z = 0

@helper def incX(n: Z): Unit = {
  x = x + n
}

def bar(): Unit = {
  val oldX = x
  incX(3)
  assert(oldX + 3 == x)
}
