// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x: Z = 0

@inline def incX(n: Z): Unit = {
  x = x + n
}

def bar(): Unit = {
  val oldX = x
  incX(3)
  assert(oldX + 3 == x)
}
