// #Sireum #Logika
import org.sireum._

val Z_CONST: Z = 1

object O {
  val B_CONST: B = T
}

def foo(): Unit = {
  assert(Z_CONST === 1)
  assert(O.B_CONST)
}