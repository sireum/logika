// #Sireum #Logika
//@Logika: --background save
import org.sireum._

val Z_CONST: Z = 1

object O {
  val B_CONST: B = T
}

import O._

@datatype class Foo {
  val x: Z = 2
}

@record class Bar {
  val y: Z = 3
}

def foo(): Unit = {
  assert(Z_CONST == 1)
  assert(B_CONST)
  assert(O.B_CONST)
  val foo = Foo()
  assert(foo.x == 2)
  assert(Bar().y == 3)
}