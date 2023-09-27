// #Sireum #Logika
//@Logika: --background save
import org.sireum._

object A {
  @helper @strictpure def invH(a: A): B = a.x != 0
}

@datatype class A(x: Z) {
  @spec def inv = Invariant(
    A.invH(this)
  )
}

def foo(a: A): Unit = {
  assert(a.x != 0)
}

