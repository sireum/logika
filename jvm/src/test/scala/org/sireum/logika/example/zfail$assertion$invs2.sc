// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x: Z = 0
var y: Z = 0
@spec def xNonNeg = Invariant(
  if (x >= 0) y >= 0 else F
)

def foo(): Unit = {
}

def bar(): Unit = {
  foo()
  assert(F)
}