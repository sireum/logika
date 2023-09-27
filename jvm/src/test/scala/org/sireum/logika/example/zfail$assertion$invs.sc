// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x: Z = 0
var y: Z = 0
@spec def xNonNeg = Invariant(
  x >= 0, y >= 0
)

def foo(): Unit = {
}

def bar(): Unit = {
  foo()
  assert(F)
}