// #Sireum #Logika
import org.sireum._

var globalR = r"0"

def foo(x: R): Unit = {
  assert(x > globalR)
}