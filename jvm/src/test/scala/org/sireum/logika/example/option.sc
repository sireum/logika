// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def bar(x: Z): Option[Z] = {
  Contract(
    Ensures(Res == Some(x))
  )
  return Some(x)
}

def foo(): Unit = {
  assert(bar(4).get > 0)
}

val x = Z.random
val xOpt = Some(Some(x))
assert(xOpt.value.value == x)