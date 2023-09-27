// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def foo(x: Z, y: Z): Z = {
  Contract(
    Ensures(Res == x + 2 * y)
  )
  return x + 2 * y
}

val r = foo(1, 2)
assert(r == foo(x = 1, y = 2))
assert(r == foo(y = 2, x = 1))