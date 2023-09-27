// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@datatype class Foo(x: Z, y: Z)

val foo = Foo(1, 2)
assert(foo == Foo(x = 1, y = 2))
assert(foo(x = 2) == Foo(y = 2, x = 2))