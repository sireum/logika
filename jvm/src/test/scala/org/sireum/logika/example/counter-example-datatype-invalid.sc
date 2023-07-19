// #Sireum #Logika
import org.sireum._

@datatype class ZWrapper(v: Z)

val n = 0
val m = 1


assert(n != m)
val q = ZWrapper(n)
assert(ZWrapper(n).v == m)