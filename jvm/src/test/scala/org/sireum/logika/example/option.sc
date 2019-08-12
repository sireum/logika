// #Sireum
import org.sireum._

val x = Z.random
val xOpt = Some(Some(x))
assert(xOpt.value.value == x)