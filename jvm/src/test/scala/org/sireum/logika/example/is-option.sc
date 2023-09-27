// #Sireum #Logika
//@Logika: --background save
import org.sireum._

val s1 = ISZ(1, 2, 3)
assert(T)
assert(s1(0) == 1)
assert(s1(1) == 2)
assert(s1(2) == 3)
assert(s1.size == 3)
val s2 = ISZ(Some(3))
assert(s2(0).value == 3)