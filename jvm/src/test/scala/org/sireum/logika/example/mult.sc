// #Sireum #Logika
//@Logika: --background save
import org.sireum._

val m = Z.random
val n = Z.random
assume(n >= 0)
var i = 0
var r: Z = 0
while (i < n) {
  Invariant(
    Modifies(i, r),
    0 <= i,
    i <= n,
    r == m * i
  )
  r = r + m
  i = i + 1
}
assert(r == m * n)