// #Sireum #Logika
import org.sireum._

val m = Z.random
val n = 3
var i = 0
var r: Z = 0
while (i < n) { // loop unrolling (no modify clause)
  Invariant(
    0 <= i,
    i <= n,
    r == m * i
  )
  r = r + m
  i = i + 1
}
assert(r == m * n)                  