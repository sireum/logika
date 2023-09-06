// #Sireum #Logika
import org.sireum._

val y = Z.random
var x = y + 4
x = x - y
Deduce(
  |- (Old(x) == y + 4),
  |- (Old(x) - y == x)
)
