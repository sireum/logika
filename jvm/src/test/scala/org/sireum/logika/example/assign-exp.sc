// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x: Z = {
  val y = 2
  val z = 3
  y * z
}
assert(x == 6)

x = if (B.random) {
  10
}  else {
  11
}
assert(x == 10 || x == 11)

x = Z.random match {
  case z"0" => 100
  case z"1" => 101
  case _ => 102
}
assert(x == 100 || x == 101 || x == 102)