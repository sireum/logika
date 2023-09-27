// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def zeroize(a: ZS): Unit = {
  Contract(
    Modifies(a),
    Ensures(
      All(a)(e => e == 0),
      a.size == In(a).size
    )
  )
  var i: Z = 0
  while (i < a.size) {
    Invariant(
      Modifies(a, i),
      0 <= i,
      i <= a.size,
      All(0 until i)(j => a(j) == 0),
      a.size == In(a).size
    )
    a(i) = 0
    i = i + 1
  }
}