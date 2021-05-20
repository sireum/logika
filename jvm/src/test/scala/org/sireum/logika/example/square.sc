// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

def square(a: ZS): Unit = {
  Contract(
    Modifies(a),
    Ensures(a.size == In(a).size,
            ∀(a.indices)(i => a(i) == In(a)(i) * In(a)(i)))
  )
  var x: Z = 0

  while (x != a.size) {
    Invariant(
      Modifies(x, a),
      ∀(0 until x)(i => a(i) == In(a)(i) * In(a)(i)),
      ∀(x until a.size)(i => a(i) == In(a)(i)),
      0 <= x,
      x <= a.size,
      a.size == In(a).size,
    )
    a(x) = a(x) * a(x)
    x = x + 1
  }
}
