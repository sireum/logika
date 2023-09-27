// #Sireum #Logika
//@Logika: --background save
import org.sireum._

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
      0 <= x,
      x <= a.size,
      a.size == In(a).size,
      ∀(0 until x)(i => a(i) == In(a)(i) * In(a)(i)),
      ∀(x until a.size)(i => a(i) == In(a)(i))
    )
    a(x) = a(x) * a(x)
    x = x + 1
  }
}
