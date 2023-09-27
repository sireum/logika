// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def foo[A](a1: A, a2: A): B = {
  Contract(
    Ensures(Res == (a1 != a2))
  )
  return a1 != a2
}

@datatype class Foo[A](x: A) {
  def foo[B](a: A, b1: B, b2: B): B = {
    Contract(
      Ensures(
        (x == a) ->: (Res == b1),
        (x != a) ->: (Res == b2)
      )
    )
    if (x == a) {
      return b1
    } else {
      return b2
    }
  }
}