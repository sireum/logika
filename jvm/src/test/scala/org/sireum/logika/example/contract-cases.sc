// #Sireum

import org.sireum._

def abs(n: Z): Z = {
  Contract(
    Case(
      Requires(n < 0),
      Ensures(Res == -n)
    ),
    Case(
      Requires(n >= 0),
      Ensures(Res == n)
    )
  )
  if (n <= 0) {
    return -n
  } else {
    return n
  }
}

def test(): Unit = {
  val x = Z.random
  assert(abs(x * x) >= 0)
  assert(abs(x * -x) >= 0)
}