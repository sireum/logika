// #Sireum #Logika
import org.sireum._

@strictpure def f(n: Z): Z =
  if (n < 0) {
    halt("Undefined")
  } else if (n == 0) {
    1
  } else {
    n * f(n - 1)
  }

@pure def factorial(n: Z): Z = {
  Contract(
    Requires(n >= 0),
    Ensures(Res == f(n))
  )
  var r: Z = 1
  var i: Z = 0
  while (i < n) {
    Invariant(
      Modifies(r, i),
      r == f(i),
      0 <= i,
      i <= n
    )
    i = i + 1
    r = r * i
  }
  return r
}