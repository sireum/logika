// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.N._

@strictpure def f(num: N): N =
  if (num == n"0") n"1"
  else num * f(num - n"1")

@pure def factorial(num: N): N = {
  Contract(
    Ensures(Res == f(num))
  )
  var r: N = n"1"
  var i: N = n"0"
  while (i < num) {
    Invariant(
      Modifies(r, i),
      r == f(i),
      i <= num
    )
    assert(F)
    i = i + n"1"
    r = r * i
  }
  return r
}