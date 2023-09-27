// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@strictpure def f(num: Z): Z =
  if (num < 0) {
    halt("Undefined")
  } else if (num == 0) {
    1
  } else {
    num * f(num - 1)
  }

@pure def factorial(num: Z): Z = {
  Contract(
    Requires(num >= 0),
    Ensures(Res == f(num))
  )
  var r: Z = 1
  var i: Z = 0
  while (i < num) {
    Invariant(
      Modifies(r, i),
      r == f(i),
      0 <= i,
      i <= num
    )
    assert(F)
    i = i + 1
    r = r * i
  }
  return r
}

def foo(): Unit = {
  assert(factorial(5) == 120)
}
