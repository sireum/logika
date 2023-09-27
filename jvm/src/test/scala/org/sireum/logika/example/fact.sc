// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.ClaimOf

@spec def f(num: Z): Z = $

@spec def fFact = Fact(
  f(0) == 1,
  ∀{ num: Z => (num > 0) ->: (f(num) == num * f(num - 1)) }
)

@pure def factorial(num: Z): Z = {
  Contract(
    Requires(num >= 0),
    Ensures(Res == f(num))
  )
  var r: Z = 1
  var i: Z = 0

  Deduce(
    //@formatter:off
    1 #> (f(0) == 1)                                                 by ClaimOf(fFact _)
    //@formatter:on
  )

  while (i < num) {
    Invariant(
      Modifies(r, i),
      r == f(i),
      0 <= i,
      i <= num
    )
    i = i + 1
    r = r * i

    Deduce(
      //@formatter:off
      1 #> ∀{ num: Z => (num > 0) ->: (f(num) == num * f(num - 1)) }  by ClaimOf(fFact _)
      //@formatter:on
    )
  }
  return r
}

def foo(): Unit = {
  Deduce(
    //@formatter:off
    1 #> (f(0) == 1)                                                 by ClaimOf(fFact _),
    2 #> ∀{ num: Z => (num > 0) ->: (f(num) == num * f(num - 1)) }    by ClaimOf(fFact _)
    //@formatter:on
  )
  assert(factorial(5) == 120)
}
