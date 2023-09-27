// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.{Auto, Smt2}

@strictpure def countTil(s: ZS, e: Z, til: Z): Z =
  if (til <= 0 | til > s.size) 0
  else if (s(til - 1) == e) 1 + countTil(s, e, til - 1)
  else countTil(s, e, til - 1)

@pure def count(s: ZS, e: Z): Z = {
  Contract(
    Ensures(Res == countTil(s, e, s.size))
  )

  var i: Z = 0
  var r: Z = 0
  while (i < s.size) {
    Invariant(
      Modifies(i, r),
      0 <= i,
      i <= s.size,
      r == countTil(s, e, i)
    )
    if (s(i) == e) {
      Deduce(
        //@formatter:off
        1 #> (r == countTil(s, e, i))                          by Auto,
        2 #> !(i + 1 <= 0 | i > s.size)                        by Auto,
        3 #> (s((i + 1) - 1) == e)                             by Auto,
        4 #> (countTil(s, e, i + 1) == 1 + countTil(s, e, i))  by Smt2("cvc5,--enum-inst-interleave", 2000, 1000000)
        //@formatter:on
      )
      r = r + 1
    }
    i = i + 1
  }
  return r
}

def test1(): Unit = {
  val s = ZS(1, 2, 1, 3, 2, 1)
  assert(count(s, 1) == countTil(s, 1, s.size))
  assert(count(s, 2) == countTil(s, 2, s.size))
  assert(count(s, 3) == countTil(s, 3, s.size))
}

test1()