// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.{Auto, Smt2}

@strictpure def countRange(s: ZS, e: Z, from: Z, til: Z): Z =
  if (til > s.size | from < 0 | from >= til) 0
  else if (s(til - 1) == e) 1 + countRange(s, e, from, til - 1)
  else countRange(s, e, from, til - 1)

@pure def count(s: ZS, e: Z): Z = {
  Contract(
    Ensures(
      Res == countRange(s, e, 0, s.size)
    )
  )

  var i: Z = 0
  var r: Z = 0
  while (i < s.size) {
    Invariant(
      Modifies(i, r),
      0 <= i,
      i <= s.size,
      r == countRange(s, e, 0, i)
    )
    if (s(i) == e) {
      Deduce(
        //@formatter:off
        1 #> (s(i) == e)                                                 by Auto,
        2 #> (r == countRange(s, e, 0, i))                               by Auto,
        3 #> !(i + 1 > s.size | 0 < 0 | 0 >= i + 1)                      by Auto,
        4 #> (countRange(s, e, 0, i + 1) == 1 + countRange(s, e, 0, i))  by Smt2("cvc5,--enum-inst-interleave", 2000, 1000000),
        //@formatter:on
      )
      r = r + 1
    }
    i = i + 1
  }
  return r
}

def test1(n: Z): Unit = {
  Contract(
    Requires(!(1 <= n & n <= 3))
  )

  val s = ZS(1, 2, 1, 3, 2, 1)

  assert(count(s, 1) == countRange(s, 1, 0, s.size))
  assert(count(s, 2) == countRange(s, 2, 0, s.size))
  assert(count(s, 3) == countRange(s, 3, 0, s.size))

  assert(s.size == 6)
  assert(countRange(s, 1, 0, 0) == 0)
  assert(countRange(s, 1, -1, 0) == 0)
  assert(countRange(s, 1, 0, 7) == 0)

  assert(countRange(s, 1, 0, 1) == 1)
  assert(countRange(s, 1, 0, 2) == 1)

  assert(countRange(s, 2, 0, 1) == 0)
  assert(countRange(s, 2, 0, 2) == 1)
  assert(countRange(s, 2, 0, 3) == 1)
  assert(countRange(s, 2, 0, 4) == 1)

  assert(countRange(s, 3, 0, 1) == 0)
  assert(countRange(s, 3, 0, 2) == 0)
  assert(countRange(s, 3, 0, 3) == 0)

  assert(countRange(s, n, 0, 0) == 0)
  assert(countRange(s, n, 0, 1) == 0)
  assert(countRange(s, n, 0, 2) == 0)
  assert(countRange(s, n, 0, 3) == 0)
  assert(countRange(s, n, 0, 4) == 0)
  assert(countRange(s, n, 0, 5) == 0)
  assert(countRange(s, n, 0, 6) == 0)
  assert(countRange(s, n, 0, 7) == 0)
  assert(countRange(s, n, 0, 8) == 0)

  assert(countRange(s, n, 1, 1) == 0)
  assert(countRange(s, n, 1, 2) == 0)
  assert(countRange(s, n, 1, 3) == 0)
  assert(countRange(s, n, 1, 4) == 0)
  assert(countRange(s, n, 1, 5) == 0)
  assert(countRange(s, n, 1, 6) == 0)
  assert(countRange(s, n, 1, 7) == 0)

  assert(countRange(s, n, 2, 2) == 0)
  assert(countRange(s, n, 2, 3) == 0)
  assert(countRange(s, n, 2, 4) == 0)
  assert(countRange(s, n, 2, 5) == 0)
  assert(countRange(s, n, 2, 6) == 0)
  assert(countRange(s, n, 2, 7) == 0)

  assert(countRange(s, n, 3, 4) == 0)
  assert(countRange(s, n, 3, 5) == 0)
  assert(countRange(s, n, 3, 6) == 0)
  assert(countRange(s, n, 3, 7) == 0)

  assert(countRange(s, n, 4, 5) == 0)
  assert(countRange(s, n, 4, 6) == 0)
  assert(countRange(s, n, 4, 7) == 0)

  assert(countRange(s, n, 5, 6) == 0)
  assert(countRange(s, n, 5, 7) == 0)

  assert(countRange(s, n, 6, 7) == 0)

  // The following could not be deduced
  /*
  assert(countRange(s, 1, 0, 3) == 2)

  assert(countRange(s, 2, 0, 5) == 2)

  assert(countRange(s, 3, 0, 4) == 1)

  assert(count(s, 1) == 1 + countRange(s, 1, 0, s.size - 1))

  assert(count(s, 1) == 1 + countRange(s, 1, 1, s.size))
   */
}

test1(4)