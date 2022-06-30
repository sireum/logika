// #Sireum #Logika

// Note: this example requires alt-ergo for validity checking

import org.sireum._
import org.sireum.justification.Premise

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
        1 #> (s(i) === e) by Premise,
        5 #> (r == countRange(s, e, 0, i))                               by Premise,
        6 #> !(i + 1 > s.size | 0 < 0 | 0 >= i + 1)                      by Premise,
        7 #> (countRange(s, e, 0, i + 1) == 1 + countRange(s, e, 0, i))  by Premise,
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
  assert(count(s, 1) == countRange(s, 1, 0, s.size))
  assert(count(s, 2) == countRange(s, 2, 0, s.size))
  assert(count(s, 3) == countRange(s, 3, 0, s.size))

  // The following could not be deduced
  /*
  assert(count(s, 1) == 1 + countRange(s, 1, 0, s.size - 1))
  assert(count(s, 1) == 1 + countRange(s, 1, 1, s.size))
   */
}

test1()