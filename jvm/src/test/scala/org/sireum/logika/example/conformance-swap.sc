// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def swap[@index I, E](s: MS[I, E], i: I, j: I): Unit = {
  Contract(
    Requires(s.isInBound(i), s.isInBound(j)),
    Modifies(s),
    Ensures(s ≡ In(s)(i ~> In(s)(j), j ~> In(s)(i)))
  )
  val t = s(i)
  s(i) = s(j)
  s(j) = t
}


def swapArith(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Modifies(s),
    Case(
      "i == j",
      Requires(i == j),
      Ensures(s ≡ In(s))
    ),
    Case(
      "i != j",
      Requires(i != j, 0 <= i, i < s.size, 0 <= j, j < s.size),
      Ensures(
        s.size == In(s).size,
        s(i) == In(s)(j),
        s(j) == In(s)(i),
        All(s.indices)(k => (k != i & k != j) ->: (s(k) == In(s)(k)))
      )
    )
  )
  if (i != j) {
    s(i) = s(i) + s(j)
    s(j) = s(i) - s(j)
    s(i) = s(i) - s(j)
  }
}

@pure def swapEqSwapArithTheorem(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size, 0 <= j, j < s.size)
  )
  val s1 = s
  val s2 = s
  swap(s1, i, j)
  swapArith(s2, i, j)
  assert(s1 == s2)
}
