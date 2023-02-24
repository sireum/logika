// #Sireum #Logika
import org.sireum._

def swap(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size, 0 <= j, j < s.size),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == In(s)(j),
      s(j) == In(s)(i),
      All(s.indices)(k => (k != i & k != j) ->: (s(k) == In(s)(k)))
    )
  )
  val t: Z = s(i)
  s(i) = s(j)
  s(j) = t
}


def swapArith(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size, 0 <= j, j < s.size),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == In(s)(j),
      s(j) == In(s)(i),
      All(s.indices)(k => (k != i & k != j) ->: (s(k) == In(s)(k)))
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
