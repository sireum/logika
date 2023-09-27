// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def swap[@index I, T](s: MS[I, T], i: I, j: I): Unit = {
  Contract(
    Reads(),
    Requires(s.isInBound(i), s.isInBound(j)),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == In(s)(j),
      s(j) == In(s)(i),
      All{ k: I => s.isInBound(k) -->: (k != i & k != j) ->: (s(k) == In(s)(k)) },
      All(s.indices)(k => (k != i & k != j) ->: (s(k) == In(s)(k)))
    )
  )
  val t = s(i)
  s(i) = s(j)
  s(j) = t
}

def swapZS(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size, 0 <= j, j < s.size),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == In(s)(j),
      s(j) == In(s)(i),
      All{ k: Z => (0 <= k & k < s.size) -->: (k != i & k != j) ->: (s(k) == In(s)(k)) },
      All(0 until s.size)(k => (k != i & k != j) ->: (s(k) == In(s)(k))),
      All(s.indices)(k => (k != i & k != j) ->: (s(k) == In(s)(k)))
    )
  )
  val t: Z = s(i)
  s(i) = s(j)
  s(j) = t
}

def swapZS2(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size, 0 <= j, j < s.size),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == In(s)(j),
      s(j) == In(s)(i),
      All{ k: Z => (0 <= k & k < s.size) -->: (k != i & k != j) ->: (s(k) == In(s)(k)) },
      All(0 until s.size)(k => (k != i & k != j) ->: (s(k) == In(s)(k))),
      All(s.indices)(k => (k != i & k != j) ->: (s(k) == In(s)(k)))
    )
  )
  if (i != j) {
    s(i) = s(i) + s(j)
    s(j) = s(i) - s(j)
    s(i) = s(i) - s(j)
    Deduce(|- (All{ k: Z => (0 <= k & k < s.size) -->: (k != i & k != j) ->: (s(k) == In(s)(k)) })) // required when SMT2 query is simplified
  } else {
    Deduce(|- (All{ k: Z => (0 <= k & k < s.size) -->: (k != i & k != j) ->: (s(k) == In(s)(k)) })) // require when SMT2 query is simplified
  }
}
