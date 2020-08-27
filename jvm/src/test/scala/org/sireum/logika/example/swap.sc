// #Sireum
import org.sireum._

def swap(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size, 0 <= j, j < s.size),
    Modifies(s),
    Ensures(
      //s.size == In(s).size,
      //s(i) == In(s)(j),
      //s(j) == In(s)(i),
      All{ k: Z => (0 <= k & k < s.size) imply_: (k != i & k != j) imply_: (s(k) == In(s)(k)) },
      All(0 until s.size)(k => (k != i & k != j) imply_: (s(k) == In(s)(k))),
      //All(s.indices)(k => (k != i & k != j) imply_: (s(k) == In(s)(k)))
    )
  )
  val t: Z = s(i)
  s(i) = s(j)
  s(j) = t
}