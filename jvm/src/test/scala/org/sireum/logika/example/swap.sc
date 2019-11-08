// #Sireum
import org.sireum._

@pure def swap(s: ZS, i: Z, j: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size, 0 <= j, j < s.size),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == In(s)(j),
      s(j) == In(s)(i),
      //All(s.indices)(k => (k != i & k != j) imply_: (s(k) == In(s)(k)))
    )
  )
  val t: Z = s(i)
  s(i) = s(j)
  s(j) = t
}