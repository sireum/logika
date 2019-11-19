// #Sireum
import org.sireum._

def update(s: MSZ[Z], i: Z, v: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == v,
      All{ j: Z => (0 <= j & j < s.size) imply_: (i != j) imply_: (s(j) == In(s)(j)) },
      //All(s.indices)((j: Z) => (i != j) imply_: (s(j) == In(s)(j))),
      !(Exists{ j:Z => (i != j) & (s(j) == In(s)(j)) & (0 <= j & j < s.size) }),
    )
  )
  s(i) = v
}