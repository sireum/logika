// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def update(s: MSZ[Z], i: Z, v: Z): Unit = {
  Contract(
    Requires(0 <= i, i < s.size),
    Modifies(s),
    Ensures(
      s.size == In(s).size,
      s(i) == v,
      All{ j: Z => (0 <= j & j < s.size) -->: (i != j) ->: (s(j) == In(s)(j)) },
      //All(s.indices)((j: Z) => (i != j) ->: (s(j) == In(s)(j))),
      //!(Exists{ j:Z => ((0 <= j & j < s.size) & (i != j)) && (s(j) == In(s)(j)) }),
      //s == In(s)(i ~> v)
    )
  )

  s(i) = v
}