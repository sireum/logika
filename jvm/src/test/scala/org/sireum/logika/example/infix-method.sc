// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@datatype class V(x: Z) {
  def +(y: Z): V = {
    Contract(Ensures(Res[V].x == x + y))
    return V(x + y)
  }
}

val n = Z.random
val m = Z.random
assert((V(n) + m).x == n + m)