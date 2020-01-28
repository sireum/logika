// #Sireum

import org.sireum._

object Object {

  def inc(n: Z): Z = {
    Contract(
      Ensures(Res == n + 1)
    )
    return n + 1
  }

}

import Object._

def test1(x: Z): Unit = {
  assert(inc(x) == x + 1)
}