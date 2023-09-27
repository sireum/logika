// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def testTuple(): Unit = {
  val x = Z.random
  val y = Z.random

  val z = (x, y)

  assert(z._1 == x)
  assert(z._2 == y)
  assert(z == ((x, y)))
}

@pure def pair[T1, T2](t1: T1, t2: T2): (T1, T2) = {
  Contract(
    Ensures(Res == ((t1, t2)))
  )
  return (t1, t2)
}

def testTupleMethod(x: B, y: Z): Unit = {
  val z = pair(x, y)
  println("x = ", z._1, " and y = ", z._2)
  val (a, b) = z
  assert(a == x & b == y)
}

testTupleMethod(true, 5)