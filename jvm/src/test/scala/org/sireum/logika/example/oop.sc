// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.Premise

@sig trait AParent2[T] {
  @spec var x: T = $
  @spec var y: Z = $

  @spec def yNonNegative = Invariant(
    y >= 0
  )
}

@sig trait AParent extends AParent2[Z] {
  @spec var z: Z = $
}

@datatype class A extends AParent

object B {
  var inc: Z = 1

  @spec def incPos = Invariant(
    inc > 0
  )

  def compute(a: A): Unit = {
    Contract(
      Modifies(a),
      Ensures(
        (In(a).x >= 0) ->: (a.x > 0),
        a.x == In(a).x + inc,
        a.y == In(a).y + a.x,
        a.z == In(a).z,
        a == In(a) // inferred
      )
    )
    Spec {
      a.x = a.x + inc
      a.y = a.y + a.x
      Deduce(
        Old(a) ≡ In(a)(x = In(a).x + B.inc) by Premise,
        a ≡ Old(a)(y = Old(a).y + Old(a).x) by Premise
      )
    }
  }
}

import B._

def foo(az: A): Unit = {
  Contract(
    Reads(inc),
    Modifies(az),
    Ensures(
      az.x > In(az).x,
      az.y == In(az).y + az.x,
      az.z == In(az).z,
      az == In(az) // inferred
    )
  )
  B.compute(az)
}