// #Sireum #Logika

import org.sireum._

@strictpure def add(x: Z, y: Z): Z = x + y

def inc(x: Z): Z = {
  Contract(
    Ensures(Res == add(x, 1))
  )
  return x + 1
}


@strictpure def eq[T](x: T, y: T): B = x == y

def ifEqual[T](x: T, y: T, t: Z, f: Z): Z = {
  Contract(
    Ensures(
      eq(x, y) imply_: (Res == t),
      !eq(x, y) imply_: (Res == f)
    )
  )
  if (x != y) {
    return f
  } else {
    return t
  }
}

@datatype class A(x: Z) {
  @strictpure def <(other: A): B = x < other.x

  def min(other: A): A = {
    Contract(
      Ensures(
        (this < other) imply_: (Res == this),
        !(this < other) imply_: (Res == other)
      )
    )
    if (x >= other.x) {
      return other
    } else {
      return this
    }
  }
}

