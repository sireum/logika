// #Sireum #Logika
import org.sireum._
import org.sireum.justification.{Algebra, Algebra_*, Premise}

def valid(): Unit = {
  Deduce(
    1 #> (0 <= 0) by Algebra
  )
  Deduce(
    1 #> (24 < 42 - 4 - 2) by Algebra
  )
  Deduce(
    1 #> (44 - (1 + (1 + (1 - 1))) == 42) by Algebra
  )
  val x = 0
  val y = 42
  Deduce(
    1 #> (x == 0) by Premise,
    2 #> (y == 42) by Premise,
        3 #> (y > x) by Algebra_*(ISZ(1, 2))
  )
}

def invalid(): Unit = {
  Deduce(
    1 #> (0 < 0) by Algebra
  )
  Deduce(
    1 #> (42 + 0 == 4 + 2) by Algebra
  )
}

def disallowed(): Unit = {
  Deduce(
    1 #> (T || F) by Algebra
  )
  Deduce(
    1 #> ((42 == 1) && T) by Algebra
  )
  val a = 2
  val b = 44
  Deduce(
    1 #> (a == 2) by Premise,
    2 #> (a <= 42) by Algebra_*(ISZ(1)),
    3 #> (b == 44) by Premise,
    4 #> (b >= 42) by Algebra_*(ISZ(3)),
    5 #> (a > 42 imply_: a != b) by Algebra_*(ISZ(1, 2))
  )
}
