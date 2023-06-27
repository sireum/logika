// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

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
