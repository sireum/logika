// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

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
    3 #> (y > x) by Algebra* (1, 2)
  )
}
