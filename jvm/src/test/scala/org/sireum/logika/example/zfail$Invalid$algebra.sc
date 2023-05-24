// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

def invalid(): Unit = {
  Deduce(
    1 #> (0 < 0) by Algebra
  )
  Deduce(
    1 #> (42 + 0 == 4 + 2) by Algebra
  )
}
