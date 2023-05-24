// #Sireum #Logika
import org.sireum._
import org.sireum.justification.{Premise, Subst1}

def a(): Unit = {
  val x = 4 - 5
  val y = (8 + 4) - (5 + 6)
  Deduce(
    1 #> (x === 4 - 5) by Premise,
    2 #> (y == (8 + 4) - (5 + 6)) by Premise,
    3 #> (y == 8 + x + 6) by Subst1(1, 2)
  )
}
