// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

val x = Z.random

Deduce(
  (x == 0) by Admit
)