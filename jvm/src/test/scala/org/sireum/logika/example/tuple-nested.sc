// #Sireum #Logika
//@Logika: --background save
import org.sireum._

type Matrix = ((Z, Z), (Z, Z))

val umat: Matrix = ((1, 0), (0, 1))

Deduce(|- (umat == ((1, 0), (0, 1))))