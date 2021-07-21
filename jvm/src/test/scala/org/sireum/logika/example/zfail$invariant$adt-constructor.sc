// #Sireum #Logika
import org.sireum._

@datatype class A(val x: Z) {
  @spec def xPos = Invariant(
    x > 0
  )
}

val a1 = A(5)
val a2 = A(0)