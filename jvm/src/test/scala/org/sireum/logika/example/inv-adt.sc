// #Sireum #Logika
import org.sireum._

var x: Option[Z] = Some(2)

@spec def xAtLeast2 = Invariant(
  x.isEmpty || x.get > 0
)

def foo(): Unit = {
}