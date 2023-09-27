// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x = 2

@spec def xAtLeast2 = Invariant(
  x >= 2
)

def foo(): Unit = {
  Contract(
    Modifies(x)
  )
  x = x + 1
}