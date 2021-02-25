// #Sireum #Logika
import org.sireum._

var x: Z = 0

def inc(): Unit = {
  Contract(
    Modifies(x),
    Ensures(x == In(x) + 1)
  )
  x = x + 1
}