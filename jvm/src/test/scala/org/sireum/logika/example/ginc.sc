// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x: Z = 0

def inc(): Unit = {
  Contract(
    Modifies(x),
    Ensures(x == In(x) + 1)
  )
  x = x + 1
}