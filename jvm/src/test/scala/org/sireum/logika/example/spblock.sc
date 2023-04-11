// #Sireum #Logika
import org.sireum._

def foo(x: Z): Z = {
  Contract(
    Ensures(
      Res == {
        val t = x * x
        2 * t
      }
    )
  )
  return 2 * x * x
}