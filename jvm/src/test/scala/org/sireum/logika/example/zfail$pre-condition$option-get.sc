// #Sireum #Logika
import org.sireum._

def foo[T](o: Option[T]): T = {
  Contract(
    Requires(o.isEmpty)
  )
  return o.get
}