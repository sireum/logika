// #Sireum #Logika
import org.sireum._

def foo(o: Option[Z], x: Z): Z = {
  Contract(
    Requires(o == Some(x)),
    Ensures(Res[Z] >= 0)
  )
  return o.get
}