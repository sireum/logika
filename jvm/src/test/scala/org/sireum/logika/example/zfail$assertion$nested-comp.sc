// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def foo(b: B, zOpt: Option[Z]): Unit = {
  Contract(
    Requires(b ->: (zOpt.nonEmpty && zOpt.get == 5))
  )
  assert(zOpt.nonEmpty)
}
