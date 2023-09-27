// #Sireum
//@Logika: --background save
import org.sireum._

def foo[@index I](i: I): Unit = {
  val n = i.toZ
  assert(n * n >= 0)
}