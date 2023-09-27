// #Sireum #Logika
//@Logika: --background save
import org.sireum._

ISZ(1, 2, 3) match {
  case ISZ(x, y, _*) => assert(x < y)
}