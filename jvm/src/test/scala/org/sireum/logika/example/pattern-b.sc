// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var b = B.random

b match {
  case T =>
  case F =>
}

b match {
  case T =>
  case _ =>
}

b match {
  case _ =>
}

b match {
  case F => b = T
  case _ =>
}

assert(b)