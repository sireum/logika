// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@enum object Bool {
  'True
  'False
}

var b: Bool.Type = Bool.True
if (B.random) {
  b = Bool.False
}

b match {
  case Bool.True =>
  case Bool.False =>
}

b match {
  case Bool.True =>
  case _ =>
}

b match {
  case _ =>
}

b match {
  case Bool.False => b = Bool.True
  case _ =>
}

assert(b == Bool.True)