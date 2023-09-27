// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@enum object Bool {
  'True
  'False
}

def foo(b: Bool.Type): Unit = {
  Contract(
    Case(Requires(b == Bool.True)),
    Case(Requires(b == Bool.False))
  )
  var b2: Bool.Type = Bool.False

  b match {
    case Bool.True => b2 = Bool.True
    case Bool.False =>
  }

  assert(b2 == Bool.True)
  assert(b2 == Bool.False)
}