// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def foo(): Unit = {
  val a = ISZ(1, 2, 3)
  assert(a.size >= 3 && a(0) == 1)
  assert(a.size >= 4 || a(1) == 2)
  assert((a.size >= 3) -->: (a(2) == 3))
  assert(!(a.size >= 4 && a(3) == 0))
  assert(a.size >= 3 || a(3) == 0)
  assert((a.size >= 4) -->: (a(3) == 0))
}

def bar(s: ISZ[Z]): Unit = {
  Contract(
    Requires(s.size > 0)
  )
  assert(s.size >= 1 && s(0) * s(0) >= 0)
  assert(s.size >= 4 || s(0) * s(0) >= 0)
  assert((s.size >= 4) -->: (s(3) * s(3) >= 0))
}