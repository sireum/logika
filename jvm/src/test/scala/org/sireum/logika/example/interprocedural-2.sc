// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x: Z = 0

@helper def incX(n: Z): Unit = {
  x = x + n
}

def bar(): Unit = {
  setOptions("Logika", """--sat --par --par-branch --interprocedural""")
  val oldX = x
  incX(3)
  assert(oldX + 3 == x)
}
