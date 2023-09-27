// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@record class A(var x: Z) {
  @helper def incX(n: Z): Unit = {
    x = x + n
  }

  def foo(): Unit = {
    setOptions("Logika", """--sat --par --par-branch --interprocedural""")
    val oldX = x
    incX(1)
    assert(oldX + 1 == x)
  }
}