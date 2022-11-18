// #Sireum #Logika
import org.sireum._

@record class A(var x: Z) {
  @helper def incX(n: Z): Unit = {
    x = x + n
  }

  def foo(): Unit = {
    val oldX = x
    incX(1)
    assert(oldX + 1 == x)
  }
}