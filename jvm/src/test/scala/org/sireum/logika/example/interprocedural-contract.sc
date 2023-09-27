// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var x: Z = 0

@helper @pure def addX(n: Z): Z = {
  Contract(
    Ensures(Res == x + n)
  )
  halt("TODO")
}

def foo(): Unit = {
  setOptions("Logika", """--sat --par --par-branch --interprocedural --interprocedural-contracts""")
  val oldX = x
  val m = addX(1)
  x = 0
  assert(oldX + 1 == m)
}
