// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def infeasiblePattern(): Unit = {
  var n = 0

  ISZ(1, 2, 3) match {
    case ISZ(x, y, _*) if x < y =>
      n = 1
    case _ =>
  }

  assert(n == 1, "n has to be 1")
  println("n = ", n)
}

infeasiblePattern()


def inexhaustivePattern(): Unit = {
  (Z.random, Z.random) match {
    case (z"0", x) =>
      println(x)
  }
}

def adtPattern(): Unit = {
  var zOpt: Option[Z] = None()

  if (B.random) {
    zOpt = Some(Z.random)
  }

  zOpt match {
    case Some(x) => println(x)
    case _ =>
  }

  zOpt = Some(Z.random)

  zOpt match {
    case Some(_) =>
  }
}