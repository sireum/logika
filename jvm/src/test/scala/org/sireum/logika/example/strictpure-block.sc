// #Sireum #Logika
import org.sireum._

def foo(x: Z): Z = {
  Contract(
    Ensures(
      Res == {
        val t = x * x
        2 * t
      }
    )
  )
  return 2 * x * x
}

def absOpt(zOpt: Option[Z]): Option[Z] = {
  Contract(
    Ensures({
      Res[Option[Z]] match {
        case Some(res) => res >= 0
        case _ => T
      }
    })
  )
  val r: Option[Z] = zOpt match {
    case Some(z) if z < 0 => Some(-z)
    case Some(z) => Some(z)
    case _ => None()
  }
  return r
}