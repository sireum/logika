// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var zOpt: Option[Z] = None[Z]()

if (B.random) {
  zOpt = Some(Z.random)
}

zOpt match {
  case Some(x) =>
  case _ =>
}

zOpt = Some(Z.random)

zOpt match {
  case Some(_) =>
}