// #Sireum #Logika
import org.sireum._

var in : Z = 0
var acc : B = T
var pin : Z = 0

def control_dependence_limited_release(): Unit = {
  Contract(
    Modifies(acc),
    InfoFlows(
      Flow("limited release",
        InAgree(in == pin),
        OutAgree(acc)))
  )
  if (in == pin) {
    acc = T
  } else {
    acc = F
  }
  assert(T)
}