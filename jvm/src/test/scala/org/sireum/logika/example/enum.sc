// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@enum object Day {
  "Sunday"
  "Monday"
  "Tuesday"
  "Wednesday"
  "Thursday"
  "Friday"
  "Saturday"
}

val x = Day.Monday
assert(x != Day.Sunday)

def foo(y: Day.Type): Unit = {
  y match {
    case Day.Sunday =>
    case Day.Monday =>
    case Day.Tuesday =>
    case Day.Wednesday =>
    case Day.Thursday =>
    case Day.Friday =>
    case Day.Saturday =>
  }
}