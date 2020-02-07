// #Sireum

import org.sireum._

@enum object Day {
  'Sunday
  'Monday
  'Tuesday
  'Wednesday
  'Thursday
  'Friday
  'Saturday
}

val x = Day.Monday
assert(x != Day.Sunday)