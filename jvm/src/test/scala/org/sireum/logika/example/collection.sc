// #Sireum #Logika
import org.sireum._
import org.sireum.justification.Auto

// some may require larger timeout, e.g., 5000 ms

def map1(): Unit = {
  val n = Z.random
  var m = Map.empty[Z, Z]

  Deduce(
    //@formatter:off
    1 #> (m.size == 0)                 by Auto,
    2 #> (m.entries == ISZ[(Z, Z)]())  by Auto,
    3 #> (!m.contains(n))              by Auto
    //@formatter:on
  )

  m = m + n ~> 2

  Deduce(
    //@formatter:off
    1 #> m.contains(n)                 by Auto,
    2 #> (m.get(n) == Some(2))         by Auto,
    3 #> (m.entries(0) == ((n, 2)))    by Auto
    //@formatter:on
  )

  m = m - ((n, 1))

  Deduce(
    //@formatter:off
    1 #> m.contains(n)                 by Auto,
    2 #> (m.get(n) == Some(2))         by Auto,
    3 #> (m.entries(0) == ((n, 2)))    by Auto
    //@formatter:on
  )

  m = m - ((n, 2))

  Deduce(
    //@formatter:off
    1 #> (!m.contains(n))              by Auto,
    2 #> (m.get(n) == None[Z]())       by Auto
    //@formatter:on
  )
}

def map2(m0: Map[Z, Z]): Unit = {
  var m = m0
  val n = Z.random

  m = m + n ~> 2

  Deduce(
    //@formatter:off
    1 #> m.contains(n)                 by Auto,
    2 #> (m.get(n) == Some(2))         by Auto
    //@formatter:on
  )

  m = m + (n + 1) ~> 3

  Deduce(
    //@formatter:off
    1 #> m.contains(n + 1)              by Auto,
    2 #> (m.get(n + 1) == Some(3))      by Auto,
    3 #> m.contains(n)                  by Auto,
    4 #> (m.get(n) == Some(2))          by Auto,
    //@formatter:on
  )

}

def set1(): Unit = {
  val n = Z.random
  var s = Set.empty[Z]

  Deduce(
    //@formatter:off
    1 #> (s.size == 0)                  by Auto,
    2 #> (s.elements == ISZ[Z]())       by Auto,
    3 #> (!s.contains(n))               by Auto,
    //@formatter:on
  )

  s = s + n

  Deduce(
    //@formatter:off
    1 #> (s.elements == ISZ(n))         by Auto,
    2 #> (s.contains(n))                by Auto,
    //@formatter:on
  )

  s = s + (n + 1)

  Deduce(
    //@formatter:off
    1 #> s.contains(n + 1)              by Auto,
    2 #> s.contains(n)                  by Auto,
    //@formatter:on
  )

  s = s - n

  Deduce(
    //@formatter:off
    1 #> !s.contains(n)                 by Auto,
    2 #> s.contains(n + 1)              by Auto,
    //@formatter:on
  )
}

def set2(s0: Set[Z]): Unit = {
  var s = s0
  val n = Z.random

  s = s + n
  s = s + (n + 1)

  Deduce(
    //@formatter:off
    1 #> s.contains(n + 1)              by Auto,
    2 #> s.contains(n)                  by Auto,
    //@formatter:on
  )
}