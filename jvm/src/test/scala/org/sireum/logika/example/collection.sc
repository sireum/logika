// #Sireum #Logika
import org.sireum._
import org.sireum.justification.Premise

// some may require larger timeout, e.g., 5000 ms

def map1(): Unit = {
  val n = Z.random
  var m = Map.empty[Z, Z]

  Deduce(
    //@formatter:off
    1 #> (m.size == 0)                 by Premise,
    2 #> (m.entries == ISZ[(Z, Z)]())  by Premise,
    3 #> (!m.contains(n))              by Premise
    //@formatter:on
  )

  m = m + n ~> 2

  Deduce(
    //@formatter:off
    1 #> m.contains(n)                 by Premise,
    2 #> (m.get(n) == Some(2))         by Premise,
    3 #> (m.entries(0) == ((n, 2)))    by Premise
    //@formatter:on
  )

  m = m - ((n, 1))

  Deduce(
    //@formatter:off
    1 #> m.contains(n)                 by Premise,
    2 #> (m.get(n) == Some(2))         by Premise,
    3 #> (m.entries(0) == ((n, 2)))    by Premise
    //@formatter:on
  )

  m = m - ((n, 2))

  Deduce(
    //@formatter:off
    1 #> (!m.contains(n))              by Premise,
    2 #> (m.get(n) == None[Z]())       by Premise
    //@formatter:on
  )
}

def map2(m0: Map[Z, Z]): Unit = {
  var m = m0
  val n = Z.random

  m = m + n ~> 2

  Deduce(
    //@formatter:off
    1 #> m.contains(n)                 by Premise,
    2 #> (m.get(n) == Some(2))         by Premise
    //@formatter:on
  )

  m = m + (n + 1) ~> 3

  Deduce(
    //@formatter:off
    1 #> m.contains(n + 1)              by Premise,
    2 #> (m.get(n + 1) == Some(3))      by Premise,
    3 #> m.contains(n)                  by Premise,
    4 #> (m.get(n) == Some(2))          by Premise,
    //@formatter:on
  )

}

def set1(): Unit = {
  val n = Z.random
  var s = Set.empty[Z]

  Deduce(
    //@formatter:off
    1 #> (s.size == 0)                  by Premise,
    2 #> (s.elements == ISZ[Z]())       by Premise,
    3 #> (!s.contains(n))               by Premise,
    //@formatter:on
  )

  s = s + n

  Deduce(
    //@formatter:off
    1 #> (s.elements == ISZ(n))         by Premise,
    2 #> (s.contains(n))                by Premise,
    //@formatter:on
  )

  s = s + (n + 1)

  Deduce(
    //@formatter:off
    1 #> s.contains(n + 1)              by Premise,
    2 #> s.contains(n)                  by Premise,
    //@formatter:on
  )

  s = s - n

  Deduce(
    //@formatter:off
    1 #> !s.contains(n)                 by Premise,
    2 #> s.contains(n + 1)              by Premise,
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
    1 #> s.contains(n + 1)              by Premise,
    2 #> s.contains(n)                  by Premise,
    //@formatter:on
  )
}