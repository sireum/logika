// #Sireum #Logika
import org.sireum._

def map1(): Unit = {
  val n = Z.random
  var m = Map.empty[Z, Z]
  assert(m.size == 0)
  assert(m.entries == ISZ[(Z, Z)]())
  assert(!m.contains(n))

  m = m + n ~> 2
  assert(m.size == 1)
  assert(m.contains(n))
  assert(m.get(n) == Some(2))
  assert(m.entries(0) == ((n, 2)))

  m = m - ((n, 2))
  assert(m.size == 0)

  m = m - ((n, 1))
  assert(m.size == 0)
}

def map2(m0: Map[Z, Z]): Unit = {
  var m = m0
  val n = Z.random
  m = m + n ~> 2
  assert(m.contains(n))
  assert(m.get(n) == Some(2))

  m = m + (n + 1) ~> 3

  // require larger timeout, e.g., 5000 ms
  //assert(m.contains(n + 1))
  //assert(m.get(n + 1) == Some(3))
}

def set1(): Unit = {
  val n = Z.random
  var s = Set.empty[Z]
  assert(s.size == 0)
  assert(s.elements == ISZ[Z]())
  assert(!s.contains(n))

  s = s + n
  assert(s.size == 1)
  assert(s.contains(n))

  s = s + (n + 1)

  // require larger timeout, e.g., 5000 ms
  //assert(s.size == 2)
  //assert(s.contains(n))
  //assert(s.contains(n + 1))

  //s = s - n
  //assert(s.size == 1)
}

def set2(s0: Set[Z]): Unit = {
  var s = s0
  val n = Z.random
  s = s + n
  assert(s.contains(n))

  s = s + (n + 1)
  assert(s.contains(n + 1))
  // assert(s.contains(n))
}