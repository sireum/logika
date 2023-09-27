// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.{Algebra, Auto, Premise, Subst_<, Subst_>}

def a(x: Z): Unit = {
  val y = -3 + 42
  val z = x + 1 + (y + 3) + 4
  Deduce(
    1 #> (y + 3 == 42) by Auto,
    2 #> (z == x + 1 + (y + 3) + 4) by Premise,
      3 #> (z == x + 1 + 42 + 4) by Subst_<(1, 2)
  )
}

def b(): Unit = {
  val x = 4 - 5
  val y = 8 + (4 - 5) + 6
  Deduce(
    1 #> (x == 4 - 5) by Premise,
    2 #> (y == 8 + (4 - 5) + 6) by Premise,
    3 #> (y == 8 + x + 6) by Subst_>(1, 2)
  )
}

def c(): Unit = {
  val x = -2 + 42
  val y = (8 + (x + 2)) - (5 - x + 2) * (x + 2)
  Deduce(
    1 #> (x + 2 == 42) by Auto,
    2 #> (y == (8 + (x + 2)) - (5 - x + 2) * (x + 2)) by Premise,
    3 #> (y == (8 + 42) - (5 - x + 2) * 42) by Subst_<(1, 2)
  )
}

def v3_seq_2(x: Z, y: Z): Z = {
  Contract(
    Requires(x == 0 && y > x)
  )
  val g: ZS = ZS(2, 4)
  Deduce(
    1 #> (g(0) > 0 && g.size >= 1) by Auto,
    2 #> (x == 0 && y > x) by Premise,
    3 #> (x == 0) by Auto,
    4 #> (0 <= x) by Algebra and 3,
    5 #> (g.size >= 1) by Auto,
    6 #> (x < g.size) by Algebra and (3, 5)
  )
  val g_old = g
  g(x) = y
  Deduce(
    1 #> (g(x) == y) by Auto,
    2 #> (g_old(0) > 0 && g_old.size >= 1) by Auto,
    3 #> (x == 0 && y > x) by Auto,
    4 #> (g.size == g_old.size) by Auto,
    5 #> (g_old.size >= 1) by Auto,
    6 #> (g.size >= 1) by Subst_>(4, 5),
    7 #> (x == 0) by Auto,
    8 #> (y > x) by Auto,
    9 #> (g(0) == y) by Subst_<(7, 1),
    10 #> (g(0) > x) by Subst_>(9, 8),
    11 #> (g(0) > 0) by Subst_<(7, 10),
    12 #> (g(0) > 0 && g.size >= 1) by Auto
  )
  return x
}

def v3_assignment_14(): Unit = {
  var dimes: Z = 42
  var money: Z = dimes * 10

  assert(money == dimes * 10)
  Deduce(
    1 #> (money == dimes * 10) by Premise
  )
  val dimes_old = dimes
  dimes = dimes + 1
  Deduce(
    1 #> (dimes == dimes_old + 1) by Auto,
    2 #> (money == dimes_old * 10) by Auto,
    3 #> (dimes_old == dimes - 1) by Algebra and 1,
    4 #> (money == (dimes - 1) * 10) by Subst_<(3, 2)
  )
  val money_old = money
  money = money + 10
  Deduce(
    1 #> (money_old == (dimes - 1) * 10) by Auto,
    2 #> (money == money_old + 10) by Auto,
    3 #> (money_old == money - 10) by Algebra and 2,
    4 #> (money - 10 == ((dimes - 1) * 10)) by Subst_<(3, 1),
    5 #> (money == ((dimes - 1) * 10) + 10) by Algebra and 4,
    6 #> (money == dimes * 10) by Algebra and 5
  )
}

def foo(seq: ISZ[Z], index: Z): Unit = {
  Contract(
    Requires(
      seq.isInBound(0),
      seq.isInBound(index)
    )
  )

  val s = seq
  val i = seq(index)
  val index0 = index
  val b = seq.isInBound(index)

  Deduce(
    1 #> (s === seq) by Premise,
    2 #> (i == seq(index)) by Premise,
    3 #> (i == s(index)) by Subst_>(1, 2)
  )

  Deduce(
    1 #> (s === seq) by Premise,
    2 #> (index0 == index) by Premise,
    3 #> (b == seq.isInBound(index)) by Premise,
    4 #> (b == s.isInBound(index)) by Subst_>(1, 3),
    5 #> (b == s.isInBound(index0)) by Subst_>(2, 4)
  )
}
