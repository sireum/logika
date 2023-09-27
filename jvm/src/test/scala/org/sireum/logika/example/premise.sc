// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.{Auto, Premise}

var y: Z = 0

object Foo {
  var y: Z = 0
}

def addY(n: Z): Unit = {
  Contract(
    Modifies(y),
    Ensures(y == In(y) + n)
  )
  y = y + n
}


def addFooY(n: Z): Unit = {
  Contract(
    Modifies(Foo.y),
    Ensures(Foo.y == In(Foo.y) + n)
  )
  Foo.y = Foo.y + n
}


def testId(): Unit = {
  Contract(
    Modifies(y)
  )

  var x = 4

  Deduce(
    //@formatter:off
    x == 4              by Premise
    //@formatter:on
  )

  x = 5

  Deduce(
    //@formatter:off
    Old(x) == 4         by Premise,
    x == 5              by Premise
    //@formatter:on
  )

  y = y + 1

  Deduce(
    //@formatter:off
    y == Old(y) + 1   by Premise
    //@formatter:on
  )
}


def testName(): Unit = {
  Contract(
    Modifies(Foo.y)
  )

  Foo.y = Foo.y + 1

  Deduce(
    //@formatter:off
    Foo.y == Old(Foo.y) + 1          by Premise
    //@formatter:on
  )

  Foo.y = Foo.y + 2

  Deduce(
    //@formatter:off
    Old(Foo.y) == In(Foo.y) + 1      by Premise,
    Foo.y == Old(Foo.y) + 2          by Premise
    //@formatter:on
  )
}

def testIdString(): Unit = {
  Contract(
    Modifies(y)
  )

  addY(0)

  Deduce(
    //@formatter:off
    At[Z]("addY.n", 0) == 0                         by Premise,
    y == In(y) + 0                                  by Premise
    //@formatter:on
  )

  addY(1)

  Deduce(
    //@formatter:off
    At[Z]("addY.n", 0) == 0                         by Premise,
    At[Z]("addY.n", 1) == 1                         by Premise,
    At(y, 0) + 0 == In(y) + 0                       by Premise,
    y == In(y) + 0 + 1                              by Premise
    //@formatter:on
  )
}


def testNameString(): Unit = {
  Contract(
    Modifies(Foo.y)
  )

  addFooY(0)

  Deduce(
    //@formatter:off
    At[Z]("addFooY.n", 0) == 0                                 by Premise,
    Foo.y == Old(Foo.y) + 0                                    by Premise
    //@formatter:on
  )

  addFooY(1)

  Deduce(
    //@formatter:off
    At[Z]("addFooY.n", 0) == 0                                 by Premise,
    At[Z]("addFooY.n", 1) == 1                                 by Premise,
    Old(Foo.y) == In(Foo.y) + 0                                by Premise,
    Foo.y == Old(Foo.y) + 1                                    by Premise
    //@formatter:on
  )
}

def testQuant(a: ZS): Unit = {
  Contract(
    Requires(
      ∀{j: Z => (0 <= j & j < a.size - 1) -->: (a(j) > 0)},
      ∀(0 until a.size)(j => a(j) != 0),
      ∀(a.indices)(j => a(j) >= 1),
      ∀(a)(e => e >= 2)
    )
  )

  Deduce(
    //@formatter:off
    ∀(0 until a.size - 1)(j => a(j) > 0)   by Premise,
    ∀(0 until a.size)(j => a(j) != 0)      by Premise,
    ∀(a.indices)(j => a(j) >= 1)           by Premise,
    ∀(a)(e => e >= 2)                      by Premise
    //@formatter:on
  )
}

@datatype class Foo(val x: Z) {
  @spec def inv = Invariant(
    x >= 0
  )
}

def testQuant2(foos: ISZ[Foo], i: Z): Unit = {
  Contract(
    Requires(
      0 <= i,
      i < foos.size,
      ∀(foos)(foo => foo.x > -1)
    )
  )
  Deduce(
    //@formatter:off
    foos(i).x >= 0               by Auto,
    0 <= i                       by Premise,
    i < foos.size                by Premise,
    ∀(foos)(foo => foo.x > -1)   by Premise
    //@formatter:on
  )
}

def testAdtLit[T](o: Option[T], v: T): Unit = {
  Contract(Requires(o == Some(v)))
  Deduce(o == Some(v) by Premise)
}

def testSeqLit[T](o: ISZ[T], v: T): Unit = {
  Contract(Requires(o == ISZ(v)))
  Deduce(o == ISZ(v) by Premise)
}

def testFieldLookup(o: Some[Z]): Unit = {
  Contract(Requires(o.value == 3))
  Deduce(o.value == 3 by Premise)
}