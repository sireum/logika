// #Sireum #Logika
import org.sireum._
import org.sireum.justification.Premise

var y: Z = 0

object Foo {
  var y: Z = 0
}

def addY(n: Z): Unit = {
  Contract(
    Modifies(y),
    Ensures(y === In(y) + n)
  )
  y = y + n
}


def addFooY(n: Z): Unit = {
  Contract(
    Modifies(Foo.y),
    Ensures(Foo.y === In(Foo.y) + n)
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
    x === 4              by Premise
    //@formatter:on
  )

  x = 5

  Deduce(
    //@formatter:off
    At(x, 0) === 4       by Premise,
    x === 5              by Premise,
    //@formatter:on
  )

  y = y + 1

  Deduce(
    //@formatter:off
    y === At(y, 0) + 1   by Premise
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
    Foo.y === At(Foo.y, 0) + 1          by Premise
    //@formatter:on
  )

  Foo.y = Foo.y + 2

  Deduce(
    //@formatter:off
    At(Foo.y, 1) === At(Foo.y, 0) + 1   by Premise,
    Foo.y === At(Foo.y, 1) + 2          by Premise
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
    At[Z]("addY.n", 0) === 0                     by Premise,
    y === At(y, 0) + At[Z]("addY.n", 0)          by Premise
    //@formatter:on
  )

  addY(1)

  Deduce(
    //@formatter:off
    At[Z]("addY.n", 0) === 0                     by Premise,
    At[Z]("addY.n", 1) === 1                     by Premise,
    At(y, 1) === At(y, 0) + At[Z]("addY.n", 0)   by Premise,
    y === At(y, 1) + At[Z]("addY.n", 1)          by Premise
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
    At[Z]("addFooY.n", 0) === 0                             by Premise,
    Foo.y === At(Foo.y, 0) + At[Z]("addFooY.n", 0)          by Premise
    //@formatter:on
  )

  addFooY(1)

  Deduce(
    //@formatter:off
    At[Z]("addFooY.n", 0) === 0                             by Premise,
    At[Z]("addFooY.n", 1) === 1                             by Premise,
    At(Foo.y, 1) === At(Foo.y, 0) + At[Z]("addFooY.n", 0)   by Premise,
    Foo.y === At(Foo.y, 1) + At[Z]("addFooY.n", 1)          by Premise
    //@formatter:on
  )
}

