// #Sireum #Logika
import org.sireum._
import org.sireum.justification.Premise

var y = 0

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

object Foo {
  var y: Z = 0
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