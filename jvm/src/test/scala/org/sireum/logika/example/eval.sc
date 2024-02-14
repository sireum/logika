// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

@datatype class EvalFoo[X, Y](val x: X, val y: Y)

@pure def binaryConstantPropagation(): Unit = {
  Deduce(
    //@formatter:off
    1  (1 + 2 == 3)  by Auto,
    2  (T)           by Eval(1)
    //@formatter:on
  )
}

@pure def unaryConstantPropagation(): Unit = {
  Deduce(
    //@formatter:off
    1  (-(-1) == 1)  by Auto,
    2  (T)           by Eval(1)
    //@formatter:on
  )
}

@pure def fieldAccess(o: EvalFoo[Z, Z]): Unit = {
  Deduce(
    //@formatter:off
    1  (EvalFoo(x = 4, y = 5).x == 4)   by Auto,
    2  (T)                              by Eval(1),
    3  (o(x = 4, y = 5).x == 4)         by Auto,
    4  (T)                              by Eval(3),
    5  (o(x = 4, y = 5).y == 5)         by Auto,
    6  (T)                              by Eval(5),
    7  (o(x = 4)(y = 1)(x = 5).x == 5)  by Auto,
    8  (T)                              by Eval(7),
    9  (o(x = 4)(x = 5).y == o.y)       by Auto,
    10 (T)                              by Eval(9)
    //@formatter:on
  )
}

@pure def tupleProjection(): Unit = {
  Deduce(
    //@formatter:off
    1  ((1, 2)._1 == 1)   by Auto,
    2  (T)                by Eval(1),
    3  ((1, 2)._2 == 2)   by Auto,
    4  (T)                by Eval(3)
    //@formatter:on
  )
}

@pure def indexing[T](a: ISZ[T], i: Z, j: Z, k: Z, t1: T, t2: T): Unit = {
  Contract(
    Requires(i != j, i == k, 0 <= i, i < a.size, 0 <= j, j < a.size)
  )
  Deduce(
    //@formatter:off
    1  (i != j)                             by Premise,
    2  (i == k)                             by Premise,
    3  (ISZ(1, 2, 3).size == 3)             by Auto,
    4  (T)                                  by Eval(3),
    5  (ISZ[Z](1, 2, 3)(0 ~> 5).size == 3)  by Auto,
    6  (T)                                  by Eval(5),
    7  (a(0 ~> t1).size == a.size)          by Auto,
    8  (T)                                  by Eval(7),
    9  (a(i ~> t1)(j ~> t2)(i) == t1)       by Auto,
    10 (T)                                  by Eval(9),
    11 (a(i ~> t1)(k ~> t2)(i) == t2)       by Auto,
    12 (T)                                  by Eval(11)
    //@formatter:on
  )
}