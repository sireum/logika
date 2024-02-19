// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

object Rules {

  @spec def zDistribute(x: Z, y: Z, z: Z) = Theorem(
    (x * z) + (y * z) == (x + y) * z
  )

  @spec def subst[T](x: T, y: T, P: T => B @pure) = Theorem(
    (x ≡ y) __>: P(x) __>: P(y)
  )

  @rw val myRewriteSet = RS(zDistribute _)
}

import Rules._

@pure def zDistributeTest(c: Z, d: Z): Unit = {
  Deduce(
    (2 * c + 3 * c == d) |- (5 * c == d) Proof(
      //@formatter:off
      1  (2 * c + 3 * c == d)  by Premise,
      2  (5 * c == d)          by Rewrite(RS(zDistribute _), 1) T,
      3  (5 * c == d)          by Rewrite(myRewriteSet, 1) T
      //@formatter:on
    )
  )
}

@pure def substTest(c: Z, d: Z): Unit = {
  Deduce(
    (c ≡ d, (c + 1) ≡ 3) |- ((d + 1) ≡ 3) Proof(
      //@formatter:off
      1  (c ≡ d)              by Premise,
      2  ((c + 1) ≡ 3)        by Premise,
      3  ((d + 1) ≡ 3)        by Simpl //Rewrite(RS(subst _), 2)
      //@formatter:on
    )
  )
}

@pure def substTestR(c: Z, d: Z): Unit = {
  Deduce(
    (c ≡ d, (d + 1) ≡ 3) |- ((c + 1) ≡ 3) Proof(
      //@formatter:off
      1  (c ≡ d)              by Premise,
      2  ((d + 1) ≡ 3)        by Premise,
      4  ((c + 1) ≡ 3)        by Rewrite(~RS(subst _), 2) and (1, 2) // and (...) is optional but it makes the search faster
      //@formatter:on
    )
  )
}

@datatype class EvalFoo[X, Y](val x: X, val y: Y)

@pure def binaryConstantPropagation(): Unit = {
  Deduce(
    //@formatter:off
    1  (1 + 2 == 3)  by Simpl
    //@formatter:on
  )
}

@pure def unaryConstantPropagation(): Unit = {
  Deduce(
    //@formatter:off
    1  (-(-1) == 1)  by Simpl
    //@formatter:on
  )
}

@pure def fieldAccess(o: EvalFoo[Z, Z]): Unit = {
  Deduce(
    //@formatter:off
    1  (EvalFoo(x = 4, y = 5).x == 4)   by Simpl,
    3  (o(x = 4, y = 5).x == 4)         by Simpl,
    5  (o(x = 4, y = 5).y == 5)         by Simpl,
    7  (o(x = 4)(y = 1)(x = 5).x == 5)  by Simpl,
    9  (o(x = 4)(x = 5).y == o.y)       by Simpl
    //@formatter:on
  )
}

@pure def tupleProjection(): Unit = {
  Deduce(
    //@formatter:off
    1  ((1, 2)._1 == 1)   by Simpl,
    3  ((1, 2)._2 == 2)   by Simpl
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
    3  (ISZ(1, 2, 3).size == 3)             by Simpl,
    5  (ISZ[Z](1, 2, 3)(0 ~> 5).size == 3)  by Simpl,
    7  (a(0 ~> t1).size == a.size)          by Simpl,
    9  (a(i ~> t1)(j ~> t2)(i) == t1)       by Simpl,
    11 (a(i ~> t1)(k ~> t2)(i) == t2)       by Simpl
    //@formatter:on
  )
}