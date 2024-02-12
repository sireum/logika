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
      (c === d, c + 1 === 3) |- (d + 1 === 3) Proof(
        //@formatter:off
        1  (c == d)  by Premise,
        2  (c + 1 == 3) by Premise,
        3  (d + 1 == 3) by Rewrite(RS(subst _), 2) and (1, 2)
        //@formatter:on
      )
    )
  }
}