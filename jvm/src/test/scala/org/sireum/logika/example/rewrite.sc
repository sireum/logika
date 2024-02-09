// #Sireum #Logika
import org.sireum._
import org.sireum.justification._

object Rules {

  @spec def zDistribute(x: Z, y: Z, z: Z) = Theorem(
    (x * z) + (y * z) == (x + y) * z
  )

  @rw val myRewriteSet: RS = RS(zDistribute _)

  @pure def zDistributeTest(c: Z, d: Z): Unit = {
    Deduce(
      (2 * c + 3 * c == d) |- (5 * c == d) Proof(
        //@formatter:off
        1  (2 * c + 3 * c == d)  by Premise,
        2  (5 * c == d)          by Rewrite(RS(zDistribute _), 1),
        3  (5 * c == d)          by Rewrite(myRewriteSet, 1)
        //@formatter:on
      )
    )
  }
}