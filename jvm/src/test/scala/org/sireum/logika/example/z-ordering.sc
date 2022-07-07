// #Sireum #Logika

import org.sireum._
import org.sireum.justification.{Auto_*, Lift, Auto}
import org.sireum.justification.natded.prop.ImplyI

@strictpure def isOrdered(seq: ZS): B = All(0 until seq.size - 1)(i => seq(i) <= seq(i + 1))

@strictpure def isOrderedH(seq: ZS): B = All(0 until seq.size)(i => All(i until seq.size)(j => seq(i) <= seq(j)))

@pure def ordered1Lemma(seq: ZS): Unit = {
  Deduce(|- (isOrderedH(seq) ->: isOrdered(seq)))
}

//@pure def ordered2LemmaFail(seq: ZS): Unit = {
//  Deduce(|- (isOrdered(seq) ->: isOrderedH(seq)))  // Could not deduce
//}

@pure def ordered2Lemma(seq: ZS): Unit = {
  Contract(
    Requires(isOrdered(seq)),
    Ensures(isOrderedH(seq))
  )
  var n = 0
  while (n < seq.size) {
    Invariant(
      Modifies(n),
      0 <= n,
      n <= seq.size,
      All(0 until seq.size - 1)(i => seq(i) <= seq(i + 1)),
      All(0 until n)(i => All(i until seq.size)(j => seq(i) <= seq(j)))
    )
    var m = n
    while (m < seq.size) {
      Invariant(
        Modifies(m),
        n <= m,
        m <= seq.size,
        All(n until m)(j => seq(n) <= seq(j))
      )
      Deduce(|- (All(n until m)(j => seq(n) <= seq(j)))) // required when SMT2 query is simplified
      m = m + 1
      Deduce(                                                 // required when SMT2 query is simplified
        //@formatter:off
        1 #> All(n until m - 1)(j => seq(n) <= seq(j))  by Auto,
        2 #> ((m - 2 >= 0) -->: (seq(m - 2) <= seq(m - 1)))  by Auto
        //@formatter:on
      )
    }
    n = n + 1
  }
}

@pure def orderedEqTheorem(seq: ZS): Unit = {
  Deduce(|- (isOrderedH(seq) == isOrdered(seq)) Proof(
    //@formatter:off
    1 #> (isOrderedH(seq) ->: isOrdered(seq))   by ordered1Lemma(seq),
    4 #> SubProof(
      5 #> Assume(isOrdered(seq)),
      6 #> isOrderedH(seq)                      by ordered2Lemma(seq) and 5,
    ),
    2 #> (isOrdered(seq) ->: isOrderedH(seq))   by ImplyI(4),
    3 #> (isOrderedH(seq) == isOrdered(seq))    by Auto_*(ISZ(1, 2))
    //@formatter:on
  ))
}


@pure def orderedEqTheoremUsingLift(seq: ZS): Unit = {
  Deduce(|- (isOrderedH(seq) == isOrdered(seq)) Proof(
    //@formatter:off
    1 #> (isOrderedH(seq) ->: isOrdered(seq))   by ordered1Lemma(seq),
    2 #> (isOrdered(seq) -->: isOrderedH(seq))  by Lift(ordered2Lemma(seq)),
    3 #> (isOrderedH(seq) == isOrdered(seq))    by Auto_*(ISZ(1, 2))
    //@formatter:on
  ))
}