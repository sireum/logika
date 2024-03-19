// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.{Lift, Auto}
import org.sireum.justification.natded.prop.ImplyI

@strictpure def isOrdered(seq: ZS): B = All(0 until seq.size - 1)(i => seq(i) <= seq(i + 1))

@strictpure def isOrderedH(seq: ZS): B = All(0 until seq.size)(i => All(i until seq.size)(j => seq(i) <= seq(j)))

@pure def ordered1Lemma(seq: ZS): Unit = {
  Deduce(|- (isOrderedH(seq) __>: isOrdered(seq)))
}

//@pure def ordered2LemmaFail(seq: ZS): Unit = {
//  Deduce(|- (isOrdered(seq) __>: isOrderedH(seq)))  // Could not deduce
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
        1 (  All(n until m - 1)(j => seq(n) <= seq(j))  ) by Auto,
        2 (  (m - 2 >= 0) ___>: (seq(m - 2) <= seq(m - 1))  ) by Auto
        //@formatter:on
      )
    }
    n = n + 1
  }
}

@pure def orderedEqTheorem(seq: ZS): Unit = {
  Deduce(|- (isOrderedH(seq) == isOrdered(seq)) Proof(
    //@formatter:off
    1 (  isOrderedH(seq) __>: isOrdered(seq)   ) by ordered1Lemma(seq),
    2 #> SubProof(
      3 #> Assume(  isOrdered(seq)  ),
      4 (  isOrderedH(seq)                  ) by ordered2Lemma(seq) and 3
    ),
    5 (  isOrdered(seq) __>: isOrderedH(seq)   ) by ImplyI(2),
    6 (  isOrderedH(seq) == isOrdered(seq)  ) by Auto and (1, 5)
    //@formatter:on
  ))
}


@pure def orderedEqTheoremUsingLift(seq: ZS): Unit = {
  Deduce(|- (isOrderedH(seq) == isOrdered(seq)) Proof(
    //@formatter:off
    1 (  isOrderedH(seq) __>: isOrdered(seq)   ) by ordered1Lemma(seq),
    2 (  isOrdered(seq) ___>: isOrderedH(seq)   ) by Lift(ordered2Lemma(seq)),
    3 (  isOrderedH(seq) == isOrdered(seq)  ) by Auto and (1, 2)
    //@formatter:on
  ))
}