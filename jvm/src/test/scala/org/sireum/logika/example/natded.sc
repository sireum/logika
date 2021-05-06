// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def and1(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p, q, r) |- (r & (q & p)) Proof(
      1 #> p               by Premise,
      2 #> q               by Premise,
      3 #> r               by Premise,
      4 #> (q & p)         by andI(q, p) and (2, 1),
      5 #> (r & (q & p))   by andI(r, q & p) and (3, 4),
    )
    //@formatter:on
  )
}

@pure def and2(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p & (q & r)) |- (r & p) Proof(
      1 #> (p & (q & r))   by Premise,
      2 #> p               by andE1(p, q & r) and 1,
      3 #> (q & r)         by andE2(p, q & r) and 1,
      4 #> r               by andE2(q, r) and 3,
      5 #> (r & p)         by andI(r, p) and (4, 2),
    )
    //@formatter:on
  )
}