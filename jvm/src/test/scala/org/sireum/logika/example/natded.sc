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

@pure def imply1(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    ((p & q) ->: r, p ->: q, p) |- r Proof(
      1 #> ((p & q) ->: r)       by Premise,
      2 #> (p ->: q)             by Premise,
      3 #> p                     by Premise,
      4 #> q                     by implyE(p, q) and (2, 3),
      5 #> (p & q)               by andI(p, q) and (3, 4),
      6 #> r                     by implyE(p & q, r) and (1, 5),
    )
    //@formatter:on
  )
}

@pure def imply2(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    ((p | q) ->: r,  q) |- r Proof(
      1 #> ((p | q) ->: r)       by Premise,
      2 #> q                     by Premise,
      3 #> (p | q)               by orI2(p, q) and 2,
      4 #> r                     by implyE(p | q, r) and (1, 3),
    )
    //@formatter:on
  )
}

@pure def imply3a(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    q |- (p ->: q) Proof(
      1 #> q                   by Premise,
      2 #> SubProof(
        3 #> Assume(p),
        4 #> q                 by Premise,
      ),
      5 #> (p ->: q)           by ImplyI(2),
    )
    //@formatter:on
  )
}