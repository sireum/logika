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
      4 #> (q & p)         by andI(q, p)     and (2, 1),
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
      4 #> r               by andE2(q, r)     and 3,
      5 #> (r & p)         by andI(r, p)      and (4, 2),
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
      4 #> q                     by implyE(p, q)     and (2, 3),
      5 #> (p & q)               by andI(p, q)       and (3, 4),
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
      3 #> (p | q)               by orI2(p, q)       and 2,
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

@pure def imply3b(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    q |- (p ->: q) Proof(
      1 #> SubProof(
        2 #> Assume(p),
        3 #> q             by Premise,
      ),
      4 #> (p ->: q)       by ImplyI(1),
    )
    //@formatter:on
  )
}

@pure def imply4(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p ->: r,  q ->: r) |- ((p | q) ->: r) Proof(
      1 #> (p ->: r)             by Premise,
      2 #> (q ->: r)             by Premise,
      3 #> SubProof(
        4 #> Assume(p | q),
        5 #> SubProof(
          6 #> Assume(p),
          7 #> r                 by implyE(p, r) and (1, 6),
        ),
        8 #> SubProof(
          9 #> Assume(q),
         10 #> r                 by implyE(q, r) and (2, 9),
        ),
        11 #> r                  by OrE(4, 5, 8),
      ),
      12 #> ((p | q) ->: r)      by ImplyI(3),
    )
    //@formatter:on
  )
}

@pure def introNatDed(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p | q, r) |- (p & r | q & r) Proof(
      1 #> (p | q)             by Premise,
      2 #> r                   by Premise,
      3 #> SubProof(
        4 #> Assume(p),
        5 #> (p & r)           by andI(p, r)         and (4, 2),
        6 #> (p & r | q & r)   by orI1(p & r, q & r) and 5,
      ),
      7 #> SubProof(
        8 #> Assume(q),
        9 #> (q & r)           by andI(q, r)         and (8, 2),
       10 #> (p & r | q & r)   by orI2(p & r, q & r) and 9,
      ),
      11 #> (p & r | q & r)    by OrE(1, 3, 7),
    )
    //@formatter:on
  )
}

@pure def negation1(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p | q, !p) |- q Proof(
      1 #> (p | q)        by Premise,
      2 #> (!p)           by Premise,
      3 #> SubProof(
        4 #> Assume(p),
        5 #> F            by negE(p) and (4, 2),
        6 #> q            by BottomE(5),
      ),
      7 #> SubProof(
        8 #> Assume(q),
      ),
      9 #> q              by OrE(1, 3, 7),
    )
    //@formatter:on
  )
}

@pure def negation2(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (!p) |- (p ->: q) Proof(
      1 #> (!p)            by Premise,
      2 #> SubProof(
        3 #> Assume(p),
        4 #> F             by negE(p) and (3, 1),
        5 #> q             by BottomE(4),
      ),
      6 #> (p ->: q)       by ImplyI(2),
    )
    //@formatter:on
  )
}

@pure def negation3(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p ->: !q) |- (!(p & q)) Proof(
      1 #> (p ->: !q)         by Premise,
      2 #> SubProof(
        3 #> Assume(p & q),
        4 #> p                by andE1(p, q)   and 3,
        5 #> q                by andE2(p, q)   and 3,
        6 #> (!q)             by implyE(p, !q) and (1, 4),
        7 #> F                by negE(q)       and (5, 6),
      ),
      8 #> (!(p & q))         by NegI(2),
    )
    //@formatter:on
  )
}

@pure def negation4(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p, q ->: !p) |- (!q) Proof(
      1 #> p              by Premise,
      2 #> (q ->: !p)     by Premise,
      3 #> SubProof(
        4 #> Assume(q),
        5 #> (!p)         by implyE(q, !p) and (2, 4),
        6 #> F            by negE(p)       and (1, 5),
      ),
      7 #> (!q)           by NegI(3),
    )
    //@formatter:on
  )
}

@pure def negation5(p: B): Unit = {
  Deduce(
    //@formatter:off
    p |- (!(!p)) Proof(
      1 #> p               by Premise,
      2 #> SubProof(
        3 #> Assume(!p),
        4 #> F             by negE(p) and (1, 3),
      ),
      5 #> (!(!p))         by NegI(2),
    )
    //@formatter:on
  )
}

@pure def negation6(p: B): Unit = {
  Deduce(
    //@formatter:off
    (!(!p)) |- p Proof(
      1 #> (!(!p))         by Premise,
      2 #> SubProof(
        3 #> Assume(!p),
        4 #> F             by negE(!p) and (3, 1),
      ),
      5 #> p               by PbC(2),
    )
    //@formatter:on
  )
}

@pure def negation7(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (!(!p | !q)) |- (p & q) Proof(
      1 #> (!(!p | !q))    by Premise,
      2 #> SubProof(
        3 #> Assume(!p),
        4 #> (!p | !q)     by orI1(!p, !q)  and 3,
        5 #> F             by negE(!p | !q) and (4, 1),
      ),
      6 #> p               by PbC(2),
      7 #> SubProof(
        8 #> Assume(!q),
        9 #> (!p | !q)     by orI2(!p, !q)  and 8,
       10 #> F             by negE(!p | !q) and (9, 1),
      ),
      11 #> q              by PbC(7),
      12 #> (p & q)        by andI(p, q)    and (6, 11),
    )
    //@formatter:on
  )
}

@pure def negation8(p: B): Unit = {
  Deduce(
    //@formatter:off
    |- (p | !p) Proof(
      1 #> SubProof(
        2 #> Assume(!(p | !p)),
        3 #> SubProof(
          4 #> Assume(p),
          5 #> (p | !p)           by orI1(p, !p)  and 4,
          6 #> F                  by negE(p | !p) and (5, 2),
        ),
        7 #> (!p)                 by NegI(3),
        8 #> (p | !p)             by orI2(p, !p)  and 7,
        9 #> F                    by negE(p | !p) and (8, 2),
      ),
      10 #> (p | !p)              by PbC(1),
    )
    //@formatter:on
  )
}

@pure def or1(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    p |- (p | q) Proof(
      1 #> p         by Premise,
      2 #> (p | q)   by orI1(p, q) and 1,
    )
    //@formatter:on
  )
}

@pure def or2(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p & q) |- (p | q) Proof(
      1 #> (p & q)   by Premise,
      2 #> p         by andE1(p, q) and 1,
      3 #> (p | q)   by orI1(p, q)  and 2,
    )
    //@formatter:on
  )
}

@pure def or2b(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p & q) |- (p | q) Proof(
      1 #> (p & q)   by Premise,
      2 #> q         by andE2(p, q) and 1,
      3 #> (p | q)   by orI2(p, q)  and 2,
    )
    //@formatter:on
  )
}

@pure def or3(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p | q,  r) |- (p & r | q & r) Proof(
      1 #> (p | q)                  by Premise,
      2 #> r                        by Premise,
      3 #> SubProof(
        4 #> Assume(p),
        5 #> (p & r)                by andI(p, r)         and (4, 2),
        6 #> (p & r | q & r)        by orI1(p & r, q & r) and 5,
      ),
      7 #> SubProof(
        8 #> Assume(q),
        9 #> (q & r)                by andI(q, r)         and (8, 2),
       10 #> (p & r | q & r)        by orI2(p & r, q & r) and 9,
      ),
     11 #> (p & r | q & r)          by OrE(1, 3, 7),
    )
    //@formatter:on
  )
}


