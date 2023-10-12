// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def introNatDed(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p | q, r)  |-  (p & r | q & r)
    Proof(
      1 #> (p | q)             by Premise,
      2 #> r                   by Premise,
      3 #> SubProof(
        4 #> Assume(p),
        5 #> (p & r)           by andI(p, r)         and (4, 2),
        6 #> (p & r | q & r)   by orI1(p & r, q & r) and 5
      ),
      7 #> SubProof(
        8 #> Assume(q),
        9 #> (q & r)           by andI(q, r)         and (8, 2),
        10 #> (p & r | q & r)  by orI2(p & r, q & r) and 9
      ),
      11 #> (p & r | q & r)    by OrE(1, 3, 7),
    )
    //@formatter:on
  )
}

@pure def and1(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p, q, r)  |-  (r & (q & p))
    Proof(
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
    (p & (q & r))  |-  (r & p)
    Proof(
      1 #> (p & (q & r))   by Premise,
      2 #> p               by andE1(p, q & r) and 1,
      3 #> (q & r)         by andE2(p, q & r) and 1,
      4 #> r               by andE2(q, r)     and 3,
      5 #> (r & p)         by andI(r, p)      and (4, 2),
    )
    //@formatter:on
  )
}

@pure def or1(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    p  |-  (p | q)
    Proof(
      1 #> p         by Premise,
      2 #> (p | q)   by orI1(p, q) and 1,
    )
    //@formatter:on
  )
}

@pure def or2(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p & q)  |-  (p | q)
    Proof(
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
    (p & q)  |-  (p | q)
    Proof(
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
    (p | q,  r)  |-  (p & r | q & r)
    Proof(
      1 #> (p | q)                  by Premise,
      2 #> r                        by Premise,
      3 #> SubProof(
        4 #> Assume(p),
        5 #> (p & r)                by andI(p, r)         and (4, 2),
        6 #> (p & r | q & r)        by orI1(p & r, q & r) and 5
      ),
      7 #> SubProof(
        8 #> Assume(q),
        9 #> (q & r)                by andI(q, r)         and (8, 2),
        10 #> (p & r | q & r)       by orI2(p & r, q & r) and 9
      ),
      11 #> (p & r | q & r)         by OrE(1, 3, 7)
    )
    //@formatter:on
  )
}

@pure def imply1(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    ((p & q) ->: r, p ->: q, p)  |-  r
    Proof(
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
    ((p | q) ->: r,  q)  |-  r
    Proof(
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
    q  |-  (p ->: q)
    Proof(
      1 #> q                   by Premise,
      2 #> SubProof(
        3 #> Assume(p),
        4 #> q                 by Premise
      ),
      5 #> (p ->: q)           by ImplyI(2),
    )
    //@formatter:on
  )
}

@pure def imply3b(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    q  |-  (p ->: q)
    Proof(
      1 #> SubProof(
        2 #> Assume(p),
        3 #> q             by Premise
      ),
      4 #> (p ->: q)       by ImplyI(1),
    )
    //@formatter:on
  )
}

@pure def imply4(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p ->: r,  q ->: r)  |-  ((p | q) ->: r)
    Proof(
      1 #> (p ->: r)             by Premise,
      2 #> (q ->: r)             by Premise,
      3 #> SubProof(
        4 #> Assume(p | q),
        5 #> SubProof(
          6 #> Assume(p),
          7 #> r                 by implyE(p, r) and (1, 6)
        ),
        8 #> SubProof(
          9 #> Assume(q),
         10 #> r                 by implyE(q, r) and (2, 9)
        ),
        11 #> r                  by OrE(4, 5, 8)
      ),
      12 #> ((p | q) ->: r)      by ImplyI(3)
    )
    //@formatter:on
  )
}

@pure def negation1(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p | q, !p)  |-  q
    Proof(
      1 #> (p | q)        by Premise,
      2 #> (!p)           by Premise,
      3 #> SubProof(
        4 #> Assume(p),
        5 #> F            by negE(p) and (4, 2),
        6 #> q            by bottomE(q) and 5
      ),
      7 #> SubProof(
        8 #> Assume(q)
      ),
      9 #> q              by OrE(1, 3, 7),
    )
    //@formatter:on
  )
}

@pure def negation2(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (!p)  |-  (p ->: q)
    Proof(
      1 #> (!p)            by Premise,
      2 #> SubProof(
        3 #> Assume(p),
        4 #> F             by negE(p) and (3, 1),
        5 #> q             by bottomE(q) and 4
      ),
      6 #> (p ->: q)       by ImplyI(2),
    )
    //@formatter:on
  )
}

@pure def negation3(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p ->: !q)  |-  (!(p & q))
    Proof(
      1 #> (p ->: !q)         by Premise,
      2 #> SubProof(
        3 #> Assume(p & q),
        4 #> p                by andE1(p, q)   and 3,
        5 #> q                by andE2(p, q)   and 3,
        6 #> (!q)             by implyE(p, !q) and (1, 4),
        7 #> F                by negE(q)       and (5, 6)
      ),
      8 #> (!(p & q))         by NegI(2),
    )
    //@formatter:on
  )
}

@pure def negation4(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (p, q ->: !p)  |-  (!q)
    Proof(
      1 #> p              by Premise,
      2 #> (q ->: !p)     by Premise,
      3 #> SubProof(
        4 #> Assume(q),
        5 #> (!p)         by implyE(q, !p) and (2, 4),
        6 #> F            by negE(p)       and (1, 5)
      ),
      7 #> (!q)           by NegI(3),
    )
    //@formatter:on
  )
}

@pure def negation5(p: B): Unit = {
  Deduce(
    //@formatter:off
    p  |-  (!(!p))
    Proof(
      1 #> p               by Premise,
      2 #> SubProof(
        3 #> Assume(!p),
        4 #> F             by negE(p) and (1, 3)
      ),
      5 #> (!(!p))         by NegI(2),
    )
    //@formatter:on
  )
}

@pure def negation6(p: B): Unit = {
  Deduce(
    //@formatter:off
    (!(!p))  |-  p
    Proof(
      1 #> (!(!p))         by Premise,
      2 #> SubProof(
        3 #> Assume(!p),
        4 #> F             by negE(!p) and (3, 1)
      ),
      5 #> p               by PbC(2),
    )
    //@formatter:on
  )
}

@pure def negation7(p: B, q: B): Unit = {
  Deduce(
    //@formatter:off
    (!(!p | !q))  |-  (p & q)
    Proof(
      1 #> (!(!p | !q))    by Premise,
      2 #> SubProof(
        3 #> Assume(!p),
        4 #> (!p | !q)     by orI1(!p, !q)  and 3,
        5 #> F             by negE(!p | !q) and (4, 1)
      ),
      6 #> p               by PbC(2),
      7 #> SubProof(
        8 #> Assume(!q),
        9 #> (!p | !q)     by orI2(!p, !q)  and 8,
       10 #> F             by negE(!p | !q) and (9, 1)
      ),
      11 #> q              by PbC(7),
      12 #> (p & q)        by andI(p, q)    and (6, 11)
    )
    //@formatter:on
  )
}

@pure def negation8(p: B): Unit = {
  Deduce(
    //@formatter:off
    |-  (p | !p)
    Proof(
      1 #> SubProof(
        2 #> Assume(!(p | !p)),
        3 #> SubProof(
          4 #> Assume(p),
          5 #> (p | !p)           by orI1(p, !p)  and 4,
          6 #> F                  by negE(p | !p) and (5, 2)
        ),
        7 #> (!p)                 by NegI(3),
        8 #> (p | !p)             by orI2(p, !p)  and 7,
        9 #> F                    by negE(p | !p) and (8, 2)
      ),
      10 #> (p | !p)              by PbC(1),
    )
    //@formatter:on
  )
}

@pure def universal1[T](human: T => B @pure, mortal: T => B @pure, Socrates: T): Unit = {
  Deduce(
    //@formatter:off
    (
      ∀{(x: T) => human(x) ->: mortal(x)},
      human(Socrates)
    ) |-
      mortal(Socrates)
    Proof(
      1 #> ∀{(x: T) => human(x) ->: mortal(x)}        by Premise,
      2 #> human(Socrates)                            by Premise,
      3 #> (human(Socrates) ->: mortal(Socrates))     by allE((x: T) => human(x) ->: mortal(x), Socrates) and 1,
      4 #> mortal(Socrates)                           by implyE(human(Socrates), mortal(Socrates))        and (3, 2),
    )
    //@formatter:on
  )
}

@pure def universal2[T](gt: (T, T) => B @pure, inc: T => T @pure, dec: T => T @pure): Unit = {
  Deduce(
    //@formatter:off
    (
      ∀{(x: T) => gt(inc(x), x)},
      ∀{(x: T) => gt(x, dec(x))}
    ) |-
      ∀{(x: T) => gt(inc(x), x) & gt(x, dec(x))}
    Proof(
      1 #> ∀{(x: T) => gt(inc(x), x)}                   by Premise,
      2 #> ∀{(x: T) => gt(x, dec(x))}                   by Premise,
      3 #> Let { (a: T) => SubProof(
        4 #> gt(inc(a), a)                              by allE((x: T) => gt(inc(x), x), a)   and 1,
        5 #> gt(a, dec(a))                              by allE((x: T) => gt(x, dec(x)), a)   and 2,
        6 #> (gt(inc(a), a) & gt(a, dec(a)))            by andI(gt(inc(a), a), gt(a, dec(a))) and (4, 5)
      )},
      7 #> ∀{(x: T) => gt(inc(x), x) & gt(x, dec(x))}   by AllI[T](3),
    )
    //@formatter:on
  )
}

@pure def universal3[T](human: T => B @pure, mortal: T => B @pure, soul: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    (
      ∀{(x: T) => human(x) ->: mortal(x)},
      ∀{(y: T) => mortal(y) ->: soul(y)}
    ) |-
      ∀{(x: T) => human(x) ->: soul(x)}
    Proof(
      1 #> ∀{(x: T) => human(x) ->: mortal(x)}   by Premise,
      2 #> ∀{(y: T) => mortal(y) ->: soul(y)}    by Premise,
      3 #> Let { (a: T) => SubProof(
        4 #> SubProof(
          5 #> Assume(human(a)),
          6 #> (human(a) ->: mortal(a))          by allE((x: T) => human(x) ->: mortal(x), a) and 1,
          7 #> mortal(a)                         by implyE(human(a), mortal(a))               and (6, 5),
          8 #> (mortal(a) ->: soul(a))           by allE((y: T) => mortal(y) ->: soul(y), a)  and 2,
          9 #> soul(a)                           by implyE(mortal(a), soul(a))                and (8, 7)
        ),
        10 #> (human(a) ->: soul(a))             by ImplyI(4)
      )},
      11 #> ∀{(x: T) => human(x) ->: soul(x)}    by AllI[T](3),
    )
    //@formatter:on
  )
}

@pure def universal4[T](healthy: T => B @pure, happy: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    ∀{(x: T) => healthy(x) ->: happy(x)}  |-  (∀{(y: T) => healthy(y)} ->: ∀{(x: T) => happy(x)})
    Proof(
      1 #> ∀{(x: T) => healthy(x) ->: happy(x)}                   by Premise,
      2 #> SubProof(
        3 #> Assume(∀{(y: T) => healthy(y)}),
        4 #> Let { (a: T) => SubProof(
          5 #> healthy(a)                                         by allE((y: T) => healthy(y), a)              and 3,
          6 #> (healthy(a) ->: happy(a))                          by allE((x: T) => healthy(x) ->: happy(x), a) and 1,
          7 #> happy(a)                                           by implyE(healthy(a), happy(a))               and (6, 5)
        )},
        8 #> ∀{(x: T) => happy(x)}                                by AllI[T](4)
      ),
      9 #> (∀{(y: T) => healthy(y)} ->: ∀{(x: T) => happy(x)})    by ImplyI(2)
    )
    //@formatter:on
  )
}

@pure def existential1[T](human: T => B @pure, mortal: T => B @pure, Socrates: T): Unit = {
  Deduce(
    //@formatter:off
    (human(Socrates),  mortal(Socrates))  |-  ∃{(x: T) => human(x) & mortal(x)}
    Proof(
      1 #> human(Socrates)                        by Premise,
      2 #> mortal(Socrates)                       by Premise,
      3 #> (human(Socrates) & mortal(Socrates))   by andI(human(Socrates), mortal(Socrates))           and (1, 2),
      4 #> ∃{(x: T) => human(x) & mortal(x)}      by existsI((y: T) => human(y) & mortal(y), Socrates) and 3
    )
    //@formatter:on
  )
}

@pure def existential2(vowel: C => B @pure, square: (Z, Z) => C @pure, holds: (C, C) => B @pure, e: C): Unit = {
  Deduce(
    //@formatter:off
    (vowel(e), holds(square(1, 4), e))  |-  ∃{(y: C) => vowel(y) & ∃{(x: C) => holds(x, y)}}
    Proof(
      1 #> vowel(e)                                           by Premise,
      2 #> holds(square(1, 4), e)                             by Premise,
      3 #> ∃{(x: C) => holds(x, e)}                           by existsI((z: C) => holds(z, e), square(1, 4))              and 2,
      4 #> (vowel(e) & ∃{(x: C) => holds(x, e)})              by andI(vowel(e), ∃{(x: C) => holds(x, e)})                  and (1, 3),
      5 #> ∃{(y: C) => vowel(y) & ∃{(x: C) => holds(x, y)}}   by existsI((y: C) => vowel(y) & ∃{(x: C) => holds(x, y)}, e) and 4
    )
    //@formatter:on
  )
}

@pure def existential3(vowel: C => B @pure, square: (Z, Z) => C @pure, holds: (C, C) => B @pure, e: C): Unit = {
  Deduce(
    //@formatter:off
    (vowel(e), holds(square(1, 4), e))  |-  ∃{(y: C, x: C) => vowel(y) & holds(x, y)}
    Proof(
      1 #> vowel(e)                                    by Premise,
      2 #> holds(square(1, 4), e)                      by Premise,
      3 #> (vowel(e) & holds(square(1, 4), e))         by andI(vowel(e), holds(square(1, 4), e))                    and (1, 2),
      4 #> ∃{(x: C) => vowel(e) & holds(x, e)}         by existsI((z: C) => vowel(e) & holds(z, e), square(1, 4))   and 3,
      5 #> ∃{(y: C, x: C) => vowel(y) & holds(x, y)}   by existsI((z: C) => ∃{(x: C) => vowel(z) & holds(x, z)}, e) and 4,
    )
    //@formatter:on
  )
}

@pure def existential4[T](human: T => B @pure, mortal: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    (
      ∀{(x: T) => human(x) ->: mortal(x)},
      ∃{(y: T) => human(y)}
    ) |-
      ∃{(z: T) => mortal(z)}
    Proof(
      1 #> ∀{(x: T) => human(x) ->: mortal(x)}    by Premise,
      2 #> ∃{(y: T) => human(y)}                  by Premise,
      3 #> Let { (a: T) => SubProof(
        4 #> Assume(human(a)),
        5 #> (human(a) ->: mortal(a))             by allE((x: T) => human(x) ->: mortal(x), a) and 1,
        6 #> mortal(a)                            by implyE(human(a), mortal(a))               and (5, 4),
        7 #> ∃{(z: T) => mortal(z)}               by existsI((z: T) => mortal(z), a)           and 6
      )},
      8 #> ∃{(z: T) => mortal(z)}                 by ExistsE[T](2, 3),
    )
    //@formatter:on
  )
}

@pure def existential5(vowel: C => B @pure, covered: Z => B @pure, holds: (Z, C) => B @pure, gameOver: B): Unit = {
  Deduce(
    //@formatter:off
    (
      ∃{(s: Z) => covered(s) & ∃{(c: C) => vowel(c) & holds(s, c)}},
      ∃{(x: Z) => covered(x)} ->: !gameOver
    ) |- (
      !gameOver
    )
    Proof(
      1 #> ∃{(s: Z) => covered(s) & ∃{(c: C) => vowel(c) & holds(s, c)}}   by Premise,
      2 #> (∃{(x: Z) => covered(x)} ->: !gameOver)                         by Premise,
      3 #> Let { (a: Z) => SubProof(
        4 #> Assume(covered(a) & ∃{(c: C) => vowel(c) & holds(a, c)}),
        5 #> covered(a)                                                    by andE1(covered(a), ∃{(c: C) => vowel(c) & holds(a, c)}) and 4,
        6 #> ∃{(x: Z) => covered(x)}                                       by existsI((x: Z) => covered(x), a)                       and 5
      )},
      7 #> ∃{(x: Z) => covered(x)}                                         by ExistsE[Z](1, 3),
      8 #> (!gameOver)                                                     by implyE(∃{(x: Z) => covered(x)}, !gameOver)             and (2, 7),
    )
    //@formatter:on
  )
}

