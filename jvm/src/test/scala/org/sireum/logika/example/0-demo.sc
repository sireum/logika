// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._


def copy(): Unit = {
  val s1 = MSZ(1, 2, 3)
  val s2 = s1
  s2(0) = 4
  assert(s2(0) == 4)
  println("s1 = ", s1, ", s2 = ", s2)
}

copy()


@pure def universal1[T](human: T => B @pure, mortal: T => B @pure, Socrates: T): Unit = {
  Contract(
    Requires(
      ∀ { (x: T) => human(x) ->: mortal(x) },
      human(Socrates)
    ),
    Ensures(
      mortal(Socrates)
    )
  )
  Deduce(
    //@formatter:off
    sn"All humans are mortals"
      #> ∀{(x: T) => human(x) ->: mortal(x)}        by Premise,
    1 #> human(Socrates)                            by Premise,
    2 #> (human(Socrates) ->: mortal(Socrates))     by allE((x: T) => human(x) ->: mortal(x), Socrates) and sn"All humans are mortals",
    3 #> mortal(Socrates)                           by implyE(human(Socrates), mortal(Socrates))        and (2, 1),
    //@formatter:on
  )
}


@pure def existential4[T](human: T => B @pure, mortal: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    (  ∀{(x: T) => human(x) ->: mortal(x)},  ∃{(y: T) => human(y)}  )  ⊢  ∃{(z: T) => mortal(z)}
    Proof(
      1 #> ∀{(x: T) => human(x) ->: mortal(x)}    by Premise,
      2 #> ∃{(y: T) => human(y)}                  by Premise,
      3 #> Let { (a: T) => SubProof(
        4 #> Assume(human(a)),
        5 #> (human(a) ->: mortal(a))             by allE((x: T) => human(x) ->: mortal(x), a) and 1,
        6 #> mortal(a)                            by implyE(human(a), mortal(a))               and (5, 4),
        7 #> ∃{(z: T) => mortal(z)}               by existsI((z: T) => mortal(z), a)           and 6,
      )},
      8 #> ∃{(z: T) => mortal(z)}                 by ExistsE[T](2, 3),
    )
    //@formatter:on
  )
}

