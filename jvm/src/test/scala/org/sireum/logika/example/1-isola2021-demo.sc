// #Sireum #Logika
//@Logika: --background type
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._


@pure def existential4[T](human: T => B @pure, mortal: T => B @pure): Unit = {
  Deduce(
    //@formatter:off
    (  ∀{(x: T) => human(x) ->: mortal(x)},  ∃{(y: T) => human(y)}  )  ⊢  ∃{(z: T) => mortal(z)}
    Proof(
      "All humans are mortals"
        #> ∀{(x: T) => human(x) ->: mortal(x)}    by Premise,
      2 #> ∃{(y: T) => human(y)}                  by Premise,
      5 #> Let { (a: T) => SubProof(
        4 #> Assume(human(a)),
        9 #> (human(a) ->: mortal(a))             by allE((x: T) => human(x) ->: mortal(x), a) and "All humans are mortals",
        6 #> mortal(a)                            by implyE(human(a), mortal(a))               and (9, 4),
        7 #> ∃{(z: T) => mortal(z)}               by existsI((z: T) => mortal(z), a)           and 6
      )},
      8 #> ∃{(z: T) => mortal(z)}                 by ExistsE[T](2, 5),
    )
    //@formatter:on
  )
}

