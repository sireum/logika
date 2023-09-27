// #Sireum #Logika
//@Logika: --background type
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
    "All humans are mortals"
      #> ∀{(x: T) => human(x) ->: mortal(x)}        by Auto,
    1 #> human(Socrates)                            by Auto,
    2 #> (human(Socrates) ->: mortal(Socrates))     by allE((x: T) => human(x) ->: mortal(x), Socrates) and "All humans are mortals",
    3 #> mortal(Socrates)                           by implyE(human(Socrates), mortal(Socrates))        and (2, 1)
    //@formatter:on
  )
}
