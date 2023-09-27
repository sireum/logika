// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.{ClaimOf, Auto}
import org.sireum.justification.natded.prop.{negE, ImplyI}

@spec def eq[T](t1: T, t2: T): B = $

@spec def eqFact[T](t1: T, t2: T) = Fact(
  eq(t1, t2) == (t1 == t2)
)

@spec def eqSymmetric[A](t1: A, t2: A) = Theorem(
  eq(t1, t2) == eq(t2, t1),
  Proof(
    //@formatter:off
    1 #> ∀ { (t1: A, t2: A) => eq(t1, t2) == (t1 == t2) } by ClaimOf(eqFact[A] _),
    2 #> (eq(t1, t2) == eq(t2, t1))                       by Auto
    //@formatter:on
  )
)

@spec def `Obvious 0 < 1` = Lemma(
  z"0" < z"1",
  Proof(
    (z"0" < z"1") by Auto
  )
)

@spec def obvious = Lemma(
  !(z"0" < z"1") ->: F,
  Proof(
    //@formatter:off
    1 #> SubProof(
      2 #> Assume(!(z"0" < z"1")),
      3 #> (z"0" < z"1")            by ClaimOf(`Obvious 0 < 1` _),
      4 #> F                        by negE(z"0" < z"1") and (3, 2)
    ),
    5 #> (!(z"0" < z"1") ->: F)     by ImplyI(1)
    //@formatter:on
  )
)
