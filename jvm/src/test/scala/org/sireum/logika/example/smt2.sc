// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

@pure def foo(p: B, q: B, r: B): Unit = {
  Contract(
    Requires(p __>: q, q __>: r),
    Ensures(p __>: r)
  )
  Deduce(
    1 (  p __>: q         ) by Premise,
    2 (  q __>: r         ) by Premise,
    3 SubProof(
      4 Assume(  p  ),
      5 (  q           ) by Auto,
      6 (  r           ) by Auto
    ),
    7 (  p __>: r         ) by Smt2("z3", 2000, 2000000) and 3
  )
}

@pure def bar(p: B, q: B, r: B): Unit = {
  Contract(
    Requires(p, q, r),
    Ensures(All{(x : Z) => q })
  )
  Deduce(
    1 (  p                 ) by Premise,
    2 Let{ a: Z => SubProof(
      3 (  q               ) by Premise,
      4 (  r               ) by Premise
    )},
    5 (  All{(x: Z) => q}  ) by Smt2("z3", 2000, 2000000) and 2
  )
}

@pure def baz(p: B, q: B, r: B): Unit = {
  Contract(
    Requires(∃{(x: Z) => p}, p __>: q, r),
    Ensures(q)
  )
  Deduce(
    1 (  ∃{(x: Z) => p}  ) by Premise,
    2 Let{ a: Z => SubProof(
      3 Assume(  p  ),
      4 (  q             ) by Auto,
      5 (  r             ) by Premise
    )},
    6 (  q               ) by Smt2("z3", 2000, 2000000) and (1, 2)
  )
}