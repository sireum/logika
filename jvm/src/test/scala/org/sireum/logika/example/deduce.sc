// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

@pure def squareNonNeg(n: Z): Unit = {
  Contract(
    Ensures(n * n >= 0, !(n * n < 0))
  )
  Deduce(
    //@formatter:off
    1 #>  (n * n >= 0)  by Auto,
    2 #>  !(n * n < 0)  by Auto T
    //@formatter:on
  )
}

@pure def andElim1(p: B, q: B): Unit = {
  Contract(
    Requires(p & q),
    Ensures(p)
  )
  Deduce(
    //@formatter:off
    1 #>  (p & q)  by Auto,
    2 #>  p        by Auto and 1
    //@formatter:on
  )
}

@pure def andIntro(p: B, q: B): Unit = {
  Contract(
    Requires(p, q),
    Ensures(p & q)
  )
  Deduce(
    //@formatter:off
    1 #>  p        by Auto,
    2 #>  q        by Auto,
    3 #>  (p & q)  by Auto and (1, 2)
    //@formatter:on
  )
}

def andIntroInceptionExample(x: Z, y: Z): B = {
  Contract(
    Requires(x > 0, y > 0),
    Ensures((x > 0) & (y > 0))
  )

  Deduce(
    //@formatter:off
    1 #> (x > 0)                by Auto,
    2 #> (y > 0)                by Auto,
    3 #> ((x > 0) & (y > 0))    by andIntro(x > 0, y > 0) and (1, 2),
    4 #> ((x > 0) & (y > 0))    by andIntro(p = x > 0, q = y > 0) and (1, 2),
    5 #> ((x > 0) & (y > 0))    by andIntro(x > 0, y > 0),
    6 #> ((x > 0) & (y > 0))    by andIntro(q = y > 0, p = x > 0)
    //7 #> ((x > 0) & (y > 0))    by andIntro _ and (1, 2),
    //@formatter:on
  )
  return T
}

@pure def orIntro1(p: B, q: B): Unit = {
  Contract(
    Requires(p),
    Ensures(p | q)
  )
  Deduce(
    //@formatter:off
    1 #>  p        by Auto,
    2 #>  (p | q)  by Auto and 1
    //@formatter:on
  )
}

@pure def implyElim(p: B, q: B): Unit = {
  Contract(
    Requires(p ->: q, p),
    Ensures(q)
  )
  Deduce(
    1 #>  (p ->: q)        by Auto,
    2 #>  p                by Auto,
    3 #>  q                by Smt2("z3", 2000, 1000000) and (1, 2)
  )
}

