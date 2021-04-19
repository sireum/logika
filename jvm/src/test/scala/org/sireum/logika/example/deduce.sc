// #Sireum #Logika
import org.sireum._

def square(n: Z): Z = {
  Contract(
    Ensures(
      Res[Z] == n * n,
      Res[Z] >= 0
    )
  )
  Deduce(
    //@formatter:off
    1 #>  (n * n >= 0)  by "auto",
    2 #>  !(n * n < 0)  by "auto"(1)
    //@formatter:on
  )
  return n * n
}

def andElim1(p: B, q: B): B = {
  Contract(
    Requires(p & q),
    Ensures(
      Res[B] == p,
      Res[B]
    )
  )
  Deduce(
    //@formatter:off
    1 #>  (p & q)  by "auto",
    2 #>  p        by "auto"(1)
    //@formatter:on
  )
  return p
}

def andIntro(p: B, q: B): B = {
  Contract(
    Requires(p, q),
    Ensures(
      Res[B] == p & q,
      Res[B]
    )
  )
  Deduce(
    //@formatter:off
    1 #>  p        by "auto",
    2 #>  q        by "auto",
    3 #>  (p & q)  by "auto"(1, 2)
    //@formatter:on
  )
  return p & q
}

def orIntro1(p: B, q: B): B = {
  Contract(
    Requires(p),
    Ensures(
      Res[B] == p | q,
      Res[B]
    )
  )
  Deduce(
    //@formatter:off
    1 #>  p        by "auto",
    2 #>  (p | q)  by "auto"(1)
    //@formatter:on
  )
  return p | q
}
