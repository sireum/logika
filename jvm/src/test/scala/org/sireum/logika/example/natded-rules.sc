// #Sireum #Logika

import org.sireum._

@pure def andI(p: B, q: B): Unit = {
  Contract(
    Requires(p, q),
    Ensures(p & q)
  )
}

@pure def andE1(p: B, q: B): Unit = {
  Contract(
    Requires(p & q),
    Ensures(p)
  )
}

@pure def andE2(p: B, q: B): Unit = {
  Contract(
    Requires(p & q),
    Ensures(q)
  )
}

@pure def orI1(p: B, q: B): Unit = {
  Contract(
    Requires(p),
    Ensures(p | q)
  )
}

@pure def orI2(p: B, q: B): Unit = {
  Contract(
    Requires(q),
    Ensures(p | q)
  )
}

@pure def implyE(p: B, q: B): Unit = {
  Contract(
    Requires(p ->: q, p),
    Ensures(q)
  )
}

@pure def negE(p: B): Unit = {
  Contract(
    Requires(p, !p),
    Ensures(F)
  )
}

@pure def allE[T](P: T => B @pure, E: T): Unit = {
  Contract(
    Requires(All{(x: T) => P(x)}),
    Ensures(P(E))
  )
}

@pure def existsI[T](P: T => B @pure, E: T): Unit = {
  Contract(
    Requires(P(E)),
    Ensures(Exists{(x: T) => P(x)})
  )
}
