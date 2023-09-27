// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@pure def andI(p: B, q: B): Unit = {
  Deduce((p, q) |- (p & q))
}

@pure def andE1(p: B, q: B): Unit = {
  Deduce((p & q) |- p)
}

@pure def andE2(p: B, q: B): Unit = {
  Deduce((p & q) |- q)
}

@pure def orI1(p: B, q: B): Unit = {
  Deduce(p |- (p | q))
}

@pure def orI2(p: B, q: B): Unit = {
  Deduce(q |- (p | q))
}

@pure def implyE(p: B, q: B): Unit = {
  Deduce((p ->: q, p) |- q)
}

@pure def negE(p: B): Unit = {
  Deduce((p, !p) |- F)
}

@pure def allE[T](P: T => B@pure, E: T): Unit = {
  Deduce(All { (x: T) => P(x) } |- P(E))
}

@pure def existsI[T](P: T => B@pure, E: T): Unit = {
  Deduce(P(E) |- Exists { (x: T) => P(x) })
}
