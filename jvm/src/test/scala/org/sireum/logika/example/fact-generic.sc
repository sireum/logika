// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification.ClaimOf

@spec def ne[T](t1: T, t2: T): B = $

@spec def neFact[T] = Fact(
  ∀{ (t1: T, t2: T) => ne(t1, t2) == (t1 != t2) }
)

def neImpl[A](t1: A, t2: A): B = {
  Contract(
    Ensures(Res == ne(t1, t2))
  )
  Deduce(
    ∀{ (t1: A, t2: A) => ne(t1, t2) == (t1 != t2) } by ClaimOf(neFact[A] _),
    ∀{ (t1: A, t2: A) => ne[A](t1, t2) == (t1 != t2) } by ClaimOf(neFact[A] _)
  )
  return t1 != t2
}