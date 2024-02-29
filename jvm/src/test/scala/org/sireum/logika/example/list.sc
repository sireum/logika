// #Sireum #Logika
//@Logika: --par --par-branch --background disabled

import org.sireum._

import org.sireum.justification._

@datatype trait List[T]

object List {

  @datatype class Nil[T] extends List[T]

  @datatype class Cons[T](val value: T, val next: List[T]) extends List[T]

  type Map[K, V] = List[(K, V)]

  object Map {

    @tailrec @abs def lookup[K, V](map: Map[K, V], key: K): V = map match {
      case Cons((k, v), next) => if (k ≡ key) v else lookup(next, key)
      case _ => halt(s"Could not lookup $key")
    }

    @abs def update[K, V](map: Map[K, V], key: K, value: V): Map[K, V] = map match {
      case Cons(p, next) =>
        if (p._1 ≡ key) Cons(key ~> value, next)
        else Cons(p, update(next, key, value))
      case _ => Cons(key ~> value, Nil())
    }

    @pure def lookupUpdateEq[K, V](map: Map[K, V], key: K, value: V): Unit = {
      Contract(
        Ensures(lookup(update(map, key, value), key) ≡ value)
      )

      map match {
        case Cons(p, next) => {

          Deduce((  map ≡ Cons(p, next)  ) by Auto)

          if (p._1 ≡ key) {

            Deduce(
              //@formatter:off
              1  (  map ≡ Cons(p, next)                                 ) by Auto,
              2  (  p._1 ≡ key                                          ) by Premise,
              3  (  update(map, key, value) ≡ Cons(key ~> value, next)  ) by RSimpl(RS(update[K, V] _)), //Auto,
              4  (  lookup(update(map, key, value), key) ≡ value        ) by RSimpl(RS(lookup[K, V] _)) //Auto
              //@formatter:on
            )

          } else {

            Deduce(
              //@formatter:off
              1  (  map ≡ Cons(p, next)                                          ) by Auto,
              2  (  p._1 ≢ key                                                   ) by Auto,
              3  (  update(map, key, value) ≡ Cons(p, update(next, key, value))  ) by Auto,
              4  (  lookup(Cons(p, update(next, key, value)), key) ≡
                    lookup(update(next, key, value), key)                        ) by RSimpl(RS(lookup[K, V] _)),
              5  (  lookup(Cons(p, update(next, key, value)), key) ≡ value       ) by Rewrite(RS(lookupUpdateEq[K, V] _), 4)
              //@formatter:on
            )

          }
        }
        case _ => {

          Deduce(
            //@formatter:off
            1  (  map ≡ Nil[(K, V)]()                                          ) by Auto,
            2  (  update(map, key, value) ≡ Cons(key ~> value, Nil[(K, V)]())  ) by Auto,
            3  (  lookup(update(map, key, value), key) ≡ value                 ) by Auto
            //@formatter:on
          )

        }
      }
    }

    @pure def lookupUpdateNe[K, V](map: Map[K, V], key1: K, key2: K, value: V): Unit = {
      Contract(
        Requires(key1 ≢ key2),
        Ensures(lookup(update(map, key1, value), key2) ≡ lookup(map, key1))
      )
      map match {
        case Cons(p, next) =>
          Deduce(
            //@formatter:off
            1  (  map ≡ Cons(p, next)  ) by Auto
            //@formatter:on
          )
        case _ =>
          Deduce(
            //@formatter:off
            1  (  map ≡ Nil[(K, V)]()  ) by Auto
            //@formatter:on
          )
      }
      halt("TODO")
    }

  }
}