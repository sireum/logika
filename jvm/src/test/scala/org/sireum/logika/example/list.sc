// #Sireum #Logika
//@Logika: --par --par-branch --background disabled

import org.sireum._

import org.sireum.justification._

@datatype trait List[T] {

  @strictpure def length: Z = this match {
    case List.Cons(_, next) => 1 + next.length
    case _ => 0
  }

  @strictpure def hd: T = this match {
    case List.Cons(value, _) => value
    case _ => halt("Trying to access hd on an empty list")
  }

  @strictpure def tl: List[T] = this match {
    case List.Cons(_, next) => next
    case _ => halt("Trying to access tl on an empty list")
  }

  @strictpure def ++(l2: List[T]): List[T] = this match {
    case l@List.Cons(_, next) => l(next = next ++ l2)
    case _ => l2
  }

  @strictpure def drop(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(_, next) => next.drop(n - 1)
      case _ => halt(s"Trying to drop $n elements from an empty list")
    }
  } else {
    this
  }

  @strictpure def take(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(value, next) => List.Cons(value, next.take(n - 1))
      case _ => halt(s"Trying to take $n elements from an empty list")
    }
  } else {
    List.empty
  }
}

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

          if (p._1 ≡ key) {

            Deduce(
              //@formatter:off
              1 (  map ≡ Cons(p, next)                                 ) by Auto,
              2 (  p._1 ≡ key                                          ) by Premise,
              3 (  update(map, key, value) ≡ Cons(key ~> value, next)  ) by RSimpl(RS(update _)), //Auto,
              4 (  lookup(update(map, key, value), key) ≡ value        ) by RSimpl(RS(lookup _))  //Auto
              //@formatter:on
            )
            return

          } else {

            //lookupUpdateEq(next, key, value) // either this or proof step #5 below

            Deduce(
              //@formatter:off
              1 (  map ≡ Cons(p, next)                                          ) by Auto,
              2 (  !(p._1 ≡ key)                                                ) by Premise,
              3 (  update(map, key, value) ≡ Cons(p, update(next, key, value))  ) by RSimpl(RS(update _)), //Auto,
              4 (  lookup(Cons(p, update(next, key, value)), key) ≡
                      lookup(update(next, key, value), key)                     ) by RSimpl(RS(lookup _)),
              5 (  lookup(update(map, key, value), key) ≡ value                 ) by Rewrite(RS(lookupUpdateEq _), 4)
              //@formatter:on
            )
            return

          }
        }
        case _ => {

          Deduce(
            //@formatter:off
            1 (  map ≡ Nil[(K, V)]()                                          ) by Auto,
            2 (  update(map, key, value) ≡ Cons(key ~> value, Nil[(K, V)]())  ) by RSimpl(RS(update _)), //Auto,
            3 (  lookup(update(map, key, value), key) ≡ value                 ) by RSimpl(RS(lookup _))  //Auto
            //@formatter:on
          )
          return

        }
      }
    }

    @pure def lookupUpdateNe[K, V](map: Map[K, V], key1: K, key2: K, value: V): Unit = {
      Contract(
        Requires(key1 ≢ key2),
        Ensures(lookup(update(map, key1, value), key2) ≡ lookup(map, key2))
      )
      map match {
        case Cons(p, next) => {
          
          if (p._1 ≡ key1) {

            Deduce(
              //@formatter:off
              1 (  key1 ≢ key2                                                 ) by Premise,
              2 (  map ≡ Cons(p, next)                                         ) by Auto,
              3 (  p._1 ≡ key1                                                 ) by Premise,
              4 (  p._1 ≢ key2                                                 ) by Auto,
              5 (  update(map, key1, value) ≡ Cons(key1 ~> value, next)        ) by RSimpl(RS(update _)), //Auto,
              6 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)  ) by RSimpl(RS(lookup _))  //Auto
              //@formatter:on
            )
            return
            
          } else {

            //lookupUpdateNe(next, key1, key2, value)

            Deduce(
              //@formatter:off
              1 (  key1 ≢ key2                                                    ) by Premise,
              2 (  map ≡ Cons(p, next)                                            ) by Auto,
              3 (  !(p._1 ≡ key1)                                                 ) by Premise,
              4 (  update(map, key1, value) ≡ Cons(p, update(next, key1, value))  ) by RSimpl(RS(update _)),
              5 (  lookup(update(next, key1, value), key2) ≡ lookup(next, key2)   ) by RSimpl(RS(lookupUpdateNe _)),
              6 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)     ) by RSimpl(RS(lookup _))
              //@formatter:on
            )
            return

          }

        }
        case _ => {
          Deduce(
            //@formatter:off
            1 (  key1 ≢ key2                                                    ) by Premise,
            2 (  map ≡ Nil[(K, V)]()                                            ) by Auto,
            3 (  update(map, key1, value) ≡ Cons(key1 ~> value, Nil[(K, V)]())  ) by RSimpl(RS(update _)), //Auto,
            4 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)     ) by RSimpl(RS(lookup _))  //Auto,
            //@formatter:on
          )
          return
          
        }
      }
    }

  }

  @strictpure def make[T](value: T): List[T] = Cons(value, Nil())

  @strictpure def empty[T]: List[T] = Nil()

  @datatype class Queue[T](val error: B, val buffer: List[T], val capacity: Z, val strategy: Queue.Strategy.Type) {

    @abs def wellFormed: B =
      0 < capacity & (strategy != Queue.Strategy.Unbounded __>: buffer.length <= capacity)

    @strictpure def isEmpty: B = buffer ≡ Nil[T]()

    @strictpure def isOneElement: B = buffer.length == 1

    @strictpure def head: T = buffer.hd

    @strictpure def tail: Queue[T] = {
      val thiz = this
      thiz(buffer = buffer.tl)
    }

    @strictpure def length: Z = buffer.length

    @strictpure def push(value: T): Queue[T] = {
      val thiz = this
      strategy match {
        case Queue.Strategy.DropEarliest =>
          if (length < capacity) thiz(buffer = buffer ++ make(value))
          else thiz(buffer = buffer.tl ++ make(value))
        case Queue.Strategy.DropLatest =>
          if (length < capacity) thiz(buffer = buffer ++ make(value))
          else this
        case Queue.Strategy.Error =>
          if (length < capacity) thiz(buffer = buffer ++ make(value))
          else thiz(error = T, buffer = empty)
        case Queue.Strategy.Unbounded =>
          thiz(buffer = buffer ++ make(value))
      }
    }

    @strictpure def pushAll(values: List[T]): Queue[T] = {
      val thiz = this
      val b = buffer ++ values
      strategy match {
        case Queue.Strategy.DropEarliest => thiz(buffer = b.drop(b.length - capacity))
        case Queue.Strategy.DropLatest => thiz(buffer = b.take(capacity))
        case Queue.Strategy.Error =>
          if (b.length <= capacity) thiz(buffer = b)
          else thiz(error = T, buffer = empty)
        case Queue.Strategy.Unbounded => thiz(buffer = b)
      }
    }

    @strictpure def drop(n: Z): Queue[T] = {
      val thiz = this
      thiz(buffer = buffer.drop(n))
    }

    @strictpure def clear: Queue[T] = {
      val thiz = this
      thiz(buffer = empty)
    }

    @strictpure def setBuffer(l: List[T]): Queue[T] = {
      val thiz = this
      thiz(buffer = l)
    }
  }

  object Queue {

    @enum object Strategy {
      "DropEarliest"
      "DropLatest"
      "Error"
      "Unbounded"
    }

    @strictpure def make[T](b: List[T], c: Z, s: Strategy.Type): Queue[T] = Queue(F, b, c, s)

    @strictpure def empty[T](c: Z, s: Strategy.Type): Queue[T] = Queue(F, Nil(), c, s)

//    @pure def wfEmpty[T](c: Z, s: Strategy.Type): Unit = {
//      Contract(
//        Ensures(empty[T](c, s).wellFormed)
//      )
//      Deduce(
//        1 (  empty[T](c, s).wellFormed  ) by RSimpl(RS(Queue.$.wellFormed _))
//      )
//    }
  }


}