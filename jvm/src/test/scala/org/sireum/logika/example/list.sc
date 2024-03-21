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

  @strictpure def tlLax: List[T] = this match {
    case List.Cons(_, next) => next
    case _ => List.Nil()
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

  @strictpure def dropLax(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(_, next) => next.dropLax(n - 1)
      case _ => List.empty
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

  @strictpure def takeLax(n: Z): List[T] = if (n > 0) {
    this match {
      case List.Cons(value, next) => List.Cons(value, next.takeLax(n - 1))
      case _ => List.empty
    }
  } else {
    List.empty
  }
}

object List {

  @datatype class Nil[T] extends List[T]

  @datatype class Cons[T](val value: T, val next: List[T]) extends List[T]

  @pure def emptyZeroLength[T](l: List[T]): Unit = {
    Contract(
      Ensures(l.length >= 0)
    )

    l match {
      case Cons(a, next) => {

        emptyZeroLength(next)

        Deduce(
          //@formatter:off
          1 (  l ≡ Cons(a, next)             ) by Auto,
          2 (  next.length >= 0              ) by Premise,
          3 (  l.length ≡ (1 + next.length)  ) by Auto,
          4 (  l.length >= 0                 ) by Auto and (2, 3)
          //@formatter:on
        )
        return
      }
      case _ => {
        Deduce(
          //@formatter:off
          1 (  l ≡ Nil[T]()   ) by Auto,
          2 (  l.length >= 0  ) by Auto
          //@formatter:on
        )
        return
      }
    }
  }

  @pure def emptyZeroLengthInductExpansionTest[T](l: List[T]): Unit = {
    Contract(
      Ensures(l.length >= 0)
    )

    l: @induct // to be expanded

    halt("To be filled in")
  }

  @pure def emptyZeroLengthInduct[T](l: List[T]): Unit = {
    Contract(
      Ensures(l.length >= 0)
    )

    (l : @induct) match {
      case Cons(value, next) => {
        Deduce(
          //@formatter:off
          1 (  l ≡ List.Cons[T](value, next)  ) by Premise, // auto-generated
          2 (  next.length >= 0               ) by Premise, // auto-generated
          3 (  l.length ≡ (1 + next.length)   ) by Simpl,   // Auto,
          4 (  l.length >= 0                  ) by Auto and (2, 3)
          //@formatter:on
        )
        return
      }
      case Nil() => {
        Deduce(
          //@formatter:off
          1 (  l ≡ List.Nil[T]()  ) by Premise, // auto-generated
          2 (  l.length >= 0      ) by Simpl    // Auto
          //@formatter:on
        )
        return
      }
    }
  }

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

            lookupUpdateEq(next, key, value)

            Deduce(
              //@formatter:off
              1 (  map ≡ Cons(p, next)                                          ) by Auto,
              2 (  !(p._1 ≡ key)                                                ) by Premise,
              3 (  update(map, key, value) ≡ Cons(p, update(next, key, value))  ) by RSimpl(RS(update _)), //Auto,
              4 (  lookup(Cons(p, update(next, key, value)), key) ≡
                     lookup(update(next, key, value), key)                      ) by RSimpl(RS(lookup _)),
              5 (  lookup(update(next, key, value), key) ≡ value                ) by Auto,
              6 (  lookup(update(map, key, value), key) ≡ value                 ) by Rewrite(RS(lookup _), 5)
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

    @pure def lookupUpdateEqInduct[K, V](map: Map[K, V], key: K, value: V): Unit = {
      Contract(
        Ensures(lookup(update(map, key, value), key) ≡ value)
      )

      (map: @induct) match {
        case Cons(p, next) => {

          if (p._1 ≡ key) {

            Deduce(
              //@formatter:off
              1 (  map ≡ Cons(p, next)                                 ) by Premise, // auto-generated
              2 (  p._1 ≡ key                                          ) by Premise,
              3 (  update(map, key, value) ≡ Cons(key ~> value, next)  ) by RSimpl(RS(update _)), //Auto,
              4 (  lookup(update(map, key, value), key) ≡ value        ) by RSimpl(RS(lookup _))  //Auto
              //@formatter:on
            )
            return

          } else {

            Deduce(
              //@formatter:off
              1 (  map ≡ Cons(p, next)                                          ) by Premise, // auto-generated
              2 (  lookup(update(next, key, value), key) ≡ value                ) by Premise, // auto-generated
              3 (  !(p._1 ≡ key)                                                ) by Premise,
              4 (  update(map, key, value) ≡ Cons(p, update(next, key, value))  ) by RSimpl(RS(update _)), //Auto,
              5 (  lookup(Cons(p, update(next, key, value)), key) ≡
                     lookup(update(next, key, value), key)                      ) by RSimpl(RS(lookup _)) and (3, 4),
              6 (  lookup(update(map, key, value), key) ≡ value                 ) by Rewrite(RS(lookup _), 2)
              //@formatter:on
            )
            return

          }
        }
        case Nil() => {

          Deduce(
            //@formatter:off
            1 (  map ≡ Nil[(K, V)]()                                          ) by Premise, // auto-generated
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

            lookupUpdateNe(next, key1, key2, value)

            if (p._1 ≡ key2) {
              Deduce(
                //@formatter:off
                1 (  key1 ≢ key2                                                    ) by Premise,
                2 (  map ≡ Cons(p, next)                                            ) by Auto,
                3 (  !(p._1 ≡ key1)                                                 ) by Premise,
                4 (  p._1 ≡ key2                                                    ) by Premise,
                5 (  update(map, key1, value) ≡ Cons(p, update(next, key1, value))  ) by RSimpl(RS(update _)),
                6 (  lookup(update(next, key1, value), key2) ≡ lookup(next, key2)   ) by Auto,
                7 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)     ) by RSimpl(RS(lookup _))
                //@formatter:on
              )
            } else {
              Deduce(
                //@formatter:off
                1 (  key1 ≢ key2                                                    ) by Premise,
                2 (  map ≡ Cons(p, next)                                            ) by Auto,
                3 (  !(p._1 ≡ key1)                                                 ) by Premise,
                4 (  !(p._1 ≡ key2)                                                 ) by Premise,
                5 (  update(map, key1, value) ≡ Cons(p, update(next, key1, value))  ) by RSimpl(RS(update _)),
                6 (  lookup(update(next, key1, value), key2) ≡ lookup(next, key2)   ) by Auto,
                7 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)     ) by RSimpl(RS(lookup _))
                //@formatter:on
              )
            }
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

    @pure def lookupUpdateNeInduct[K, V](map: Map[K, V], key1: K, key2: K, value: V): Unit = {
      Contract(
        Requires(key1 ≢ key2),
        Ensures(lookup(update(map, key1, value), key2) ≡ lookup(map, key2))
      )
      (map: @induct) match {
        case Cons(p, next) => {

          if (p._1 ≡ key1) {

            Deduce(
              //@formatter:off
              1 (  map ≡ Cons(p, next)                                         ) by Premise, // auto-generated
              2 (  key1 ≢ key2                                                 ) by Premise,
              3 (  p._1 ≡ key1                                                 ) by Premise,
              4 (  p._1 ≢ key2                                                 ) by Auto,
              5 (  update(map, key1, value) ≡ Cons(key1 ~> value, next)        ) by RSimpl(RS(update _)), //Auto,
              6 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)  ) by RSimpl(RS(lookup _))  //Auto
              //@formatter:on
            )
            return

          } else {

            if (p._1 ≡ key2) {
              Deduce(
                //@formatter:off
                1 (  map ≡ Cons(p, next)                                            ) by Premise, // auto-generated
                2 (  lookup(update(next, key1, value), key2) ≡ lookup(next, key2)   ) by Premise, // auto-generated
                3 (  key1 ≢ key2                                                    ) by Premise,
                4 (  !(p._1 ≡ key1)                                                 ) by Premise,
                5 (  p._1 ≡ key2                                                    ) by Premise,
                6 (  update(map, key1, value) ≡ Cons(p, update(next, key1, value))  ) by RSimpl(RS(update _)),
                7 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)     ) by RSimpl(RS(lookup _))
                //@formatter:on
              )
            } else {
              Deduce(
                //@formatter:off
                1 (  map ≡ Cons(p, next)                                            ) by Premise, // auto-generated
                2 (  lookup(update(next, key1, value), key2) ≡ lookup(next, key2)   ) by Premise, // auto-generated
                3 (  key1 ≢ key2                                                    ) by Premise,
                4 (  !(p._1 ≡ key1)                                                 ) by Premise,
                5 (  !(p._1 ≡ key2)                                                 ) by Premise,
                6 (  update(map, key1, value) ≡ Cons(p, update(next, key1, value))  ) by RSimpl(RS(update _)),
                7 (  lookup(update(map, key1, value), key2) ≡ lookup(map, key2)     ) by RSimpl(RS(lookup _))
                //@formatter:on
              )
            }
            return

          }

        }
        case Nil() => {
          Deduce(
            //@formatter:off
            1 (  map ≡ Nil[(K, V)]()                                            ) by Premise, // auto-generated
            2 (  key1 ≢ key2                                                    ) by Premise,
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
      thiz(buffer = buffer.tlLax)
    }

    @strictpure def length: Z = buffer.length

    @strictpure def push(value: T): Queue[T] = {
      val thiz = this
      strategy match {
        case Queue.Strategy.DropEarliest =>
          if (length < capacity) thiz(buffer = buffer ++ make(value))
          else thiz(buffer = buffer.tlLax ++ make(value))
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
      thiz(buffer = buffer.dropLax(n))
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

    @pure def wfEmpty[T](c: Z, s: Strategy.Type): Unit = {
      Contract(
        Requires(0 < c),
        Ensures(empty[T](c, s).wellFormed)
      )
      Deduce(
        //@formatter:off
        1 (  0 < c                      ) by Premise,
        2 (  empty[T](c, s).wellFormed  ) by RSimpl(RS(Queue.$$.wellFormed _)) // Auto
        //@formatter:on
      )
    }

    @pure def wfEmptyAuto[T](c: Z, s: Strategy.Type): Unit = {
      Contract(
        Requires(0 < c),
        Ensures(empty[T](c, s).wellFormed)
      )
    }

    @pure def singleQueueHead[T](q: Queue[T], a: T): Unit = {
      Contract(
        Requires(q.buffer ≡ List.make(a)),
        Ensures(q.head ≡ a)
      )
      Deduce(
        //@formatter:off
        1 (  q.buffer ≡ List.make(a)       ) by Premise,
        2 (  q.buffer ≡ Cons[T](a, Nil())  ) by Eval(1),
        3 (  q.head ≡ a                    ) by Simpl // Auto
        //@formatter:on
      )
    }

    @pure def singleQueueHeadAuto[T](q: Queue[T], a: T): Unit = {
      Contract(
        Requires(q.buffer ≡ List.make(a)),
        Ensures(q.head ≡ a)
      )
    }

    @pure def frameTail[T](q: Queue[T]): Unit = {
      Contract(
        Ensures(
          q.tail.error ≡ q.error,
          q.tail.capacity ≡ q.capacity,
          q.tail.strategy ≡ q.strategy
        )
      )
      Deduce(
        //@formatter:off
        1 (  q.tail.error ≡ q.error        ) by Simpl, // Auto,
        2 (  q.tail.capacity ≡ q.capacity  ) by Simpl, // Auto,
        3 (  q.tail.strategy ≡ q.strategy  ) by Simpl // Auto
        //@formatter:on
      )
    }

    @pure def frameTailAuto[T](q: Queue[T]): Unit = {
      Contract(
        Ensures(
          q.tail.error ≡ q.error,
          q.tail.capacity ≡ q.capacity,
          q.tail.strategy ≡ q.strategy
        )
      )
    }

    @pure def wfTail[T](q: Queue[T]): Unit = {
      Contract(
        Requires(q.wellFormed),
        Ensures(q.tail.wellFormed)
      )

      frameTail(q)

      Deduce(
        //@formatter:off
        1 (  q.wellFormed                                                                               ) by Premise,
        2 (  q.tail.error ≡ q.error                                                                     ) by Premise,
        3 (  q.tail.capacity ≡ q.capacity                                                               ) by Premise,
        4 (  q.tail.strategy ≡ q.strategy                                                               ) by Premise,
        5 (  q.buffer.length >= q.tail.length                                                           ) by Auto,
        6 (  0 < q.capacity &
               (q.strategy != Queue.Strategy.Unbounded __>: q.buffer.length <= q.capacity)                 ) by Rewrite(RS(Queue.$$.wellFormed _), 1), // Auto,
        7 (  0 < q.tail.capacity &
               (q.tail.strategy != Queue.Strategy.Unbounded __>: q.tail.buffer.length <= q.tail.capacity)  ) by Auto,
        8 (  q.tail.wellFormed                                                                          ) by Rewrite(RS(Queue.$$.wellFormed _), 7) // Auto,
        //@formatter:on
      )
    }

    @pure def wfTailAuto[T](q: Queue[T]): Unit = {
      Contract(
        Requires(q.wellFormed),
        Ensures(q.tail.wellFormed)
      )
    }

    @pure def singleQueueTail[T](q: Queue[T], a: T): Unit = {
      Contract(
        Requires(q.buffer ≡ List.make(a)),
        Ensures(q.tail.buffer ≡ List.empty[T])
      )
      Deduce(
        //@formatter:off
        1 (  q.buffer ≡ List.make(a)        ) by Premise,
        2 (  q.buffer ≡ Cons[T](a, Nil())   ) by Eval(1),
        3 (  q.tail.buffer ≡ List.Nil[T]()  ) by Simpl, // Auto,
        4 (  q.tail.buffer ≡ List.empty[T]  ) by Simpl  // Auto
        //@formatter:on
      )
    }

    @pure def singleQueueTailAuto[T](q: Queue[T], a: T): Unit = {
      Contract(
        Requires(q.buffer ≡ List.make(a)),
        Ensures(q.tail.buffer ≡ List.empty[T])
      )
    }

    @pure def framePush[T](q: Queue[T], a: T): Unit = {
      Contract(
        Ensures(
          q.push(a).capacity ≡ q.capacity,
          q.push(a).strategy ≡ q.strategy
        )
      )

      (q.strategy: @induct) match {
        case Queue.Strategy.DropEarliest => {
          if (q.length < q.capacity) {
            Deduce(
              //@formatter:off
              1 (  q.strategy ≡ List.Queue.Strategy.DropEarliest  ) by Premise, // auto-generated
              2 (  q.length < q.capacity                          ) by Premise,
              3 (  q.push(a).capacity ≡ q.capacity                ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy                ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  q.strategy ≡ List.Queue.Strategy.DropEarliest  ) by Premise, // auto-generated
              2 (  !(q.length < q.capacity)                       ) by Premise,
              3 (  q.push(a).capacity ≡ q.capacity                ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy                ) by Simpl
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.DropLatest => {
          if (q.length < q.capacity) {
            Deduce(
              //@formatter:off
              1 (  q.strategy ≡ List.Queue.Strategy.DropLatest  ) by Premise, // auto-generated
              2 (  q.length < q.capacity                        ) by Premise,
              3 (  q.push(a).capacity ≡ q.capacity              ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy              ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  q.strategy ≡ List.Queue.Strategy.DropLatest  ) by Premise, // auto-generated
              2 (  !(q.length < q.capacity)                     ) by Premise,
              3 (  q.push(a).capacity ≡ q.capacity              ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy              ) by Simpl
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.Error => {
          if (q.length < q.capacity) {
            Deduce(
              //@formatter:off
              1 (  q.strategy ≡ List.Queue.Strategy.Error  ) by Premise, // auto-generated
              2 (  q.length < q.capacity                   ) by Premise,
              3 (  q.push(a).capacity ≡ q.capacity         ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy         ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  q.strategy ≡ List.Queue.Strategy.Error  ) by Premise, // auto-generated
              2 (  !(q.length < q.capacity)                ) by Premise,
              3 (  q.push(a).capacity ≡ q.capacity         ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy         ) by Simpl
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.Unbounded => {
          Deduce(
            //@formatter:off
            1 (  q.strategy ≡ List.Queue.Strategy.Unbounded  ) by Premise, // auto-generated
            2 (  q.push(a).capacity ≡ q.capacity             ) by Simpl,
            3 (  q.push(a).strategy ≡ q.strategy             ) by Simpl
            //@formatter:on
          )
          return
        }
      }
    }

    @pure def pushWithinCapacity[T](q: Queue[T], a: T): Unit = {
      Contract(
        Requires(q.length < q.capacity),
        Ensures(q.push(a).buffer ≡ (q.buffer ++ List.make(a)))
      )

      (q.strategy: @induct) match {
        case Queue.Strategy.DropEarliest => {
          Deduce(
            //@formatter:off
            1 (  q.length < q.capacity                          ) by Premise,
            2 (  q.strategy ≡ List.Queue.Strategy.DropEarliest  ) by Premise,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl
            //@formatter:on
          )
          return
        }
        case Queue.Strategy.DropLatest => {
          Deduce(
            //@formatter:off
            1 (  q.length < q.capacity                          ) by Premise,
            2 (  q.strategy ≡ List.Queue.Strategy.DropLatest    ) by Premise,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl
            //@formatter:on
          )
          return
        }
        case Queue.Strategy.Error => {
          Deduce(
            //@formatter:off
            1 (  q.length < q.capacity                          ) by Premise,
            2 (  q.strategy ≡ List.Queue.Strategy.Error         ) by Premise,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl
            //@formatter:on
          )
          return
        }
        case Queue.Strategy.Unbounded => {
          Deduce(
            //@formatter:off
            1 (  q.strategy ≡ List.Queue.Strategy.Unbounded     ) by Premise,
            2 (  q.push(a).capacity ≡ q.capacity                ) by Simpl,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl
            //@formatter:on
          )
          return
        }
      }
    }

    @pure def wfPush[T](q: Queue[T], a: T): Unit = {
      Contract(
        Requires(q.wellFormed),
        Ensures(q.push(a).wellFormed)
      )

      framePush(q, a)

      (q.strategy: @induct) match {
        case Queue.Strategy.DropEarliest => {
          if (q.length < q.capacity) {

            pushWithinCapacity(q, a)

            Deduce(
              //@formatter:off
              1 (  q.wellFormed                                   ) by Premise,
              2 (  q.push(a).capacity ≡ q.capacity                ) by Premise,
              3 (  q.push(a).strategy ≡ q.strategy                ) by Premise,
              4 (  q.strategy ≡ List.Queue.Strategy.DropEarliest  ) by Premise,
              5 (  q.length < q.capacity                          ) by Premise,
              6 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl, // Auto
              7 (  q.push(a).wellFormed                           ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  q.wellFormed                                         ) by Premise,
              2 (  q.push(a).capacity ≡ q.capacity                      ) by Premise,
              3 (  q.push(a).strategy ≡ q.strategy                      ) by Premise,
              4 (  q.strategy ≡ List.Queue.Strategy.DropEarliest        ) by Premise,
              5 (  !(q.length < q.capacity)                             ) by Premise,
              6 (  q.push(a).buffer ≡ (q.buffer.tlLax ++ List.make(a))  ) by Simpl,
              7 (  q.push(a).wellFormed                                 ) by Simpl
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.DropLatest => {
          if (q.length < q.capacity) {

            pushWithinCapacity(q, a)

            Deduce(
              //@formatter:off
              1 (  q.wellFormed                                   ) by Premise,
              2 (  q.push(a).capacity ≡ q.capacity                ) by Premise,
              3 (  q.push(a).strategy ≡ q.strategy                ) by Premise,
              4 (  q.strategy ≡ List.Queue.Strategy.DropLatest    ) by Premise,
              5 (  q.length < q.capacity                          ) by Premise,
              6 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl, // Auto,
              7 (  q.push(a).wellFormed                           ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  q.wellFormed                                 ) by Premise,
              2 (  q.push(a).capacity ≡ q.capacity              ) by Premise,
              3 (  q.push(a).strategy ≡ q.strategy              ) by Premise,
              4 (  q.strategy ≡ List.Queue.Strategy.DropLatest  ) by Premise,
              5 (  !(q.length < q.capacity)                     ) by Premise,
              6 (  q.push(a).buffer ≡ q.buffer                  ) by Simpl, // Auto,
              7 (  q.push(a).wellFormed                         ) by Simpl // Auto
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.Error => {
          if (q.length < q.capacity) {

            pushWithinCapacity(q, a)

            Deduce(
              //@formatter:off
              1 (  q.wellFormed                                   ) by Premise,
              2 (  q.push(a).capacity ≡ q.capacity                ) by Premise,
              3 (  q.push(a).strategy ≡ q.strategy                ) by Premise,
              4 (  q.strategy ≡ List.Queue.Strategy.Error         ) by Premise,
              5 (  q.length < q.capacity                          ) by Premise,
              6 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl, // Auto,
              7 (  q.push(a).wellFormed                           ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  q.wellFormed                            ) by Premise,
              2 (  q.push(a).capacity ≡ q.capacity         ) by Premise,
              3 (  q.push(a).strategy ≡ q.strategy         ) by Premise,
              4 (  q.strategy ≡ List.Queue.Strategy.Error  ) by Premise,
              5 (  !(q.length < q.capacity)                ) by Premise,
              6 (  q.push(a).buffer ≡ List.empty[T]        ) by Simpl, // Auto,
              7 (  q.push(a).wellFormed                    ) by Simpl // Auto
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.Unbounded => {
          Deduce(
            //@formatter:off
            1 (  q.wellFormed                                   ) by Premise,
            2 (  q.push(a).capacity ≡ q.capacity                ) by Premise,
            3 (  q.push(a).strategy ≡ q.strategy                ) by Premise,
            4 (  q.strategy ≡ List.Queue.Strategy.Unbounded     ) by Premise,
            5 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl,
            6 (  q.push(a).wellFormed                           ) by Simpl
            //@formatter:on
          )
          return
        }
      }

    }

    @pure def frameDrop[T](q: Queue[T], n: Z): Unit = {
      Contract(
        Ensures(
          q.drop(n).capacity ≡ q.capacity,
          q.drop(n).strategy ≡ q.strategy,
          q.drop(n).error ≡ q.error
        )
      )

      Deduce(
        //@formatter:off
        1 (  q.drop(n).capacity ≡ q.capacity  ) by Simpl,
        2 (  q.drop(n).strategy ≡ q.strategy  ) by Simpl,
        3 (  q.drop(n).error ≡ q.error        ) by Simpl
        //@formatter:on
      )
    }

    @pure def dropLeLength[T](l: List[T], n: Z): Unit = {
      Contract(
        Ensures(l.length >= l.dropLax(n).length)
      )

      if (n > 0) {
        l match {
          case Cons(e, next) => {
            dropLeLength(next, n - 1)

            Deduce(
              //@formatter:off
              1 (  n > 0                                             ) by Premise,
              2 (  l ≡ Cons(e, next)                                 ) by Auto,
              3 (  next.length >= next.dropLax(n - 1).length         ) by Premise,
              4 (  l.dropLax(n).length ≡ next.dropLax(n - 1).length  ) by Simpl,
              5 (  next.length >= l.dropLax(n).length                ) by Subst_>(4, 3),
              6 (  l.length ≡ (1 + next.length)                      ) by Simpl,
              7 (  l.length >= l.dropLax(n).length                   ) by Auto and (5, 6)
              //@formatter:on
            )
            return
          }
          case _ => {
            Deduce(
              //@formatter:off
              1 (  n > 0                            ) by Premise,
              2 (  l ≡ Nil[T]()                     ) by Auto,
              3 (  l.dropLax(n) ≡ Nil[T]()          ) by Simpl,
              4 (  l.length >= l.dropLax(n).length  ) by Simpl
              //@formatter:on
            )
            return
          }
        }
      } else {
        Deduce(
          //@formatter:off
          1 (  !(n > 0)                         ) by Premise,
          2 (  l ≡ l.dropLax(n)                 ) by Simpl,
          3 (  l.length >= l.dropLax(n).length  ) by Simpl
          //@formatter:on
        )
        return
      }

    }

    @pure def wfDrop[T](q: Queue[T], n: Z): Unit = {
      Contract(
        Requires(q.wellFormed),
        Ensures(q.drop(n).wellFormed)
      )

      frameDrop(q, n)
      dropLeLength(q.buffer, n)

      Deduce(
        //@formatter:off
        1 (  q.wellFormed                                                                                 ) by Premise,
        2 (  q.drop(n).capacity ≡ q.capacity                                                              ) by Premise,
        3 (  q.drop(n).strategy ≡ q.strategy                                                              ) by Premise,
        4 (  q.drop(n).error ≡ q.error                                                                    ) by Premise,
        5 (  q.buffer.length >= q.buffer.dropLax(n).length                                                ) by Premise,
        6 (  q.buffer.dropLax(n).length ≡ q.drop(n).length                                                ) by Simpl,
        7 (  q.buffer.length >= q.drop(n).length                                                          ) by Subst_<(6, 5),
        8 (  0 < q.capacity &
          (q.strategy != Queue.Strategy.Unbounded __>: q.buffer.length <= q.capacity)                        ) by Rewrite(RS(Queue.$$.wellFormed _), 1), // Auto,
        9 (  0 < q.drop(n).capacity &
               (q.drop(n).strategy != Queue.Strategy.Unbounded __>: q.drop(n).length <= q.drop(n).capacity)  ) by Auto,
       10 (  q.drop(n).wellFormed                                                                         ) by Rewrite(RS(Queue.$$.wellFormed _), 9)
        //@formatter:on
      )
    }

    @pure def frameClear[T](q: Queue[T]): Unit = {
      Contract(
        Ensures(
          q.clear.capacity ≡ q.capacity,
          q.clear.strategy ≡ q.strategy,
          q.clear.error ≡ q.error
        )
      )
      Deduce(
        //@formatter:off
        1 (  q.clear.capacity ≡ q.capacity  ) by Simpl,
        2 (  q.clear.strategy ≡ q.strategy  ) by Simpl,
        3 (  q.clear.error ≡ q.error        ) by Simpl
        //@formatter:on
      )
    }

    @pure def frameClearAuto[T](q: Queue[T]): Unit = {
      Contract(
        Ensures(
          q.clear.capacity ≡ q.capacity,
          q.clear.strategy ≡ q.strategy,
          q.clear.error ≡ q.error
        )
      )
    }

    @pure def wfClear[T](q: Queue[T]): Unit = {
      Contract(
        Requires(q.wellFormed),
        Ensures(q.clear.wellFormed)
      )
      emptyZeroLength(q.buffer)
      frameClear(q)
      Deduce(
        //@formatter:off
        1 (  q.wellFormed                                                                                  ) by Premise,
        2 (  q.clear.capacity ≡ q.capacity                                                                 ) by Premise,
        3 (  q.clear.strategy ≡ q.strategy                                                                 ) by Premise,
        4 (  q.clear.error ≡ q.error                                                                       ) by Premise,
        5 (  q.clear.buffer.length ≡ 0                                                                     ) by Simpl,
        6 (  0 < q.capacity &
               (q.strategy != Queue.Strategy.Unbounded __>: q.buffer.length <= q.capacity)                    ) by Rewrite(RS(Queue.$$.wellFormed _), 1), // Auto,
        7 (  0 < q.capacity                                                                                ) by Simpl,
        8 (  0 < q.clear.capacity &
               (q.clear.strategy != Queue.Strategy.Unbounded __>: q.buffer.length <= q.clear.capacity)        ) by Auto,
        9 (  0 < q.clear.capacity &
               (q.clear.strategy != Queue.Strategy.Unbounded __>: q.clear.buffer.length <= q.clear.capacity)  ) by Simpl,
       10 (  q.clear.wellFormed                                                                            ) by RSimpl(RS(Queue.$$.wellFormed _))
        //@formatter:on
      )
    }

    @pure def wfClearAuto[T](q: Queue[T]): Unit = {
      Contract(
        Requires(q.wellFormed),
        Ensures(q.clear.wellFormed)
      )
    }

    @pure def frameSetBuffer[T](q: Queue[T], l: List[T]): Unit = {
      Contract(
        Ensures(
          q.setBuffer(l).capacity ≡ q.capacity,
          q.setBuffer(l).strategy ≡ q.strategy,
          q.setBuffer(l).error ≡ q.error
        )
      )
      Deduce(
        //@formatter:off
        1 (  q.setBuffer(l).capacity ≡ q.capacity  ) by Simpl,
        2 (  q.setBuffer(l).strategy ≡ q.strategy  ) by Simpl,
        3 (  q.setBuffer(l).error ≡ q.error        ) by Simpl
        //@formatter:on
      )
    }

    @pure def frameSetBufferAuto[T](q: Queue[T], l: List[T]): Unit = {
      Contract(
        Ensures(
          q.setBuffer(l).capacity ≡ q.capacity,
          q.setBuffer(l).strategy ≡ q.strategy,
          q.setBuffer(l).error ≡ q.error
        )
      )
    }

    @pure def wfSetBuffer[T](q: Queue[T], l: List[T]): Unit = {
      Contract(
        Requires(
          q.wellFormed,
          l.length <= q.capacity
        ),
        Ensures(q.setBuffer(l).wellFormed)
      )
      frameSetBuffer(q, l)
      Deduce(
        //@formatter:off
        1 (  q.wellFormed                                                                                                       ) by Premise,
        2 (  l.length <= q.capacity                                                                                             ) by Premise,
        3 (  q.setBuffer(l).capacity ≡ q.capacity                                                                               ) by Premise,
        4 (  q.setBuffer(l).strategy ≡ q.strategy                                                                               ) by Premise,
        5 (  q.setBuffer(l).error ≡ q.error                                                                                     ) by Premise,
        6 (  q.setBuffer(l).length ≡ l.length                                                                                   ) by Simpl,
        7 (  q.setBuffer(l).length <= q.capacity                                                                                ) by Subst_>(6, 2),
        8 (  q.setBuffer(l).length <= q.setBuffer(l).capacity                                                                   ) by Subst_>(3, 7),
        9 (  0 < q.capacity &
               (q.strategy != Queue.Strategy.Unbounded __>: q.buffer.length <= q.capacity)                                         ) by Rewrite(RS(Queue.$$.wellFormed _), 1), // Auto,
       10 (  0 < q.setBuffer(l).capacity &
               (q.setBuffer(l).strategy != Queue.Strategy.Unbounded __>: q.setBuffer(l).buffer.length <= q.setBuffer(l).capacity)  ) by Auto,
       11 (  q.setBuffer(l).wellFormed                                                                                          ) by Rewrite(RS(Queue.$$.wellFormed _), 10)
        //@formatter:on
      )
      
    }

    @pure def wfSetBufferAuto[T](q: Queue[T], l: List[T]): Unit = {
      Contract(
        Requires(
          q.wellFormed,
          l.length <= q.capacity
        ),
        Ensures(q.setBuffer(l).wellFormed)
      )
    }
  }


}