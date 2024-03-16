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
              5 (  lookup(Cons(p, update(next, key, value)), key) ≡ value       ) by Rewrite(RS(lookupUpdateEq _), 4),
              6 (  lookup(update(next, key, value), key) ≡ value                ) by Rewrite(RS(lookup _), 5)
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

            if (p._1 ≡ key2) {
              Deduce(
                //@formatter:off
                1 (  key1 ≢ key2                                                    ) by Premise,
                2 (  map ≡ Cons(p, next)                                            ) by Auto,
                3 (  !(p._1 ≡ key1)                                                 ) by Premise,
                4 (  p._1 ≡ key2                                                    ) by Premise,
                5 (  update(map, key1, value) ≡ Cons(p, update(next, key1, value))  ) by RSimpl(RS(update _)),
                6 (  lookup(update(next, key1, value), key2) ≡ lookup(next, key2)   ) by RSimpl(RS(lookupUpdateNe _)),
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
                6 (  lookup(update(next, key1, value), key2) ≡ lookup(next, key2)   ) by RSimpl(RS(lookupUpdateNe _)),
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

    @pure def wfEmpty[T](c: Z, s: Strategy.Type): Unit = {
      Contract(
        Requires(0 < c),
        Ensures(empty[T](c, s).wellFormed)
      )
      Deduce(
        //@formatter:off
        1 (  0 < c                      ) by Premise,
        2 (  empty[T](c, s).wellFormed  ) by RSimpl(RS(Queue.$.wellFormed _)) // Auto
        //@formatter:on
      )
    }

    @pure def singleQueueHead[T](q: Queue[T], a: T): Unit = {
      Contract(
        Requires(q.buffer ≡ List.make(a)),
        Ensures(q.head ≡ a)
      )
      Deduce(
        //@formatter:off
        1 (  q.buffer ≡ List.make(a)  ) by Premise,
        2 (  q.head ≡ a               ) by Simpl // Auto
        //@formatter:on
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

    @pure def wfTail[T](q: Queue[T]): Unit = {
      Contract(
        Requires(q.wellFormed),
        Ensures(q.tail.wellFormed)
      )

      frameTail(q)

      Deduce(
        //@formatter:off
        1 (  q.wellFormed                                                                               ) by Premise,
        2 (  q.tail.error == q.error                                                                    ) by Premise,
        3 (  q.tail.capacity == q.capacity                                                              ) by Premise,
        4 (  q.tail.strategy == q.strategy                                                              ) by Premise,
        5 (  q.buffer.length >= q.tail.length                                                           ) by Auto,
        6 (  0 < q.capacity &
               (q.strategy != Queue.Strategy.Unbounded __>: q.buffer.length <= q.capacity)                 ) by Rewrite(RS(Queue.$.wellFormed _), 1), // Auto,
        7 (  0 < q.tail.capacity &
               (q.tail.strategy != Queue.Strategy.Unbounded __>: q.tail.buffer.length <= q.tail.capacity)  ) by Auto,
        8 (  q.tail.wellFormed                                                                          ) by Rewrite(RS(Queue.$.wellFormed _), 7) // Auto,
        //@formatter:on
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
        2 (  q.tail.buffer ≡ List.Nil[T]()  ) by Simpl // Auto
        //@formatter:on
      )
    }

    @pure def framePush[T](q: Queue[T], a: T): Unit = {
      Contract(
        Ensures(
          q.push(a).capacity ≡ q.capacity,
          q.push(a).strategy ≡ q.strategy
        )
      )

      q.strategy match {
        case Queue.Strategy.DropEarliest => {
          if (q.length < q.capacity) {
            Deduce(
              //@formatter:off
              1 (  q.length < q.capacity                           ) by Premise,
              2 (  q.strategy == List.Queue.Strategy.DropEarliest  ) by Auto,
              3 (  q.push(a).capacity ≡ q.capacity                 ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy                 ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  !(q.length < q.capacity)                        ) by Premise,
              2 (  q.strategy == List.Queue.Strategy.DropEarliest  ) by Auto,
              3 (  q.push(a).capacity ≡ q.capacity                 ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy                 ) by Simpl
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.DropLatest => {
          if (q.length < q.capacity) {
            Deduce(
              //@formatter:off
              1 (  q.length < q.capacity                         ) by Premise,
              2 (  q.strategy == List.Queue.Strategy.DropLatest  ) by Auto,
              3 (  q.push(a).capacity ≡ q.capacity               ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy               ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  !(q.length < q.capacity)                      ) by Premise,
              2 (  q.strategy == List.Queue.Strategy.DropLatest  ) by Auto,
              3 (  q.push(a).capacity ≡ q.capacity               ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy               ) by Simpl
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.Error => {
          if (q.length < q.capacity) {
            Deduce(
              //@formatter:off
              1 (  q.length < q.capacity                    ) by Premise,
              2 (  q.strategy == List.Queue.Strategy.Error  ) by Auto,
              3 (  q.push(a).capacity ≡ q.capacity          ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy          ) by Simpl
              //@formatter:on
            )
            return
          } else {
            Deduce(
              //@formatter:off
              1 (  !(q.length < q.capacity)                 ) by Premise,
              2 (  q.strategy == List.Queue.Strategy.Error  ) by Auto,
              3 (  q.push(a).capacity ≡ q.capacity          ) by Simpl,
              4 (  q.push(a).strategy ≡ q.strategy          ) by Simpl
              //@formatter:on
            )
            return
          }
        }
        case Queue.Strategy.Unbounded => {
          Deduce(
            //@formatter:off
            1 (  q.strategy == List.Queue.Strategy.Unbounded  ) by Auto,
            2 (  q.push(a).capacity ≡ q.capacity              ) by Simpl,
            3 (  q.push(a).strategy ≡ q.strategy              ) by Simpl
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

      q.strategy match {
        case Queue.Strategy.DropEarliest => {
          Deduce(
            //@formatter:off
            1 (  q.length < q.capacity                           ) by Premise,
            2 (  q.strategy == List.Queue.Strategy.DropEarliest  ) by Auto,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))   ) by Simpl
            //@formatter:on
          )
          return
        }
        case Queue.Strategy.DropLatest => {
          Deduce(
            //@formatter:off
            1 (  q.length < q.capacity                          ) by Premise,
            2 (  q.strategy == List.Queue.Strategy.DropLatest   ) by Auto,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl
            //@formatter:on
          )
          return
        }
        case Queue.Strategy.Error => {
          Deduce(
            //@formatter:off
            1 (  q.length < q.capacity                          ) by Premise,
            2 (  q.strategy == List.Queue.Strategy.Error        ) by Auto,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl
            //@formatter:on
          )
          return
        }
        case Queue.Strategy.Unbounded => {
          Deduce(
            //@formatter:off
            1 (  q.strategy == List.Queue.Strategy.Unbounded    ) by Auto,
            2 (  q.push(a).capacity ≡ q.capacity                ) by Simpl,
            3 (  q.push(a).buffer ≡ (q.buffer ++ List.make(a))  ) by Simpl
            //@formatter:on
          )
          return
        }
      }
    }
  }


}