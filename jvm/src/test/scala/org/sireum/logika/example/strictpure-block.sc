// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

def foo(x: Z): Z = {
  Contract(
    Ensures(
      Res == {
        val t = x * x
        2 * t
      }
    )
  )
  return 2 * x * x
}

def absOpt(zOpt: Option[Z]): Option[Z] = {
  Contract(
    Ensures({
      Res[Option[Z]] match {
        case Some(res) => res >= 0
        case _ => T
      }
    })
  )
  val r: Option[Z] = zOpt match {
    case Some(z) if z < 0 => Some(-z)
    case Some(z) => Some(z)
    case _ => None()
  }
  return r
}

@strictpure def sum(s: ISZ[Z], i: Z): Z = if (s.isInBound(i)) {
  s(i) + sum(s, i + 1)
} else {
  0
}

def unfoldTauto(): Unit = {

  Deduce(

    (sum(ISZ(1, 2, 3), 2) == {
      val s = ISZ[Z](1, 2, 3)
      val i = 2
      if (s.isInBound(i)) {
        s(i) + sum(s, i + 1)
      } else {
        0
      }
    }) by Auto T,

    (sum(ISZ(1, 2, 3), 2) == {
      val s = ISZ[Z](1, 2, 3)
      val i = 2
      if (s.isInBound(i)) {
        s(i) + {
          val s1 = s
          val i1 = i + 1
          if (s1.isInBound(i1)) {
            s(i1) + sum(s1, i1 + 1)
          } else {
            0
          }
        }
      } else {
        0
      }
    }) by Auto T,

    (sum(ISZ(1, 2, 3), 2) == {
      val s = ISZ[Z](1, 2, 3)
      s(2) + {
        val s1 = s
        if (s1.isInBound(3)) {
          s(3) + sum(s1, 3)
        } else {
          0
        }
      }
    }) by Auto T,

    (sum(ISZ(1, 2, 3), 2) == {
      val s = ISZ[Z](1, 2, 3)
      3 + {
        val s1 = s
        if (s1.isInBound(3)) {
          s(3) + sum(s1, 3)
        } else {
          0
        }
      }
    }) by Auto T,

    (sum(ISZ(1, 2, 3), 2) == {
      val s = ISZ[Z](1, 2, 3)
      3 + {
        val s1 = s
        0
      }
    }) by Auto T,

    (sum(ISZ(1, 2, 3), 2) == 3) by Auto T
  )

  Deduce(
    ⊢(sum(ISZ(1, 2, 3), 0) == 6),
    ⊢(sum(ISZ(1, 2, 3), 1) == 5),
    ⊢(sum(ISZ(1, 2, 3), 2) == 3)
  )

}

def unfoldTautoSameDiff(s: ISZ[Z], i: Z): Unit = {
  Deduce(

    1 #> (sum(s, i) == {
      val s0 = s
      val i0 = i
      if (s0.isInBound(i0)) {
        s0(i0) + (sum(s0, i0 + 1): @l)
      } else {
        0
      }
    }) by Auto T,

    2 #> (sum(s, i) == {
      val s0 = s
      val i0 = i
      if (s0.isInBound(i0)) {
        s0(i0) + ({
          val i1 = i0 + 1
          if (s.isInBound(i1)) {
            s(i1) + sum(s, i + 2)
          } else {
            0
          }
        }: @l)
      } else {
        0
      }
    }) by SameDiff(1),

    3 #> (sum(s, i + 1) == {
      val s1 = s
      val i1 = i + 1
      if (s1.isInBound(i1)) {
        s1(i1) + sum(s1, i1 + 1)
      } else {
        0
      }
    }) by Auto T

  )
}