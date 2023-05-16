// #Sireum #Logika

import org.sireum._
import org.sireum.justification._

@strictpure def sum(s: ISZ[Z], i: Z): Z = if (s.isInBound(i)) {
  s(i) + sum(s, i + 1)
} else {
  0
}

def foo(seq: ISZ[Z], index: Z): Unit = {
  Deduce(

    1 #> (sum(seq, index) == (sum(seq, index): @l)) by Tauto,

    2 #>
      (sum(seq, index) == ({
        val s = seq
        val i = index
        if (s.isInBound(i)) {
          s(i) + sum(s, i + 1)
        } else {
          0
        }
      }: @l)) by Unfold(1),

    3 #> (sum(seq, index) == (sum(seq, index): @l)) by Fold(2)
  )
}