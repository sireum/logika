// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

@strictpure def sum(s: ISZ[Z], i: Z): Z = if (s.isInBound(i)) s(i) + sum(s, i + 1) else 0

def foo(seq: ISZ[Z], index: Z): Unit = {
  Deduce(

    1 #> (sum(seq, index) == (sum(seq, index): @l)) by Auto T,

    2 #>
      (sum(seq, index) == ({
        val s0 = seq
        val i0 = index
        if (s0.isInBound(i0)) s0(i0) + sum(s0, i0 + 1) else 0
      }: @l)) by Unfold(1),

    3 #>
      (sum(seq, index) == ({
        val i0 = index
        if (seq.isInBound(i0)) seq(i0) + sum(seq, i0 + 1) else 0
      }: @l)) by ValE(2),

    4 #>
      (sum(seq, index) == ({
        val s = seq
        val i0 = index
        if (s.isInBound(i0)) s(i0) + sum(s, i0 + 1) else 0
      }: @l)) by ValI(3)
  )
}