// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

@strictpure def sum(s: ISZ[Z], i: Z): Z = if (s.isInBound(i)) {
  s(i) + sum(s, i + 1)
} else {
  0
}

def sumFoldUnfold(seq: ISZ[Z], index: Z): Unit = {
  Deduce(

    1 #> (sum(seq, index) == (sum(seq, index): @l)) by Auto T,

    2 #>
      (sum(seq, index) == ({
        val s0 = seq
        val i0 = index
        if (s0.isInBound(i0)) {
          s0(i0) + sum(s0, i0 + 1)
        } else {
          0
        }
      }: @l)) by Unfold(1),

    3 #> (sum(seq, index) == (sum(seq, index): @l)) by Fold(2)
  )
}

@strictpure def exists[E](s: ISZ[E], i: Z, e: E): B =
  if (s.isInBound(i)) if (s(i) == e) T else exists(s, i + 1, e)
  else F

def existsFoldUnfold[V](seq: ISZ[V], index: Z, element: V): Unit = {
  Deduce(

    1 #> (exists(seq, index, element) == (exists(seq, index, element): @l)) by Auto T,

    2 #>
      (exists(seq, index, element) == ({
        val s0 = seq
        val i0 = index
        val e0 = element
        if (s0.isInBound(i0)) if (s0(i0) == e0) T else exists(s0, i0 + 1, e0)
        else F
      }: @l)) by Unfold(1),

    3 #> (exists(seq, index, element) == (exists(seq, index, element): @l)) by Fold(2)
  )
}

def existsFoldUnfoldZ(seq: ISZ[Z], index: Z, element: Z): Unit = {
  Deduce(

    1 #> (exists(seq, index, element) == (exists(seq, index, element): @l)) by Auto T,

    2 #>
      (exists(seq, index, element) == ({
        val s0 = seq
        val i0 = index
        val e0 = element
        if (s0.isInBound(i0)) if (s0(i0) == e0) T else exists(s0, i0 + 1, e0)
        else F
      }: @l)) by Unfold(1),

    3 #> (exists(seq, index, element) == (exists(seq, index, element): @l)) by Fold(2)
  )
}

@datatype class SeqOps[E](val s: ISZ[E]) {

  @strictpure def exists(i: Z, e: E): B =
    if (s.isInBound(i)) if (s(i) == e) T else exists(i + 1, e)
    else F

}

def seqOpsExistsFoldUnfold[V](seqOps: SeqOps[V], index: Z, element: V): Unit = {
  Deduce(

    1 #> (seqOps.exists(index, element) == (seqOps.exists(index, element): @l)) by Auto T,

    2 #>
      (seqOps.exists(index, element) == ({
        val seqOps0 = seqOps
        val i0 = index
        val e0 = element
        if (seqOps0.s.isInBound(i0)) if (seqOps0.s(i0) == e0) T else seqOps0.exists(i0 + 1, e0)
        else F
      }: @l)) by Unfold(1),

    3 #> (seqOps.exists(index, element) == (seqOps.exists(index, element): @l)) by Fold(2)
  )
}
