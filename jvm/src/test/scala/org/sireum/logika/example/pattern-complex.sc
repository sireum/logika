// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@datatype class Tuple[K,E](used: B, elem: E){}

@record class classExample [@imm K, @imm E](p: B, tuple1: Tuple[K,E], tuple2: Tuple[K,E]) {

  @pure def matchExampleWorkingA(): Z = {
    Contract(
      Ensures(
        ((!tuple1.used) -->: (Res[Z] == 0)),
        ((tuple1.used && tuple1.elem == tuple2.elem) -->: (Res[Z] == 1)),
        ((tuple1.used && tuple1.elem != tuple2.elem) -->: (Res[Z] == 2)),
        ((Res[Z] != 3))
      )
    )
    tuple1 match {
      case Tuple(F, _) =>
        return 0
      case Tuple(T, _) if (tuple1.elem == tuple2.elem) =>
        assert(tuple1.elem == tuple2.elem)
        return 1
      case Tuple(x, _) =>
        assert(x)
        assert(tuple1.elem != tuple2.elem)
        return 2
    }
    return 3
  }

  @pure def matchExampleWorkingB(): Z = { // Third Branch has "e"
    Contract(
      Ensures(
        ((!tuple1.used) -->: (Res[Z] == 0)),
        ((tuple1.used && tuple1.elem == tuple2.elem) -->: (Res[Z] == 1)),
        ((tuple1.used && tuple1.elem != tuple2.elem) -->: (Res[Z] == 2)),
        ((Res[Z] != 3))
      )
    )
    tuple1 match {
      case Tuple(F, _) =>
        return 0
      case Tuple(T, _) if (tuple1.elem == tuple2.elem) =>
        assert(tuple1.elem == tuple2.elem)
        return 1
      case Tuple(x, e) =>
        assert(x)
        assert(tuple1.elem != tuple2.elem)
        return 2
    }
    return 3
  }

  @pure def matchExampleFailsA(): Z = { // Second Branch has "e"
    Contract(
      Ensures(
        ((!tuple1.used) -->: (Res[Z] == 0)),
        ((tuple1.used && tuple1.elem == tuple2.elem) -->: (Res[Z] == 1)),
        ((tuple1.used && tuple1.elem != tuple2.elem) -->: (Res[Z] == 2)),
        ((Res[Z] != 3))
      )
    )
    tuple1 match {
      case Tuple(F, _) =>
        return 0
      case Tuple(T, e) if (tuple1.elem == tuple2.elem) =>
        assert(tuple1.elem == tuple2.elem)
        return 1
      case Tuple(x, _) =>
        assert(x)
        assert(tuple1.elem != tuple2.elem)
        return 2
    }
    return 3
  }

  @pure def matchExampleFailsB(): Z = {
    Contract(
      Ensures(
        ((!tuple1.used) -->: (Res[Z] == 0)),
        ((tuple1.used && tuple1.elem == tuple2.elem) -->: (Res[Z] == 1)),
        ((tuple1.used && tuple1.elem != tuple2.elem) -->: (Res[Z] == 2)),
        ((Res[Z] != 3))
      )
    )
    tuple1 match {
      case Tuple(F, _) =>
        return 0
      case Tuple(T, e) if (tuple1.elem == tuple2.elem) =>
        assert(tuple1.elem == tuple2.elem)
        return 1
      case Tuple(x, e) =>
        assert(x)
        assert(tuple1.elem != tuple2.elem)
        return 2
    }
    return 3
  }
}