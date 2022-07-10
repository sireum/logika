// #Sireum #Logika

import org.sireum._
import org.sireum.justification.ClaimOf

object AST {

  @datatype trait Exp

  object Exp {

    @datatype class LitB(val value: B) extends Exp

    @datatype class LitZ(val value: Z) extends Exp

    @datatype class VarRef(val id: String) extends Exp

    @datatype class Binary(val left: Exp, val op: Binary.Op.Type, val right: Exp) extends Exp

    object Binary {
      @enum object Op {
        "And"
        "Or"
        "Imply"
        "CondAnd"
        "CondOr"
        "CondImply"
        "Eq"
        "Ne"
        "Add"
        "Sub"
        "Mul"
        "Div"
        "Rem"
        "Lt"
        "Le"
        "Gt"
        "Ge"
      }
    }
  }
}

@datatype class State(val status: State.Status.Type,
                      val store: State.Store)

object State {
  type Store = AssocS[String, Value]

  @datatype trait Value

  object Value {
    @datatype class Integer(val value: Z) extends Value

    @datatype class Boolean(val value: B) extends Value

    @datatype class Error extends Value
  }

  @enum object Status {
    "Normal"
    "Halt"
    "TypeError"
    "ArithError"
    "StoreError"
  }

}

object Spec {

  object Aux {
    @spec def valueToB(value: State.Value): B = $

    @spec def valueToBFact(value: State.Value) = Fact(
      ?(value)((v: State.Value.Boolean) =>
        valueToB(value) == v.value
      )
    )

    @spec def valueToZ(value: State.Value): Z = $

    @spec def valueToZFact(value: State.Value) = Fact(
      ?(value)((v: State.Value.Integer) =>
        valueToZ(value) == v.value
      )
    )
  }

  @spec def evalExp(state: State, exp: AST.Exp): (State, State.Value) = $

  @spec def evalExpNonNormal(s0: State, exp: AST.Exp) = Fact(
    (s0.status =!= State.Status.Normal) ->: (Spec.evalExp(s0, exp) === ((s0, State.Value.Error())))
  )

  @spec def evalExpLitBFact(s0: State, exp: AST.Exp) = Fact(
    ?(exp) { (exp: AST.Exp.LitB) =>
      (s0.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((s0, State.Value.Boolean(exp.value))))
    }
  )

  @spec def evalExpLitZFact(s0: State, exp: AST.Exp) = Fact(
    ?(exp) { (exp: AST.Exp.LitZ) =>
      (s0.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((s0, State.Value.Integer(exp.value))))
    }
  )

  @spec def evalExpVarRefFact(s0: State, exp: AST.Exp, v: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.VarRef) =>
      (s0.status === State.Status.Normal) ->: (s0.store.get(exp.id) === Some(v)) ->:
        (Spec.evalExp(s0, exp) === ((s0, v)))
    }
  )

  @spec def evalExpVarRefStoreErrorFact(s0: State, exp: AST.Exp) = Fact(
    ?(exp) { (exp: AST.Exp.VarRef) =>
      (s0.status === State.Status.Normal) ->: (s0.store.get(exp.id) === None[State.Value]()) ->:
        (Spec.evalExp(s0, exp) === ((s0(status = State.Status.StoreError), State.Value.Error())))
    }
  )

  @spec def evalExpBinaryBooleanAndFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.And) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value & right.value))))
    },
  )

  @spec def evalExpBinaryBooleanOrFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Or) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value | right.value))))
    },
  )

  @spec def evalExpBinaryBooleanImplyFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Imply) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value ->: right.value))))
    },
  )

  @spec def evalExpBinaryBooleanEqFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Eq) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value === right.value))))
    },
  )

  @spec def evalExpBinaryBooleanNeFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Ne) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value =!= right.value))))
    },
  )

  @spec def evalExpBinaryCondAnd1BooleanFact(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(F)))) ->:
        (sN.status === State.Status.Normal) ->: (exp.op === AST.Exp.Binary.Op.CondAnd) ->:
        (Spec.evalExp(s0, exp) === ((sN, State.Value.Boolean(F))))
    },
  )

  @spec def evalExpBinaryCondOr1BooleanFact(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(T)))) ->:
        (sN.status === State.Status.Normal) ->: (exp.op === AST.Exp.Binary.Op.CondOr) ->:
        (Spec.evalExp(s0, exp) === ((sN, State.Value.Boolean(T))))
    },
  )

  @spec def evalExpBinaryCondImply1BooleanFact(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(F)))) ->:
        (sN.status === State.Status.Normal) ->: (exp.op === AST.Exp.Binary.Op.CondImply) ->:
        (Spec.evalExp(s0, exp) === ((sN, State.Value.Boolean(T))))
    },
  )

  @spec def evalExpBinaryCondAnd2BooleanFact(s0: State, exp: AST.Exp, sN: State, right: State.Value.Boolean, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(T)))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.CondAnd) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, right)))
    },
  )

  @spec def evalExpBinaryCondOr2BooleanFact(s0: State, exp: AST.Exp, sN: State, right: State.Value.Boolean, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(F)))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.CondOr) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, right)))
    },
  )

  @spec def evalExpBinaryCondImply2BooleanFact(s0: State, exp: AST.Exp, sN: State, right: State.Value.Boolean, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(T)))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.CondImply) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, right)))
    },
  )

  @spec def evalExpBinaryIntegerAddFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Add) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(left.value + right.value))))
    },
  )

  @spec def evalExpBinaryIntegerSubFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Sub) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(left.value - right.value))))
    },
  )

  @spec def evalExpBinaryIntegerMulFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Mul) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(left.value * right.value))))
    },
  )

  @spec def evalExpBinaryIntegerDivFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Div) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        ((right.value =!= 0) -->: (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(left.value / right.value)))))
    },
  )

  @spec def evalExpBinaryIntegerRemFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Rem) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        ((right.value > 0) -->: (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(left.value % right.value)))))
    },
  )

  @spec def evalExpBinaryIntegerEqFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Eq) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value === right.value))))
    },
  )

  @spec def evalExpBinaryIntegerNeFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Ne) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value =!= right.value))))
    },
  )

  @spec def evalExpBinaryIntegerLtFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Lt) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value < right.value))))
    },
  )

  @spec def evalExpBinaryIntegerLeFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Le) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value <= right.value))))
    },
  )

  @spec def evalExpBinaryIntegerGtFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Gt) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value > right.value))))
    },
  )

  @spec def evalExpBinaryIntegerGeFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (exp.op === AST.Exp.Binary.Op.Ge) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(left.value >= right.value))))
    },
  )

  @spec def evalExpBinaryNonNormal1Fact(s0: State, exp: AST.Exp, sN: State, v1: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, v1))) ->: (sN.status =!= State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sN, State.Value.Error())))
    },
  )

  @spec def evalExpBinaryNonNormal2Fact(s0: State, exp: AST.Exp, sN: State, v1: State.Value, sM: State, v2: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, v1))) ->: (sN.status === State.Status.Normal) ->:
        (Spec.evalExp(sN, exp.right) === ((sM, v2))) ->: (sM.status =!= State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
    },
  )

  @spec def evalExpBinaryBooleanOpTypeErrorFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->: !(
        exp.op === AST.Exp.Binary.Op.And | exp.op === AST.Exp.Binary.Op.Or | exp.op === AST.Exp.Binary.Op.Imply |
          exp.op === AST.Exp.Binary.Op.CondAnd | exp.op === AST.Exp.Binary.Op.CondOr | exp.op === AST.Exp.Binary.Op.CondImply |
          exp.op === AST.Exp.Binary.Op.Eq | exp.op === AST.Exp.Binary.Op.Ne
        ) ->:
        (Spec.evalExp(s0, exp) === ((sN(status = State.Status.TypeError), State.Value.Error())))
    },
  )

  @spec def evalExpBinaryIntegerOpTypeErrorFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->: !(
        exp.op === AST.Exp.Binary.Op.Add | exp.op === AST.Exp.Binary.Op.Sub | exp.op === AST.Exp.Binary.Op.Mul |
          exp.op === AST.Exp.Binary.Op.Div | exp.op === AST.Exp.Binary.Op.Rem | exp.op === AST.Exp.Binary.Op.Eq |
          exp.op === AST.Exp.Binary.Op.Ne | exp.op === AST.Exp.Binary.Op.Lt | exp.op === AST.Exp.Binary.Op.Le |
          exp.op === AST.Exp.Binary.Op.Gt | exp.op === AST.Exp.Binary.Op.Ge
        ) ->:
        (Spec.evalExp(s0, exp) === ((sN(status = State.Status.TypeError), State.Value.Error())))
    },
  )

  @spec def evalExpBinaryTypeError1Fact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM(status = State.Status.TypeError), State.Value.Error())))
    },
  )

  @spec def evalExpBinaryTypeError2Fact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
        (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
        (Spec.evalExp(s0, exp) === ((sM(status = State.Status.TypeError), State.Value.Error())))
    },
  )

  @spec def evalExpBinaryValueError1Fact(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Error()))) ->:
        (Spec.evalExp(s0, exp) === ((sN, State.Value.Error())))
    },
  )

  @spec def evalExpBinaryValueError2Fact(s0: State, exp: AST.Exp, sN: State, sM: State, v1: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, v1))) ->: (sN.status === State.Status.Normal) ->:
        (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Error()))) ->:
        (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
    },
  )

  @spec def evalExpBinaryIntegerDivArithErrorFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->:
        (exp.op === AST.Exp.Binary.Op.Div) ->: (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Integer(0)))) ->:
        (Spec.evalExp(s0, exp) === ((sM(status = State.Status.ArithError), State.Value.Error())))
    },
  )

  @spec def evalExpBinaryIntegerRemArithErrorFact(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->:
        (exp.op === AST.Exp.Binary.Op.Rem) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (right.value <= 0) ->:
        (Spec.evalExp(s0, exp) === ((sM(status = State.Status.ArithError), State.Value.Error())))
    },
  )
}

object Impl {

  def evalLitB(state: State, e: AST.Exp.LitB): (State, State.Value) = {
    Contract(
      Requires(state.status === State.Status.Normal),
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val rv: State.Value = State.Value.Boolean(e.value)
    Deduce(
      ∀ { (s0: State, exp: AST.Exp) =>
        ?(exp) { (exp: AST.Exp.LitB) =>
          (s0.status === State.Status.Normal) ->:
            (Spec.evalExp(s0, exp) === ((s0, State.Value.Boolean(exp.value))))
        }
      } by ClaimOf(Spec.evalExpLitBFact _),
    )
    return (state, rv)
  }

  def evalLitZ(state: State, e: AST.Exp.LitZ): (State, State.Value) = {
    Contract(
      Requires(state.status === State.Status.Normal),
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val rv: State.Value = State.Value.Integer(e.value)
    val exp: AST.Exp = e
    Deduce(
      ?(exp) { (exp: AST.Exp.LitZ) =>
        (state.status === State.Status.Normal) ->:
          (Spec.evalExp(state, exp) === ((state, State.Value.Integer(exp.value))))
      } by Spec.evalExpLitZFact(state, exp),
    )
    return (state, rv)
  }

  def evalVarRef(state: State, e: AST.Exp.VarRef): (State, State.Value) = {
    Contract(
      Requires(state.status === State.Status.Normal),
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val exp: AST.Exp = e
    state.store.get(e.id) match {
      case Some(rv) =>
        Deduce(
          ?(exp) { (exp: AST.Exp.VarRef) =>
            (state.status === State.Status.Normal) ->: (state.store.get(exp.id) === Some(rv)) ->:
              (Spec.evalExp(state, exp) === ((state, rv)))
          } by Spec.evalExpVarRefFact(state, exp, rv),
        )
        return (state, rv)
      case _ =>
        Deduce(
          ?(exp) { (exp: AST.Exp.VarRef) =>
            (state.status === State.Status.Normal) ->: (state.store.get(exp.id) === None[State.Value]()) ->:
              (Spec.evalExp(state, exp) === ((state(status = State.Status.StoreError), State.Value.Error())))
          } by Spec.evalExpVarRefStoreErrorFact(state, exp),
        )
        return (state(status = State.Status.StoreError), State.Value.Error())
    }
  }

  def evalBinaryExp(s0: State, e: AST.Exp.Binary): (State, State.Value) = {
    Contract(
      Requires(s0.status === State.Status.Normal),
      Ensures(Spec.evalExp(s0, e) == Res)
    )
    val exp: AST.Exp = e
    val (sN, left) = evalExp(s0, e.left)
    if (sN.status =!= State.Status.Normal) {
      Deduce(
        ?(exp) { (exp: AST.Exp.Binary) =>
          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status =!= State.Status.Normal) ->:
            (Spec.evalExp(s0, exp) === ((sN, State.Value.Error())))
        } by Spec.evalExpBinaryNonNormal1Fact(s0, exp, sN, left)
      )
      return (sN, State.Value.Error())
    } else {
      left match {
        case l: State.Value.Boolean =>
          if (e.op === AST.Exp.Binary.Op.CondAnd) {
            if (l.value) {
              val (sM, right) = evalExp(sN, e.right)
              if (sM.status =!= State.Status.Normal) {
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status =!= State.Status.Normal) ->:
                      (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                  } by Spec.evalExpBinaryNonNormal2Fact(s0, exp, sN, left, sM, right)
                )
                return (sM, State.Value.Error())
              } else {
                right match {
                  case right: State.Value.Boolean =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(T)))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.CondAnd) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, right)))
                      } by Spec.evalExpBinaryCondAnd2BooleanFact(s0, exp, sN, right, sM)
                    )
                    return (sM, right)
                  case r: State.Value.Integer =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM(status = State.Status.TypeError), State.Value.Error())))
                      } by Spec.evalExpBinaryTypeError1Fact(s0, exp, sN, l, sM, r)
                    )
                    return (sM(status = State.Status.TypeError), State.Value.Error())
                  case r: State.Value.Error =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Error()))) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                      } by Spec.evalExpBinaryValueError2Fact(s0, exp, sN, sM, left)
                    )
                    return (sM, r)
                }
              }
            } else {
              Deduce(
                ?(exp) { (exp: AST.Exp.Binary) =>
                  (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(F)))) ->:
                    (sN.status === State.Status.Normal) ->: (exp.op === AST.Exp.Binary.Op.CondAnd) ->:
                    (Spec.evalExp(s0, exp) === ((sN, State.Value.Boolean(F))))
                } by Spec.evalExpBinaryCondAnd1BooleanFact(s0, exp, sN)
              )
              return (sN, State.Value.Boolean(F))
            }
          } else if (e.op === AST.Exp.Binary.Op.CondOr) {
            if (!l.value) {
              val (sM, right) = evalExp(sN, e.right)
              if (sM.status =!= State.Status.Normal) {
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status =!= State.Status.Normal) ->:
                      (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                  } by Spec.evalExpBinaryNonNormal2Fact(s0, exp, sN, left, sM, right)
                )
                return (sM, State.Value.Error())
              } else {
                right match {
                  case right: State.Value.Boolean =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(F)))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.CondOr) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, right)))
                      } by Spec.evalExpBinaryCondOr2BooleanFact(s0, exp, sN, right, sM)
                    )
                    return (sM, right)
                  case r: State.Value.Integer =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM(status = State.Status.TypeError), State.Value.Error())))
                      } by Spec.evalExpBinaryTypeError1Fact(s0, exp, sN, l, sM, r)
                    )
                    return (sM(status = State.Status.TypeError), State.Value.Error())
                  case r: State.Value.Error =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Error()))) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                      } by Spec.evalExpBinaryValueError2Fact(s0, exp, sN, sM, left)
                    )
                    return (sM, r)
                }
              }
            } else {
              Deduce(
                ?(exp) { (exp: AST.Exp.Binary) =>
                  (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(T)))) ->:
                    (sN.status === State.Status.Normal) ->: (exp.op === AST.Exp.Binary.Op.CondOr) ->:
                    (Spec.evalExp(s0, exp) === ((sN, State.Value.Boolean(T))))
                } by Spec.evalExpBinaryCondOr1BooleanFact(s0, exp, sN)
              )
              return (sN, State.Value.Boolean(T))
            }
          } else if (e.op === AST.Exp.Binary.Op.CondImply) {
            if (l.value) {
              val (sM, right) = evalExp(sN, e.right)
              if (sM.status =!= State.Status.Normal) {
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status =!= State.Status.Normal) ->:
                      (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                  } by Spec.evalExpBinaryNonNormal2Fact(s0, exp, sN, left, sM, right)
                )
                return (sM, State.Value.Error())
              } else {
                right match {
                  case right: State.Value.Boolean =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(T)))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.CondImply) ->: (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, right)))
                      } by Spec.evalExpBinaryCondImply2BooleanFact(s0, exp, sN, right, sM)
                    )
                    return (sM, right)
                  case r: State.Value.Integer =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM(status = State.Status.TypeError), State.Value.Error())))
                      } by Spec.evalExpBinaryTypeError1Fact(s0, exp, sN, l, sM, r)
                    )
                    return (sM(status = State.Status.TypeError), State.Value.Error())
                  case r: State.Value.Error =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Error()))) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                      } by Spec.evalExpBinaryValueError2Fact(s0, exp, sN, sM, left)
                    )
                    return (sM, r)
                }
              }
            } else {
              Deduce(
                ?(exp) { (exp: AST.Exp.Binary) =>
                  (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Boolean(F)))) ->:
                    (sN.status === State.Status.Normal) ->: (exp.op === AST.Exp.Binary.Op.CondImply) ->:
                    (Spec.evalExp(s0, exp) === ((sN, State.Value.Boolean(T))))
                } by Spec.evalExpBinaryCondImply1BooleanFact(s0, exp, sN)
              )
              return (sN, State.Value.Boolean(T))
            }
          } else {
            val (sM, right) = evalExp(sN, e.right)
            if (sM.status =!= State.Status.Normal) {
              Deduce(
                ?(exp) { (exp: AST.Exp.Binary) =>
                  (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                    (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status =!= State.Status.Normal) ->:
                    (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                } by Spec.evalExpBinaryNonNormal2Fact(s0, exp, sN, left, sM, right)
              )
              return (sM, State.Value.Error())
            } else {
              right match {
                case r: State.Value.Boolean =>
                  e.op match {
                    case AST.Exp.Binary.Op.And =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                            (exp.op === AST.Exp.Binary.Op.And) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value & r.value))))
                        } by Spec.evalExpBinaryBooleanAndFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Boolean(l.value & r.value))
                    case AST.Exp.Binary.Op.Or =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                            (exp.op === AST.Exp.Binary.Op.Or) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value | r.value))))
                        } by Spec.evalExpBinaryBooleanOrFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Boolean(l.value | r.value))
                    case AST.Exp.Binary.Op.Imply =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                            (exp.op === AST.Exp.Binary.Op.Imply) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value ->: r.value))))
                        } by Spec.evalExpBinaryBooleanImplyFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Boolean(l.value ->: r.value))
                    case AST.Exp.Binary.Op.Eq =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                            (exp.op === AST.Exp.Binary.Op.Eq) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value === r.value))))
                        } by Spec.evalExpBinaryBooleanEqFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Boolean(l.value === r.value))
                    case AST.Exp.Binary.Op.Ne =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                            (exp.op === AST.Exp.Binary.Op.Ne) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value =!= r.value))))
                        } by Spec.evalExpBinaryBooleanNeFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Boolean(l.value =!= r.value))
                    case _ =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->: !(
                            exp.op === AST.Exp.Binary.Op.And | exp.op === AST.Exp.Binary.Op.Or | exp.op === AST.Exp.Binary.Op.Imply |
                              exp.op === AST.Exp.Binary.Op.CondAnd | exp.op === AST.Exp.Binary.Op.CondOr | exp.op === AST.Exp.Binary.Op.CondImply |
                              exp.op === AST.Exp.Binary.Op.Eq | exp.op === AST.Exp.Binary.Op.Ne
                            ) ->:
                            (Spec.evalExp(s0, exp) === ((sN(status = State.Status.TypeError), State.Value.Error())))
                        } by Spec.evalExpBinaryBooleanOpTypeErrorFact(s0, exp, sN, l),
                      )
                      return (sN(status = State.Status.TypeError), State.Value.Error())
                  }
                case r: State.Value.Integer =>
                  Deduce(
                    ?(exp) { (exp: AST.Exp.Binary) =>
                      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                        (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                        (Spec.evalExp(s0, exp) === ((sM(status = State.Status.TypeError), State.Value.Error())))
                    } by Spec.evalExpBinaryTypeError1Fact(s0, exp, sN, l, sM, r)
                  )
                  return (sM(status = State.Status.TypeError), State.Value.Error())
                case r: State.Value.Error =>
                  Deduce(
                    ?(exp) { (exp: AST.Exp.Binary) =>
                      (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                        (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Error()))) ->:
                        (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                    } by Spec.evalExpBinaryValueError2Fact(s0, exp, sN, sM, left)
                  )
                  return (sM, r)
              }
            }
          }
        case l: State.Value.Integer =>
          val (sM, right) = evalExp(sN, e.right)
          if (sM.status =!= State.Status.Normal) {
            Deduce(
              ?(exp) { (exp: AST.Exp.Binary) =>
                (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                  (Spec.evalExp(sN, exp.right) === ((sM, right))) ->: (sM.status =!= State.Status.Normal) ->:
                  (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
              } by Spec.evalExpBinaryNonNormal2Fact(s0, exp, sN, left, sM, right)
            )
            return (sM, State.Value.Error())
          } else {
            right match {
              case r: State.Value.Boolean =>
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                      (Spec.evalExp(s0, exp) === ((sM(status = State.Status.TypeError), State.Value.Error())))
                  } by Spec.evalExpBinaryTypeError2Fact(s0, exp, sN, l, sM, r)
                )
                return (sM(status = State.Status.TypeError), State.Value.Error())
              case r: State.Value.Integer =>
                e.op match {
                  case AST.Exp.Binary.Op.Add =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Add) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(l.value + r.value))))
                      } by Spec.evalExpBinaryIntegerAddFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Integer(l.value + r.value))
                  case AST.Exp.Binary.Op.Sub =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Sub) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(l.value - r.value))))
                      } by Spec.evalExpBinaryIntegerSubFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Integer(l.value - r.value))
                  case AST.Exp.Binary.Op.Mul =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Mul) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(l.value * r.value))))
                      } by Spec.evalExpBinaryIntegerMulFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Integer(l.value * r.value))
                  case AST.Exp.Binary.Op.Div =>
                    if (r.value === 0) {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->:
                            (exp.op === AST.Exp.Binary.Op.Div) ->: (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Integer(0)))) ->:
                            (Spec.evalExp(s0, exp) === ((sM(status = State.Status.ArithError), State.Value.Error())))
                        } by Spec.evalExpBinaryIntegerDivArithErrorFact(s0, exp, sN, l, sM)
                      )
                      return (sM(status = State.Status.ArithError), State.Value.Error())
                    } else {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                            (exp.op === AST.Exp.Binary.Op.Div) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                            ((r.value =!= 0) -->: (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(l.value / r.value)))))
                        } by Spec.evalExpBinaryIntegerDivFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Integer(l.value / r.value))
                    }
                  case AST.Exp.Binary.Op.Rem =>
                    if (r.value <= 0) {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->:
                            (exp.op === AST.Exp.Binary.Op.Rem) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (r.value <= 0) ->:
                            (Spec.evalExp(s0, exp) === ((sM(status = State.Status.ArithError), State.Value.Error())))
                        } by Spec.evalExpBinaryIntegerRemArithErrorFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM(status = State.Status.ArithError), State.Value.Error())
                    } else {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                            (exp.op === AST.Exp.Binary.Op.Rem) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                            ((r.value > 0) -->: (Spec.evalExp(s0, exp) === ((sM, State.Value.Integer(l.value % r.value)))))
                        } by Spec.evalExpBinaryIntegerRemFact(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Integer(l.value % r.value))
                    }
                  case AST.Exp.Binary.Op.Eq =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Eq) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value === r.value))))
                      } by Spec.evalExpBinaryIntegerEqFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value === r.value))
                  case AST.Exp.Binary.Op.Ne =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Ne) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value =!= r.value))))
                      } by Spec.evalExpBinaryIntegerNeFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value =!= r.value))
                  case AST.Exp.Binary.Op.Lt =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Lt) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value < r.value))))
                      } by Spec.evalExpBinaryIntegerLtFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value < r.value))
                  case AST.Exp.Binary.Op.Le =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Le) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value <= r.value))))
                      } by Spec.evalExpBinaryIntegerLeFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value <= r.value))
                  case AST.Exp.Binary.Op.Gt =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Gt) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value > r.value))))
                      } by Spec.evalExpBinaryIntegerGtFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value > r.value))
                  case AST.Exp.Binary.Op.Ge =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->:
                          (exp.op === AST.Exp.Binary.Op.Ge) ->: (Spec.evalExp(sN, exp.right) === ((sM, r))) ->: (sM.status === State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) === ((sM, State.Value.Boolean(l.value >= r.value))))
                      } by Spec.evalExpBinaryIntegerGeFact(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value >= r.value))
                  case _ =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, l))) ->: (sN.status === State.Status.Normal) ->: !(
                          exp.op === AST.Exp.Binary.Op.Add | exp.op === AST.Exp.Binary.Op.Sub | exp.op === AST.Exp.Binary.Op.Mul |
                            exp.op === AST.Exp.Binary.Op.Div | exp.op === AST.Exp.Binary.Op.Rem | exp.op === AST.Exp.Binary.Op.Eq |
                            exp.op === AST.Exp.Binary.Op.Ne | exp.op === AST.Exp.Binary.Op.Lt | exp.op === AST.Exp.Binary.Op.Le |
                            exp.op === AST.Exp.Binary.Op.Gt | exp.op === AST.Exp.Binary.Op.Ge
                          ) ->:
                          (Spec.evalExp(s0, exp) === ((sN(status = State.Status.TypeError), State.Value.Error())))
                      } by Spec.evalExpBinaryIntegerOpTypeErrorFact(s0, exp, sN, l)
                    )
                    return (sN(status = State.Status.TypeError), State.Value.Error())
                }
              case r: State.Value.Error =>
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, left))) ->: (sN.status === State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) === ((sM, State.Value.Error()))) ->:
                      (Spec.evalExp(s0, exp) === ((sM, State.Value.Error())))
                  } by Spec.evalExpBinaryValueError2Fact(s0, exp, sN, sM, left)
                )
                return (sM, r)
            }
          }
        case _: State.Value.Error =>
          Deduce(
            ?(exp) { (exp: AST.Exp.Binary) =>
              (s0.status === State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) === ((sN, State.Value.Error()))) ->:
                (Spec.evalExp(s0, exp) === ((sN, State.Value.Error())))
            } by Spec.evalExpBinaryValueError1Fact(s0, exp, sN)
          )
          return (sN, left)
      }
    }
  }

  def evalExp(state: State, exp: AST.Exp): (State, State.Value) = {
    Contract(
      Ensures(Spec.evalExp(state, exp) === Res)
    )
    if (state.status =!= State.Status.Normal) {
      Deduce(
        (state.status =!= State.Status.Normal) ->: (Spec.evalExp(state, exp) === ((state, State.Value.Error())))
          by Spec.evalExpNonNormal(state, exp),
      )
      return (state, State.Value.Error())
    } else {
      exp match {
        case exp: AST.Exp.LitB => return evalLitB(state, exp)
        case exp: AST.Exp.LitZ => return evalLitZ(state, exp)
        case exp: AST.Exp.VarRef => return evalVarRef(state, exp)
        case exp: AST.Exp.Binary => return evalBinaryExp(state, exp)
      }
    }
  }

}
