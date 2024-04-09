// #Sireum #Logika
//@Logika: --background save --timeout 4 --sat --par --par-branch --solver-valid cvc4,--full-saturate-quant;z3;cvc5,--full-saturate-quant --solver-sat z3

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

  @spec def evalExp(state: State, exp: AST.Exp): (State, State.Value) = $

  @spec def evalExpLitB(s0: State, exp: AST.Exp) = Fact(
    ?(exp) { (exp: AST.Exp.LitB) =>
      (s0.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((s0, State.Value.Boolean(exp.value))))
    }
  )

  @spec def evalExpLitZ(s0: State, exp: AST.Exp) = Fact(
    ?(exp) { (exp: AST.Exp.LitZ) =>
      (s0.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((s0, State.Value.Integer(exp.value))))
    }
  )

  @spec def evalExpVarRef(s0: State, exp: AST.Exp, v: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.VarRef) =>
      (s0.status == State.Status.Normal) ->: (s0.store.get(exp.id) == Some(v)) ->:
        (evalExp(s0, exp) == ((s0, v)))
    }
  )

  @spec def evalExpBinaryBooleanAnd(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.And) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value & right.value))))
    }
  )

  @spec def evalExpBinaryBooleanOr(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Or) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value | right.value))))
    }
  )

  @spec def evalExpBinaryBooleanImply(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Imply) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value ->: right.value))))
    }
  )

  @spec def evalExpBinaryBooleanEq(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Eq) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value == right.value))))
    }
  )

  @spec def evalExpBinaryBooleanNe(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Ne) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value != right.value))))
    }
  )

  @spec def evalExpBinaryBooleanCondAnd1(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, State.Value.Boolean(F)))) ->:
        (sN.status == State.Status.Normal) ->: (exp.op == AST.Exp.Binary.Op.CondAnd) ->:
        (evalExp(s0, exp) == ((sN, State.Value.Boolean(F))))
    }
  )

  @spec def evalExpBinaryBooleanCondOr1(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, State.Value.Boolean(T)))) ->:
        (sN.status == State.Status.Normal) ->: (exp.op == AST.Exp.Binary.Op.CondOr) ->:
        (evalExp(s0, exp) == ((sN, State.Value.Boolean(T))))
    }
  )

  @spec def evalExpBinaryBooleanCondImply1(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, State.Value.Boolean(F)))) ->:
        (sN.status == State.Status.Normal) ->: (exp.op == AST.Exp.Binary.Op.CondImply) ->:
        (evalExp(s0, exp) == ((sN, State.Value.Boolean(T))))
    }
  )

  @spec def evalExpBinaryBooleanCondAnd2(s0: State, exp: AST.Exp, sN: State, right: State.Value.Boolean, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, State.Value.Boolean(T)))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.CondAnd) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, right)))
    }
  )

  @spec def evalExpBinaryBooleanCondOr2(s0: State, exp: AST.Exp, sN: State, right: State.Value.Boolean, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, State.Value.Boolean(F)))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.CondOr) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, right)))
    }
  )

  @spec def evalExpBinaryBooleanCondImply2(s0: State, exp: AST.Exp, sN: State, right: State.Value.Boolean, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, State.Value.Boolean(T)))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.CondImply) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, right)))
    }
  )

  @spec def evalExpBinaryIntegerAdd(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Add) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Integer(left.value + right.value))))
    }
  )

  @spec def evalExpBinaryIntegerSub(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Sub) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Integer(left.value - right.value))))
    }
  )

  @spec def evalExpBinaryIntegerMul(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Mul) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Integer(left.value * right.value))))
    }
  )

  @spec def evalExpBinaryIntegerDiv(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Div) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        ((right.value != 0) -->: (evalExp(s0, exp) == ((sM, State.Value.Integer(left.value / right.value)))))
    }
  )

  @spec def evalExpBinaryIntegerRem(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Rem) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        ((right.value > 0) -->: (evalExp(s0, exp) == ((sM, State.Value.Integer(left.value % right.value)))))
    }
  )

  @spec def evalExpBinaryIntegerEq(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Eq) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value == right.value))))
    }
  )

  @spec def evalExpBinaryIntegerNe(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Ne) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value != right.value))))
    }
  )

  @spec def evalExpBinaryIntegerLt(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Lt) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value < right.value))))
    }
  )

  @spec def evalExpBinaryIntegerLe(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Le) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value <= right.value))))
    }
  )

  @spec def evalExpBinaryIntegerGt(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Gt) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value > right.value))))
    }
  )

  @spec def evalExpBinaryIntegerGe(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (exp.op == AST.Exp.Binary.Op.Ge) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Boolean(left.value >= right.value))))
    }
  )

  @spec def evalExpNonNormal(s0: State, exp: AST.Exp) = Fact(
    (s0.status != State.Status.Normal) ->:
      (evalExp(s0, exp) == ((s0, State.Value.Error())))
  )

  @spec def evalExpVarRefStoreError(s0: State, exp: AST.Exp) = Fact(
    ?(exp) { (exp: AST.Exp.VarRef) =>
      (s0.status == State.Status.Normal) ->: (s0.store.get(exp.id) == None[State.Value]()) ->:
        (evalExp(s0, exp) == ((s0(status = State.Status.StoreError), State.Value.Error())))
    }
  )

  @spec def evalExpBinaryNonNormal1(s0: State, exp: AST.Exp, sN: State, v1: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, v1))) ->: (sN.status != State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sN, State.Value.Error())))
    }
  )

  @spec def evalExpBinaryNonNormal2(s0: State, exp: AST.Exp, sN: State, v1: State.Value, sM: State, v2: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, v1))) ->: (sN.status == State.Status.Normal) ->:
        (evalExp(sN, exp.right) == ((sM, v2))) ->: (sM.status != State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Error())))
    }
  )

  @spec def evalExpBinaryBooleanTypeError(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->: !(
        exp.op == AST.Exp.Binary.Op.And | exp.op == AST.Exp.Binary.Op.Or | exp.op == AST.Exp.Binary.Op.Imply |
          exp.op == AST.Exp.Binary.Op.CondAnd | exp.op == AST.Exp.Binary.Op.CondOr | exp.op == AST.Exp.Binary.Op.CondImply |
          exp.op == AST.Exp.Binary.Op.Eq | exp.op == AST.Exp.Binary.Op.Ne
        ) ->:
        (evalExp(s0, exp) == ((sN(status = State.Status.TypeError), State.Value.Error())))
    }
  )

  @spec def evalExpBinaryIntegerTypeError(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->: !(
        exp.op == AST.Exp.Binary.Op.Add | exp.op == AST.Exp.Binary.Op.Sub | exp.op == AST.Exp.Binary.Op.Mul |
          exp.op == AST.Exp.Binary.Op.Div | exp.op == AST.Exp.Binary.Op.Rem | exp.op == AST.Exp.Binary.Op.Eq |
          exp.op == AST.Exp.Binary.Op.Ne | exp.op == AST.Exp.Binary.Op.Lt | exp.op == AST.Exp.Binary.Op.Le |
          exp.op == AST.Exp.Binary.Op.Gt | exp.op == AST.Exp.Binary.Op.Ge
        ) ->:
        (evalExp(s0, exp) == ((sN(status = State.Status.TypeError), State.Value.Error())))
    }
  )

  @spec def evalExpBinaryTypeError1(s0: State, exp: AST.Exp, sN: State, left: State.Value.Boolean, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM(status = State.Status.TypeError), State.Value.Error())))
    }
  )

  @spec def evalExpBinaryTypeError2(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Boolean) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
        (evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
        (evalExp(s0, exp) == ((sM(status = State.Status.TypeError), State.Value.Error())))
    }
  )

  @spec def evalExpBinaryValueError1(s0: State, exp: AST.Exp, sN: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, State.Value.Error()))) ->:
        (evalExp(s0, exp) == ((sN, State.Value.Error())))
    }
  )

  @spec def evalExpBinaryValueError2(s0: State, exp: AST.Exp, sN: State, sM: State, v1: State.Value) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, v1))) ->: (sN.status == State.Status.Normal) ->:
        (evalExp(sN, exp.right) == ((sM, State.Value.Error()))) ->:
        (evalExp(s0, exp) == ((sM, State.Value.Error())))
    }
  )

  @spec def evalExpBinaryIntegerDivArithError(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->:
        (exp.op == AST.Exp.Binary.Op.Div) ->: (evalExp(sN, exp.right) == ((sM, State.Value.Integer(0)))) ->:
        (evalExp(s0, exp) == ((sM(status = State.Status.ArithError), State.Value.Error())))
    }
  )

  @spec def evalExpBinaryIntegerRemArithError(s0: State, exp: AST.Exp, sN: State, left: State.Value.Integer, sM: State, right: State.Value.Integer) = Fact(
    ?(exp) { (exp: AST.Exp.Binary) =>
      (s0.status == State.Status.Normal) ->: (evalExp(s0, exp.left) == ((sN, left))) ->:
        (exp.op == AST.Exp.Binary.Op.Rem) ->: (evalExp(sN, exp.right) == ((sM, right))) ->: (right.value <= 0) ->:
        (evalExp(s0, exp) == ((sM(status = State.Status.ArithError), State.Value.Error())))
    }
  )
}

object Exec {

  @pure def evalLitB(state: State, e: AST.Exp.LitB): (State, State.Value) = {
    Contract(
      Requires(state.status == State.Status.Normal),
      Ensures(Spec.evalExp(state, e) == Res)
    )
    Deduce(
      ∀ { (s0: State, exp: AST.Exp) =>
        ?(exp) { (exp: AST.Exp.LitB) =>
          (s0.status == State.Status.Normal) ->:
            (Spec.evalExp(s0, exp) == ((s0, State.Value.Boolean(exp.value))))
        }
      } by ClaimOf(Spec.evalExpLitB _)
    )
    return (state, State.Value.Boolean(e.value))
  }

  @pure def evalLitZ(state: State, e: AST.Exp.LitZ): (State, State.Value) = {
    Contract(
      Requires(state.status == State.Status.Normal),
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val exp: AST.Exp = e
    Deduce(
      ?(exp) { (exp: AST.Exp.LitZ) =>
        (state.status == State.Status.Normal) ->:
          (Spec.evalExp(state, exp) == ((state, State.Value.Integer(exp.value))))
      } by Spec.evalExpLitZ(state, exp)
    )
    return (state, State.Value.Integer(e.value))
  }

  @pure def evalVarRef(state: State, e: AST.Exp.VarRef): (State, State.Value) = {
    Contract(
      Requires(state.status == State.Status.Normal),
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val exp: AST.Exp = e
    state.store.get(e.id) match {
      case Some(rv) =>
        Deduce(
          ?(exp) { (exp: AST.Exp.VarRef) =>
            (state.status == State.Status.Normal) ->: (state.store.get(exp.id) == Some(rv)) ->:
              (Spec.evalExp(state, exp) == ((state, rv)))
          } by Spec.evalExpVarRef(state, exp, rv)
        )
        return (state, rv)
      case _ =>
        Deduce(
          ?(exp) { (exp: AST.Exp.VarRef) =>
            (state.status == State.Status.Normal) ->: (state.store.get(exp.id) == None[State.Value]()) ->:
              (Spec.evalExp(state, exp) == ((state(status = State.Status.StoreError), State.Value.Error())))
          } by Spec.evalExpVarRefStoreError(state, exp)
        )
        return (state(status = State.Status.StoreError), State.Value.Error())
    }
  }

  @pure def evalBinaryExp(s0: State, e: AST.Exp.Binary): (State, State.Value) = {
    Contract(
      Requires(s0.status == State.Status.Normal),
      Ensures(Spec.evalExp(s0, e) == Res)
    )
    val exp: AST.Exp = e
    val (sN, left) = evalExp(s0, e.left)
    if (sN.status != State.Status.Normal) {
      Deduce(
        ?(exp) { (exp: AST.Exp.Binary) =>
          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status != State.Status.Normal) ->:
            (Spec.evalExp(s0, exp) == ((sN, State.Value.Error())))
        } by Spec.evalExpBinaryNonNormal1(s0, exp, sN, left)
      )
      return (sN, State.Value.Error())
    } else {
      left match {
        case l: State.Value.Boolean =>
          e.op match {
            case AST.Exp.Binary.Op.CondAnd =>
              if (l.value) {
                val (sM, right) = evalExp(sN, e.right)
                if (sM.status != State.Status.Normal) {
                  Deduce(
                    ?(exp) { (exp: AST.Exp.Binary) =>
                      (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                        (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status != State.Status.Normal) ->:
                        (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                    } by Spec.evalExpBinaryNonNormal2(s0, exp, sN, left, sM, right)
                  )
                  return (sM, State.Value.Error())
                } else {
                  right match {
                    case right: State.Value.Boolean =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, State.Value.Boolean(T)))) ->: (sN.status == State.Status.Normal) ->:
                            (exp.op == AST.Exp.Binary.Op.CondAnd) ->: (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) == ((sM, right)))
                        } by Spec.evalExpBinaryBooleanCondAnd2(s0, exp, sN, right, sM)
                      )
                      return (sM, right)
                    case r: State.Value.Integer =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                            (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) == ((sM(status = State.Status.TypeError), State.Value.Error())))
                        } by Spec.evalExpBinaryTypeError1(s0, exp, sN, l, sM, r)
                      )
                      return (sM(status = State.Status.TypeError), State.Value.Error())
                    case r: State.Value.Error =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                            (Spec.evalExp(sN, exp.right) == ((sM, State.Value.Error()))) ->:
                            (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                        } by Spec.evalExpBinaryValueError2(s0, exp, sN, sM, left)
                      )
                      return (sM, r)
                  }
                }
              } else {
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, State.Value.Boolean(F)))) ->:
                      (sN.status == State.Status.Normal) ->: (exp.op == AST.Exp.Binary.Op.CondAnd) ->:
                      (Spec.evalExp(s0, exp) == ((sN, State.Value.Boolean(F))))
                  } by Spec.evalExpBinaryBooleanCondAnd1(s0, exp, sN)
                )
                return (sN, State.Value.Boolean(F))
              }
            case AST.Exp.Binary.Op.CondOr =>
              if (!l.value) {
                val (sM, right) = evalExp(sN, e.right)
                if (sM.status != State.Status.Normal) {
                  Deduce(
                    ?(exp) { (exp: AST.Exp.Binary) =>
                      (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                        (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status != State.Status.Normal) ->:
                        (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                    } by Spec.evalExpBinaryNonNormal2(s0, exp, sN, left, sM, right)
                  )
                  return (sM, State.Value.Error())
                } else {
                  right match {
                    case right: State.Value.Boolean =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, State.Value.Boolean(F)))) ->: (sN.status == State.Status.Normal) ->:
                            (exp.op == AST.Exp.Binary.Op.CondOr) ->: (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) == ((sM, right)))
                        } by Spec.evalExpBinaryBooleanCondOr2(s0, exp, sN, right, sM)
                      )
                      return (sM, right)
                    case r: State.Value.Integer =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                            (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) == ((sM(status = State.Status.TypeError), State.Value.Error())))
                        } by Spec.evalExpBinaryTypeError1(s0, exp, sN, l, sM, r)
                      )
                      return (sM(status = State.Status.TypeError), State.Value.Error())
                    case r: State.Value.Error =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                            (Spec.evalExp(sN, exp.right) == ((sM, State.Value.Error()))) ->:
                            (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                        } by Spec.evalExpBinaryValueError2(s0, exp, sN, sM, left)
                      )
                      return (sM, r)
                  }
                }
              } else {
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, State.Value.Boolean(T)))) ->:
                      (sN.status == State.Status.Normal) ->: (exp.op == AST.Exp.Binary.Op.CondOr) ->:
                      (Spec.evalExp(s0, exp) == ((sN, State.Value.Boolean(T))))
                  } by Spec.evalExpBinaryBooleanCondOr1(s0, exp, sN)
                )
                return (sN, State.Value.Boolean(T))
              }
            case AST.Exp.Binary.Op.CondImply =>
              if (l.value) {
                val (sM, right) = evalExp(sN, e.right)
                if (sM.status != State.Status.Normal) {
                  Deduce(
                    ?(exp) { (exp: AST.Exp.Binary) =>
                      (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                        (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status != State.Status.Normal) ->:
                        (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                    } by Spec.evalExpBinaryNonNormal2(s0, exp, sN, left, sM, right)
                  )
                  return (sM, State.Value.Error())
                } else {
                  right match {
                    case right: State.Value.Boolean =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, State.Value.Boolean(T)))) ->: (sN.status == State.Status.Normal) ->:
                            (exp.op == AST.Exp.Binary.Op.CondImply) ->: (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status == State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) == ((sM, right)))
                        } by Spec.evalExpBinaryBooleanCondImply2(s0, exp, sN, right, sM)
                      )
                      return (sM, right)
                    case r: State.Value.Integer =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                            (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                            (Spec.evalExp(s0, exp) == ((sM(status = State.Status.TypeError), State.Value.Error())))
                        } by Spec.evalExpBinaryTypeError1(s0, exp, sN, l, sM, r)
                      )
                      return (sM(status = State.Status.TypeError), State.Value.Error())
                    case r: State.Value.Error =>
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                            (Spec.evalExp(sN, exp.right) == ((sM, State.Value.Error()))) ->:
                            (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                        } by Spec.evalExpBinaryValueError2(s0, exp, sN, sM, left)
                      )
                      return (sM, r)
                  }
                }
              } else {
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, State.Value.Boolean(F)))) ->:
                      (sN.status == State.Status.Normal) ->: (exp.op == AST.Exp.Binary.Op.CondImply) ->:
                      (Spec.evalExp(s0, exp) == ((sN, State.Value.Boolean(T))))
                  } by Spec.evalExpBinaryBooleanCondImply1(s0, exp, sN)
                )
                return (sN, State.Value.Boolean(T))
              }
            case _ =>
              val (sM, right) = evalExp(sN, e.right)
              if (sM.status != State.Status.Normal) {
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status != State.Status.Normal) ->:
                      (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                  } by Spec.evalExpBinaryNonNormal2(s0, exp, sN, left, sM, right)
                )
                return (sM, State.Value.Error())
              } else {
                right match {
                  case r: State.Value.Boolean =>
                    e.op match {
                      case AST.Exp.Binary.Op.And =>
                        Deduce(
                          ?(exp) { (exp: AST.Exp.Binary) =>
                            (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                              (exp.op == AST.Exp.Binary.Op.And) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                              (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value & r.value))))
                          } by Spec.evalExpBinaryBooleanAnd(s0, exp, sN, l, sM, r)
                        )
                        return (sM, State.Value.Boolean(l.value & r.value))
                      case AST.Exp.Binary.Op.Or =>
                        Deduce(
                          ?(exp) { (exp: AST.Exp.Binary) =>
                            (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                              (exp.op == AST.Exp.Binary.Op.Or) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                              (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value | r.value))))
                          } by Spec.evalExpBinaryBooleanOr(s0, exp, sN, l, sM, r)
                        )
                        return (sM, State.Value.Boolean(l.value | r.value))
                      case AST.Exp.Binary.Op.Imply =>
                        Deduce(
                          ?(exp) { (exp: AST.Exp.Binary) =>
                            (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                              (exp.op == AST.Exp.Binary.Op.Imply) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                              (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value ->: r.value))))
                          } by Spec.evalExpBinaryBooleanImply(s0, exp, sN, l, sM, r)
                        )
                        return (sM, State.Value.Boolean(l.value ->: r.value))
                      case AST.Exp.Binary.Op.Eq =>
                        Deduce(
                          ?(exp) { (exp: AST.Exp.Binary) =>
                            (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                              (exp.op == AST.Exp.Binary.Op.Eq) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                              (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value == r.value))))
                          } by Spec.evalExpBinaryBooleanEq(s0, exp, sN, l, sM, r)
                        )
                        return (sM, State.Value.Boolean(l.value == r.value))
                      case AST.Exp.Binary.Op.Ne =>
                        Deduce(
                          ?(exp) { (exp: AST.Exp.Binary) =>
                            (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                              (exp.op == AST.Exp.Binary.Op.Ne) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                              (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value != r.value))))
                          } by Spec.evalExpBinaryBooleanNe(s0, exp, sN, l, sM, r)
                        )
                        return (sM, State.Value.Boolean(l.value != r.value))
                      case _ =>
                        Deduce(
                          ?(exp) { (exp: AST.Exp.Binary) =>
                            (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->: !(
                              exp.op == AST.Exp.Binary.Op.And | exp.op == AST.Exp.Binary.Op.Or | exp.op == AST.Exp.Binary.Op.Imply |
                                exp.op == AST.Exp.Binary.Op.CondAnd | exp.op == AST.Exp.Binary.Op.CondOr | exp.op == AST.Exp.Binary.Op.CondImply |
                                exp.op == AST.Exp.Binary.Op.Eq | exp.op == AST.Exp.Binary.Op.Ne
                              ) ->:
                              (Spec.evalExp(s0, exp) == ((sN(status = State.Status.TypeError), State.Value.Error())))
                          } by Spec.evalExpBinaryBooleanTypeError(s0, exp, sN, l)
                        )
                        return (sN(status = State.Status.TypeError), State.Value.Error())
                    }
                  case r: State.Value.Integer =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM(status = State.Status.TypeError), State.Value.Error())))
                      } by Spec.evalExpBinaryTypeError1(s0, exp, sN, l, sM, r)
                    )
                    return (sM(status = State.Status.TypeError), State.Value.Error())
                  case r: State.Value.Error =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                          (Spec.evalExp(sN, exp.right) == ((sM, State.Value.Error()))) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                      } by Spec.evalExpBinaryValueError2(s0, exp, sN, sM, left)
                    )
                    return (sM, r)
                }
              }
          }
        case l: State.Value.Integer =>
          val (sM, right) = evalExp(sN, e.right)
          if (sM.status != State.Status.Normal) {
            Deduce(
              ?(exp) { (exp: AST.Exp.Binary) =>
                (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                  (Spec.evalExp(sN, exp.right) == ((sM, right))) ->: (sM.status != State.Status.Normal) ->:
                  (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
              } by Spec.evalExpBinaryNonNormal2(s0, exp, sN, left, sM, right)
            )
            return (sM, State.Value.Error())
          } else {
            right match {
              case r: State.Value.Boolean =>
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                      (Spec.evalExp(s0, exp) == ((sM(status = State.Status.TypeError), State.Value.Error())))
                  } by Spec.evalExpBinaryTypeError2(s0, exp, sN, l, sM, r)
                )
                return (sM(status = State.Status.TypeError), State.Value.Error())
              case r: State.Value.Integer =>
                e.op match {
                  case AST.Exp.Binary.Op.Add =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Add) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Integer(l.value + r.value))))
                      } by Spec.evalExpBinaryIntegerAdd(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Integer(l.value + r.value))
                  case AST.Exp.Binary.Op.Sub =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Sub) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Integer(l.value - r.value))))
                      } by Spec.evalExpBinaryIntegerSub(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Integer(l.value - r.value))
                  case AST.Exp.Binary.Op.Mul =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Mul) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Integer(l.value * r.value))))
                      } by Spec.evalExpBinaryIntegerMul(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Integer(l.value * r.value))
                  case AST.Exp.Binary.Op.Div =>
                    if (r.value == 0) {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->:
                            (exp.op == AST.Exp.Binary.Op.Div) ->: (Spec.evalExp(sN, exp.right) == ((sM, State.Value.Integer(0)))) ->:
                            (Spec.evalExp(s0, exp) == ((sM(status = State.Status.ArithError), State.Value.Error())))
                        } by Spec.evalExpBinaryIntegerDivArithError(s0, exp, sN, l, sM)
                      )
                      return (sM(status = State.Status.ArithError), State.Value.Error())
                    } else {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                            (exp.op == AST.Exp.Binary.Op.Div) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                            ((r.value != 0) -->: (Spec.evalExp(s0, exp) == ((sM, State.Value.Integer(l.value / r.value)))))
                        } by Spec.evalExpBinaryIntegerDiv(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Integer(l.value / r.value))
                    }
                  case AST.Exp.Binary.Op.Rem =>
                    if (r.value <= 0) {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->:
                            (exp.op == AST.Exp.Binary.Op.Rem) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (r.value <= 0) ->:
                            (Spec.evalExp(s0, exp) == ((sM(status = State.Status.ArithError), State.Value.Error())))
                        } by Spec.evalExpBinaryIntegerRemArithError(s0, exp, sN, l, sM, r)
                      )
                      return (sM(status = State.Status.ArithError), State.Value.Error())
                    } else {
                      Deduce(
                        ?(exp) { (exp: AST.Exp.Binary) =>
                          (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                            (exp.op == AST.Exp.Binary.Op.Rem) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                            ((r.value > 0) -->: (Spec.evalExp(s0, exp) == ((sM, State.Value.Integer(l.value % r.value)))))
                        } by Spec.evalExpBinaryIntegerRem(s0, exp, sN, l, sM, r)
                      )
                      return (sM, State.Value.Integer(l.value % r.value))
                    }
                  case AST.Exp.Binary.Op.Eq =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Eq) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value == r.value))))
                      } by Spec.evalExpBinaryIntegerEq(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value == r.value))
                  case AST.Exp.Binary.Op.Ne =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Ne) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value != r.value))))
                      } by Spec.evalExpBinaryIntegerNe(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value != r.value))
                  case AST.Exp.Binary.Op.Lt =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Lt) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value < r.value))))
                      } by Spec.evalExpBinaryIntegerLt(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value < r.value))
                  case AST.Exp.Binary.Op.Le =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Le) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value <= r.value))))
                      } by Spec.evalExpBinaryIntegerLe(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value <= r.value))
                  case AST.Exp.Binary.Op.Gt =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Gt) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value > r.value))))
                      } by Spec.evalExpBinaryIntegerGt(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value > r.value))
                  case AST.Exp.Binary.Op.Ge =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->:
                          (exp.op == AST.Exp.Binary.Op.Ge) ->: (Spec.evalExp(sN, exp.right) == ((sM, r))) ->: (sM.status == State.Status.Normal) ->:
                          (Spec.evalExp(s0, exp) == ((sM, State.Value.Boolean(l.value >= r.value))))
                      } by Spec.evalExpBinaryIntegerGe(s0, exp, sN, l, sM, r)
                    )
                    return (sM, State.Value.Boolean(l.value >= r.value))
                  case _ =>
                    Deduce(
                      ?(exp) { (exp: AST.Exp.Binary) =>
                        (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, l))) ->: (sN.status == State.Status.Normal) ->: !(
                          exp.op == AST.Exp.Binary.Op.Add | exp.op == AST.Exp.Binary.Op.Sub | exp.op == AST.Exp.Binary.Op.Mul |
                            exp.op == AST.Exp.Binary.Op.Div | exp.op == AST.Exp.Binary.Op.Rem | exp.op == AST.Exp.Binary.Op.Eq |
                            exp.op == AST.Exp.Binary.Op.Ne | exp.op == AST.Exp.Binary.Op.Lt | exp.op == AST.Exp.Binary.Op.Le |
                            exp.op == AST.Exp.Binary.Op.Gt | exp.op == AST.Exp.Binary.Op.Ge
                          ) ->:
                          (Spec.evalExp(s0, exp) == ((sN(status = State.Status.TypeError), State.Value.Error())))
                      } by Spec.evalExpBinaryIntegerTypeError(s0, exp, sN, l)
                    )
                    return (sN(status = State.Status.TypeError), State.Value.Error())
                }
              case r: State.Value.Error =>
                Deduce(
                  ?(exp) { (exp: AST.Exp.Binary) =>
                    (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, left))) ->: (sN.status == State.Status.Normal) ->:
                      (Spec.evalExp(sN, exp.right) == ((sM, State.Value.Error()))) ->:
                      (Spec.evalExp(s0, exp) == ((sM, State.Value.Error())))
                  } by Spec.evalExpBinaryValueError2(s0, exp, sN, sM, left)
                )
                return (sM, r)
            }
          }
        case _: State.Value.Error =>
          Deduce(
            ?(exp) { (exp: AST.Exp.Binary) =>
              (s0.status == State.Status.Normal) ->: (Spec.evalExp(s0, exp.left) == ((sN, State.Value.Error()))) ->:
                (Spec.evalExp(s0, exp) == ((sN, State.Value.Error())))
            } by Spec.evalExpBinaryValueError1(s0, exp, sN)
          )
          return (sN, left)
      }
    }
  }

  @pure def evalExp(state: State, exp: AST.Exp): (State, State.Value) = {
    Contract(
      Ensures(Spec.evalExp(state, exp) == Res)
    )

    if (state.status != State.Status.Normal) {
      Deduce(
        (state.status != State.Status.Normal) ->:
          (Spec.evalExp(state, exp) == ((state, State.Value.Error()))) by Spec.evalExpNonNormal(state, exp)
      )
      return (state, State.Value.Error())
    }

    exp match {
      case exp: AST.Exp.LitB => return evalLitB(state, exp)
      case exp: AST.Exp.LitZ => return evalLitZ(state, exp)
      case exp: AST.Exp.VarRef => return evalVarRef(state, exp)
      case exp: AST.Exp.Binary => return evalBinaryExp(state, exp)
    }
  }

}
