// #Sireum #Logika

import org.sireum._
import org.sireum.justification.natded.pred.allE
import org.sireum.justification.{ClaimOf, Auto}

object AST {

  @datatype trait Exp

  object Exp {

    @datatype class LitB(val value: B) extends Exp

    @datatype class LitZ(val value: Z) extends Exp

    @datatype class VarRef(val id: String) extends Exp

    /* TODO
    @datatype class Binary(val left: Exp, val op: Binary.Op.Type, val right: Exp) extends Exp

    object Binary {
      @enum object Op {
        "Add"
        "Sub"
        "Mul"
        "Div"
        "Rem"
        "And"
        "Or"
        "Imply"
        "CondAnd"
        "CondOr"
        "CondImply"
      }
    }
    */
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
    "Error"
  }

}

object Spec {

  object Aux {
    @spec def valueToB(value: State.Value): B = $

    @spec def valueToBFact(value: State.Value) = Fact(
      value.isInstanceOf[State.Value.Boolean] -->: (valueToB(value) == value.asInstanceOf[State.Value.Boolean].value)
    )

    @spec def valueToZ(value: State.Value): Z = $

    @spec def valueToZFact(value: State.Value) = Fact(
      value.isInstanceOf[State.Value.Integer] -->: (valueToZ(value) == value.asInstanceOf[State.Value.Integer].value)
    )
  }

  @spec def evalExp(state: State, exp: AST.Exp): (State, State.Value) = $

  @spec def evalExpLitBFact(s0: State, exp: AST.Exp, sN: State, v: State.Value) = Fact(
    exp.isInstanceOf[AST.Exp.LitB] -->: (
      (s0 === sN &
        v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
        (Spec.evalExp(s0, exp) === ((sN, v)))
      )
  )

  @spec def evalExpLitZFact(s0: State, exp: AST.Exp, sN: State, v: State.Value) = Fact(
    exp.isInstanceOf[AST.Exp.LitZ] -->: (
      (s0 === sN &
        v === State.Value.Integer(exp.asInstanceOf[AST.Exp.LitZ].value)) ->:
        (Spec.evalExp(s0, exp) === ((sN, v)))
      )
  )

  @spec def evalExpVarRefErrorFact(s0: State, exp: AST.Exp, sN: State, v: State.Value) = Fact(
    exp.isInstanceOf[AST.Exp.VarRef] -->: (
      (s0.store.get(exp.asInstanceOf[AST.Exp.VarRef].id) === None[State.Value]()) ->:
        ((sN === s0(status = State.Status.Error) &
          v === State.Value.Error()) ->:
          (Spec.evalExp(s0, exp) === ((sN, v))))
      )
  )

  @spec def evalExpVarRefFact(s0: State, exp: AST.Exp, sN: State, v: State.Value) = Fact(
    exp.isInstanceOf[AST.Exp.VarRef] -->: (
      (s0.store.get(exp.asInstanceOf[AST.Exp.VarRef].id) === Some(v) &
        s0 === sN) ->:
        (Spec.evalExp(s0, exp) === ((sN, v)))
      )
  )
}

object Impl {

  def evalLitB(state: State, e: AST.Exp.LitB): (State, State.Value) = {
    Contract(
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val exp: AST.Exp = e
    val rv: State.Value = State.Value.Boolean(e.value)
    Deduce(
      //@formatter:off
       1 #> ∀{(s0: State, exp: AST.Exp, sN: State, v: State.Value) =>
                exp.isInstanceOf[AST.Exp.LitB] -->: (
                  (s0 === sN &
                   v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                      (Spec.evalExp(s0, exp) === ((sN, v))))}                              by ClaimOf(Spec.evalExpLitBFact _),
       2 #> ∀{(exp: AST.Exp, sN: State, v: State.Value) =>
                exp.isInstanceOf[AST.Exp.LitB] -->: (
                  (state === sN &
                   v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                      (Spec.evalExp(state, exp) === ((sN, v))))}                           by allE((s0: State) =>
                                                                                                     ∀{(exp: AST.Exp, sN: State, v: State.Value) =>
                                                                                                         exp.isInstanceOf[AST.Exp.LitB] -->: (
                                                                                                           (s0 === sN &
                                                                                                            v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                                                                                                               (Spec.evalExp(s0, exp) === ((sN, v))))},
                                                                                                   state) and 1,
       3 #> ∀{(sN: State, v: State.Value) =>
                exp.isInstanceOf[AST.Exp.LitB] -->: (
                  (state === sN &
                   v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                      (Spec.evalExp(state, exp) === ((sN, v))))}                           by allE((exp: AST.Exp) =>
                                                                                                     ∀{(sN: State, v: State.Value) =>
                                                                                                         exp.isInstanceOf[AST.Exp.LitB] -->: (
                                                                                                           (state === sN &
                                                                                                            v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                                                                                                               (Spec.evalExp(state, exp) === ((sN, v))))},
                                                                                                   exp) and 2,
       4 #> ∀{(v: State.Value) =>
                exp.isInstanceOf[AST.Exp.LitB] -->: (
                  (state === state &
                   v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                       (Spec.evalExp(state, exp) === ((state, v))))}                       by allE((sN: State) =>
                                                                                                     ∀{(v: State.Value) =>
                                                                                                         exp.isInstanceOf[AST.Exp.LitB] -->: (
                                                                                                           (state === sN &
                                                                                                            v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                                                                                                               (Spec.evalExp(state, exp) === ((sN, v))))},
                                                                                                   state) and 3,
       5 #> (exp.isInstanceOf[AST.Exp.LitB] -->: (
               (state === state &
                rv === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                  (Spec.evalExp(state, exp) === ((state, rv)))))                           by allE((v: State.Value) => exp.isInstanceOf[AST.Exp.LitB] -->: (
                                                                                                     (state === state &
                                                                                                      v === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                                                                                                         (Spec.evalExp(state, exp) === ((state, v)))),
                                                                                                   rv) and 4,
       6 #> exp.isInstanceOf[AST.Exp.LitB]                                                 by Auto,
       7 #> ((state === state &
              rv === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value)) ->:
                (Spec.evalExp(state, exp) === ((state, rv))))                              by Auto,
       8 #> (state === state &
             rv === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value))             by Auto,
       9 #> (rv === State.Value.Boolean(exp.asInstanceOf[AST.Exp.LitB].value))             by Auto,
      10 #> (Spec.evalExp(state, exp) === ((state, rv)))                                   by Auto,
      //@formatter:on
    )
    return (state, rv)
  }

  def evalLitZ(state: State, e: AST.Exp.LitZ): (State, State.Value) = {
    Contract(
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val rv: State.Value = State.Value.Integer(e.value)
    val exp: AST.Exp = e
    Deduce(
      //@formatter:off
      (exp.isInstanceOf[AST.Exp.LitZ] -->: (
        (state === state &
         rv === State.Value.Integer(exp.asInstanceOf[AST.Exp.LitZ].value)) ->:
             (Spec.evalExp(state, exp) === ((state, rv)))))                                by Spec.evalExpLitZFact(state, exp, state, rv),
      (Spec.evalExp(state, exp) === ((state, rv)))                                         by Auto
      //@formatter:on
    )
    return (state, rv)
  }

  def evalVarRef(state: State, e: AST.Exp.VarRef): (State, State.Value) = {
    Contract(
      Ensures(Spec.evalExp(state, e) == Res)
    )
    val exp: AST.Exp = e
    val r: (State, State.Value) = state.store.get(e.id) match {
      case Some(rv) =>
        Deduce(
          //@formatter:off
          (exp.isInstanceOf[AST.Exp.VarRef] -->: (
            (state.store.get(exp.asInstanceOf[AST.Exp.VarRef].id) === Some(rv) &
             state === state) ->:
                (Spec.evalExp(state, exp) === ((state, rv)))))                             by Spec.evalExpVarRefFact(state, exp, state, rv),
          (Spec.evalExp(state, exp) === ((state, rv)))                                     by Auto
          //@formatter:on
        )
        (state, rv)
      case _ =>
        val rs = state(status = State.Status.Error)
        val rv: State.Value = State.Value.Error()
        Deduce(
          //@formatter:off
          (exp.isInstanceOf[AST.Exp.VarRef] -->: (
            (state.store.get(exp.asInstanceOf[AST.Exp.VarRef].id) === None[State.Value]()) ->:
              ((rs === state(status = State.Status.Error) &
                rv === State.Value.Error()) ->:
                  (Spec.evalExp(state, exp) === ((rs, rv))))))                             by Spec.evalExpVarRefErrorFact(state, exp, rs, rv),
          (Spec.evalExp(state, exp) === ((rs, rv)))                                        by Auto
          //@formatter:on
        )
        (rs, rv)
    }
    return r
  }

  def evalExp(state: State, exp: AST.Exp): (State, State.Value) = {
    Contract(
      Ensures(Spec.evalExp(state, exp) == Res)
    )
    val r: (State, State.Value) = exp match {
      case e: AST.Exp.LitB => evalLitB(state, e)
      case e: AST.Exp.LitZ => evalLitZ(state, e)
      case e: AST.Exp.VarRef => evalVarRef(state, e)
    }
    return r
  }

}