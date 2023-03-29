// #Sireum

package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.ast.{Exp, ProofAst}
import org.sireum.lang.ast.ProofAst.Step
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, Smt2Query, State, StepProofContext}
import org.sireum.message.Position

@datatype class AlgebraPlugin extends JustificationPlugin {

  val name: String = "AlgebraPlugin"

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("Algebra", "Algebra_*")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val iszStepIdTypedOpt: Option[AST.Typed] = Some(AST.Typed.Name(AST.Typed.isName, ISZ(AST.Typed.z, AST.Typed.stepId)))

  @pure override def canHandle(logika: Logika, just: Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Ref =>
        return justificationIds.contains(just.idString) && just.isOwnedBy(justificationName)
      case just: AST.ProofAst.Step.Justification.Apply if just.witnesses.isEmpty =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return justificationIds.contains(res.id) && res.owner == justificationName
          case _ => return F
        }
      case _ => return F
    }
  }

  override def handle(logika: Logika, smt2: Smt2, cache: Logika.Cache, spcMap: HashSMap[ProofAst.StepId, StepProofContext], state: State, step: Step.Regular, reporter: Logika.Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())

    val (id, posOpt, argsOpt): (String, Option[Position], Option[ISZ[AST.ProofAst.StepId]]) = step.just match {

      case just: AST.ProofAst.Step.Justification.Ref =>
        val id = just.idString
        (id, just.id.asExp.posOpt, Some(ISZ()))
      case just: AST.ProofAst.Step.Justification.Apply =>
        val invokeId = just.invokeIdent.id.value
        val ao: Option[ISZ[AST.ProofAst.StepId]] = if (just.args.size == 1) {
          just.args(0) match {
            case arg: AST.Exp.Invoke if arg.typedOpt == iszStepIdTypedOpt =>
              arg.attr.resOpt.get match {
                case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Constructor =>
                  AST.Util.toStepIds(arg.args, Logika.kind, reporter)
                case _ =>
                  AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
              }
            case arg: AST.Exp.LitString => AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
            case arg: AST.Exp.LitZ => AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
            case arg => AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
          }
        } else {
          AST.Util.toStepIds(just.args, Logika.kind, reporter)
        }
        (invokeId, just.invokeIdent.posOpt, ao)
      case _ => halt("Infeasible")
    }

    val pos = posOpt.get
    val args = argsOpt.get

    def checkAlgebraExp(e: AST.Exp): B = {
      val ac = AlgebraPlugin.MAlgebraChecker(F, Option.none())
      ac.transformExp(e)
      if (ac.hasError) {
        reporter.error(posOpt, Logika.kind, ac.msgOpt.get)
        return F
      }
      return T
    }

    var ok = T
    if (!checkAlgebraExp(step.claim)) {
      ok = F
    }
    val ((stat, nextFresh, premises, conclusion), claims): ((B, Z, ISZ[State.Claim], State.Claim), ISZ[State.Claim]) = if (args.isEmpty) {
      val q = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
      ((q._1, q._2, state.claims ++ q._3, q._4), q._3 :+ q._4)
    } else {
      var s0 = state(claims = ISZ())
      for (arg <- args) {
        val stepNo = arg
        spcMap.get(stepNo) match {
          case Some(spc: StepProofContext.Regular) =>
            if (!checkAlgebraExp(spc.exp)) {
              ok = F // TODO - grab errors?
            } else {
              // not sure what's going on here
              val ISZ((s1, v)) = logika.evalExp(Logika.Split.Disabled, smt2, cache, T, s0, spc.exp, reporter)
              val (s2, sym) = logika.value2Sym(s1, v, spc.exp.posOpt.get)
              s0 = s2.addClaim(State.Claim.Prop(T, sym))
            }
          case _ =>
            reporter.error(posOpt, Logika.kind, s"Could not find proof step $stepNo")
            ok = F
        }
      }
      val q = logika.evalRegularStepClaim(smt2, cache, s0, step.claim, step.id.posOpt, reporter)
      ((q._1, q._2, s0.claims ++ q._3, q._4), q._3 :+ q._4)
    }
    if (ok) {
      val r = smt2.valid(logika.context.methodName, logika.config, cache, T, logika.config.logVc, logika.config.logVcDirOpt, s"$id Justification", pos, premises, conclusion, reporter)
      r.kind match {
        case Smt2Query.Result.Kind.Unsat =>
          reporter.inform(posOpt.get, Reporter.Info.Kind.Verified, "TODO - msg - thumbs up")
          return Plugin.Result(T, nextFresh, claims) // TODO - unsure about nextfresh & claims here
        case _ =>
          reporter.error(posOpt, Logika.kind, "TODO - error msg - negation not unsat :(")
          return emptyResult
      }
    } else {
      return emptyResult
    }
  }
}

object AlgebraPlugin {

  @record class MAlgebraChecker(var hasError: B, var msgOpt: Option[String]) extends AST.MTransformer {
    @pure def isUnaryNumeric(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
      kind match {
        case AST.ResolvedInfo.BuiltIn.Kind.UnaryPlus =>
        case AST.ResolvedInfo.BuiltIn.Kind.UnaryMinus =>
        case _ =>
          return F
      }
      return T
    }

    @pure def isNegation(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
      kind match {
        case AST.ResolvedInfo.BuiltIn.Kind.UnaryNot =>
        case _ =>
          return F
      }
      return T
    }

    @pure def isScalarArithmetic(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
      kind match {
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryAdd =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinarySub =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryMul =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryDiv =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryRem =>
        case _ =>
          return F
      }
      return T
    }

    // TODO - equiv? equivUni? inequiv? inequivUni? fp ops?
    @pure def isRelational(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
      kind match {
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryEq =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryNe =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryLt =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryLe =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryGt =>
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryGe =>
        case _ =>
          return F
      }
      return T
    }

    override def postExp(e: Exp): MOption[AST.Exp] = {
      e match {
        case _: AST.Exp.Quant =>
          fail("TODO - error msg - can't use algebra with quantifiers")
        case b: AST.Exp.Binary =>
          b.attr.resOpt.get match {
            case AST.ResolvedInfo.BuiltIn(kind) if !(isScalarArithmetic(kind) || isRelational(kind)) =>
              fail(s"TODO - error msg - cant use algebra w/ binary op $kind")
            case _ =>
          }
        case u: AST.Exp.Unary =>
          u.attr.resOpt.get match {
            case AST.ResolvedInfo.BuiltIn(kind) if !(isUnaryNumeric(kind) || isNegation(kind)) =>
              fail(s"TODO - error msg - can't use algebra w/ unary op $kind")
            case _ =>
          }
        case _ =>
        // TODO - anything else?? methods?
      }
      return super.postExp(e)
    }

    def fail(msg: String): Unit = {
      msgOpt = Some(msg)
      hasError = T
    }
  }
}
