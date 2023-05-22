// #Sireum

package org.sireum.logika.plugin

import org.sireum._
import org.sireum.{B, HashSMap}
import org.sireum.lang.ast.{ProofAst, ResolvedAttr}
import org.sireum.lang.ast.ProofAst.Step
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.ops.ISZOps

@datatype class SubstitutionPlugin extends JustificationPlugin {

  val name: String = "SubstitutionPlugin"

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("Subst1", "Subst2")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  override def canHandle(logika: Logika, just: Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return justificationIds.contains(res.id) && res.owner == justificationName
          case _ => return F
        }
      case _ => return F
    }
  }

  override def handle(logika: Logika, smt2: Smt2, cache: Logika.Cache, spcMap: HashSMap[ProofAst.StepId, StepProofContext], state: State, step: Step.Regular, reporter: Logika.Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())

    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    val ISZ(x, y) = AST.Util.toStepIds(just.args, Logika.kind, reporter).get

    spcMap.get(x) match {
      case Some(StepProofContext.Regular(_, AST.Exp.Binary(e1, AST.Exp.BinaryOp.Eq, e2), _)) =>
        val (sub, repl): (AST.Exp, AST.Exp) = res.id match {
          case "Subst1" => (e1, e2)
          case "Subst2" => (e2, e1)
        }
        val exp = spcMap.get(y).get.asInstanceOf[StepProofContext.Regular].exp // TODO - is casting to StepProofContext.Regular safe? what about "".SubProof??
        val subResult = AST.Transformer(SubstitutionPlugin.Substitutor(sub, repl)).transformExp(SubstitutionPlugin.unit, exp)
        if (subResult.resultOpt.get != step.claim) {
          reporter.error(step.claim.posOpt, Logika.kind, "TODO - error msg - substitution not as expected")
          return emptyResult
        } else {
          reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified, "TODO - msg - good sub")
          return Plugin.Result(T, state.nextFresh, ISZ()) // TODO - unsure about nextfresh & claims here
        }
      case Some(StepProofContext.Regular(_, _: AST.Exp.Binary, _)) =>
        reporter.error(step.claim.posOpt, Logika.kind, "TODO - error msg - gotta be an equality")
        return emptyResult
      case _ =>
        return emptyResult
    }
  }
}

object SubstitutionPlugin {

  def unit: Unit = {} // TODO - using this for transformer's context - probably want something else

  def emptyResolvedAttr: ResolvedAttr = {
    return ResolvedAttr(Option.none(), Option.none(), Option.none())
  }

  @datatype class Substitutor(sub: AST.Exp, repl: AST.Exp) extends AST.Transformer.PrePost[Unit] {
    override def postExp(ctx: Unit, exp: AST.Exp): AST.Transformer.TPostResult[Unit, AST.Exp] = {
      val substitutedExp: AST.Exp = exp match {
        case AST.Exp.Binary(left, op, right) =>
          sub match {
            case AST.Exp.Binary(subLeft, subOp, subRight) if subOp == op =>
              val optFlattenableOp: Option[String] = AST.Exp.BinaryOp.precendenceLevel(op) match {
                case z"2" => Some(AST.Exp.BinaryOp.Mul)
                case z"3" => Some(AST.Exp.BinaryOp.Add)
                case _ => Option.none()
              }
              def flatten(e: AST.Exp): ISZ[AST.Exp] = {
                e match {
                  case AST.Exp.Binary(l, o, r) if optFlattenableOp.exists(fOp => o == fOp) =>
                    return flatten(l) ++ ISZ(r) // due to plus/mul ops being parsed as left-associative, right subtree has to be an exact match... I think??
                  case _ =>
                    return ISZ(e)
                }
              }
              val fLeft = flatten(left)
              val fSubLeft = flatten(subLeft)
              if (ISZOps(fLeft).takeRight(fSubLeft.size) == fSubLeft && right == subRight) {
                val restL = ISZOps(fLeft).take(fLeft.size - fSubLeft.size)
                if (restL.isEmpty) {
                  repl
                } else {
                  val flattenedOp = optFlattenableOp.get
                  @pure def f(r: AST.Exp, t: AST.Exp): AST.Exp = {
                    return AST.Exp.Binary(r, flattenedOp, t, emptyResolvedAttr)
                  }
                  val leftTree = ISZOps(ISZOps(restL).takeRight(restL.size - 1)).foldLeft((r: AST.Exp, t: AST.Exp) => f(r,t), restL(0))
                  AST.Exp.Binary(leftTree, flattenedOp, repl, emptyResolvedAttr)
                }
              } else {
                exp
              }
            case _ =>
              exp
          }
        case _ =>
          if (exp == sub) repl else exp
      }
      return AST.Transformer.TPostResult(ctx, Some(substitutedExp))
    }
  }
}
