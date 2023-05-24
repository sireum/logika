// #Sireum

package org.sireum.logika.plugin

import org.sireum._
import org.sireum.{B, HashSMap}
import org.sireum.lang.ast.{ProofAst, ResolvedAttr, ResolvedInfo}
import org.sireum.lang.ast.ProofAst.Step
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.plugin.SubstitutionPlugin.resolveOp
import org.sireum.ops.ISZOps

@datatype class SubstitutionPlugin extends JustificationPlugin {

  val name: String = "SubstitutionPlugin"

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("Subst_>", "Subst_<")

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
      case Some(xSpc: StepProofContext.Regular) =>
        xSpc.exp match {
          case b@AST.Exp.Binary(e1, _, e2) if resolveOp(b) == AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv =>
            val (sub, repl): (AST.Exp, AST.Exp) = res.id match {
              case "Subst_>" => (e1, e2)
              case "Subst_<" => (e2, e1)
            }
            spcMap.get(y) match {
              case Some(ySpc: StepProofContext.Regular) =>
                val subResult = AST.Transformer(SubstitutionPlugin.Substitutor(sub, repl)).transformExp(SubstitutionPlugin.unit, ySpc.exp)
                if (subResult.resultOpt.get != step.claim) {
                  val msg = s"Claim ${step.id} does not match the substituted expression of ${res.id} of $x for $y"
                  reporter.error(step.claim.posOpt, Logika.kind, msg)
                  return emptyResult
                } else {
                  val msg = s"Accepted because the claim of step ${step.id} matches ${ySpc.exp} with $sub replaced by $repl"
                  reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified, msg)
                  return Plugin.Result(T, state.nextFresh, ISZ()) // TODO - unsure about nextfresh & claims here
                }
              case Some(_) =>
                reporter.error(y.posOpt, Logika.kind, s"Cannot use compound proof step $y as an argument for Substitution")
                return emptyResult
              case _ =>
                reporter.error(y.posOpt, Logika.kind, s"Could not find proof step $y")
                return emptyResult
            }
          case _ =>
            val msg = s"The first expression argument of step #$x for ${res.id} in step #${step.id} has to be a ${AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv}"
            reporter.error(x.attr.posOpt, Logika.kind, msg)
            return emptyResult
        }
      case Some(_) =>
        reporter.error(x.posOpt, Logika.kind, s"Cannot use compound proof step $x as an argument for Substitution")
        return emptyResult
      case _ =>
        reporter.error(x.posOpt, Logika.kind, s"Could not find proof step $x")
        return emptyResult
    }
  }
}

object SubstitutionPlugin {

  def unit: Unit = {} // TODO - using this for transformer's context - probably want something else

  def emptyResolvedAttr: ResolvedAttr = {
    return ResolvedAttr(Option.none(), Option.none(), Option.none())
  }

  def resolveOp(b: AST.Exp.Binary): ResolvedInfo.BuiltIn.Kind.Type = {
    b.attr.resOpt.get match {
      case AST.ResolvedInfo.BuiltIn(kind) => return kind
      case _ => halt("???")
    }
  }

  @datatype class Substitutor(sub: AST.Exp, repl: AST.Exp) extends AST.Transformer.PrePost[Unit] {
    override def postExp(ctx: Unit, exp: AST.Exp): AST.Transformer.TPostResult[Unit, AST.Exp] = {
      val substitutedExp: AST.Exp = exp match {
        case b@AST.Exp.Binary(left, opS, right) =>
          val op = resolveOp(b)
          sub match {
            case subB@AST.Exp.Binary(subLeft, _, subRight) if resolveOp(subB) == op =>
              val optFlattenableOp: Option[String] = AST.Exp.BinaryOp.precendenceLevel(opS) match {
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
                  val leftTree = ISZOps(ISZOps(restL).takeRight(restL.size - 1)).foldLeft((r: AST.Exp, t: AST.Exp) => f(r, t), restL(0))
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
