// #Sireum
/*
 Copyright (c) 2017-2023, Robby, Kansas State University
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice, this
    list of conditions and the following disclaimer.
 2. Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.logika.{Logika, Smt2, Smt2Query, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

object AutoPlugin {
  @record class MAlgebraChecker(var reporter: Reporter) extends AST.MTransformer {
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

    @pure def isRelational(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
      kind match {
        case AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv =>
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

    override def postExp(e: AST.Exp): MOption[AST.Exp] = {
      def failE(): Unit = {
        fail(e.posOpt, st"Algebra cannot be used on '${e.prettyST}'".render)
      }
      e match {
        case _: AST.Exp.Quant => fail(e.posOpt, "Algebra cannot be used with quantifiers")
        case _: AST.Exp.LitZ =>
        case _: AST.Exp.Ident if e.typedOpt == AST.Typed.zOpt =>
        case e: AST.Exp.Binary =>
          e.attr.resOpt.get match {
            case AST.ResolvedInfo.BuiltIn(kind) =>
              if (!(isScalarArithmetic(kind) || isRelational(kind))) {
                fail(e.posOpt, s"Algebra cannot be used with binary op '${e.op}'")
              }
            case _ => failE()
          }
        case e: AST.Exp.Unary =>
          e.attr.resOpt.get match {
            case AST.ResolvedInfo.BuiltIn(kind) =>
              if (!(isUnaryNumeric(kind) || isNegation(kind))) {
                fail(e.posOpt, s"Algebra cannot be used with unary op '${e.op}'")
              }
            case _ => failE()
          }
        case e: AST.Exp.Invoke =>
          e.ident.resOpt match {
            case Some(res: AST.ResolvedInfo.Method) if res.mode == AST.MethodMode.Spec =>
            case _ =>
              fail(e.ident.posOpt, s"Algebra cannot be used with non-spec method invocation")
          }
        case _ => failE()
      }
      return super.postExp(e)
    }

    def fail(posOpt: Option[message.Position], msg: String): Unit = {
      reporter.error(posOpt, Logika.kind, msg)
    }
  }

  def detectOrIntro(th: TypeHierarchy, claim: AST.Exp, pc: ISZ[AST.Exp]): Option[ST] = {
    val (left, right): (AST.Exp, AST.Exp) = claim match {
      case claim: AST.Exp.Binary =>
        claim.attr.resOpt match {
          case Some(AST.ResolvedInfo.BuiltIn(kind)) if kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryOr || kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
            (claim.left, claim.right)
          case _ => return None()
        }
      case _ => return None()
    }

    val leftNorm = th.normalizeExp(left)
    val rightNorm = th.normalizeExp(right)

    var posAntecedents = HashMap.empty[(AST.Exp, AST.Exp), AST.Exp.Binary]
    var negAntecedents = HashMap.empty[(AST.Exp, AST.Exp), AST.Exp.Binary]

    for (c <- pc) {
      c match {
        case c: AST.Exp.Binary =>
          c.attr.resOpt match {
            case Some(AST.ResolvedInfo.BuiltIn(kind)) if kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryImply || kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
              val crNorm = th.normalizeExp(c.right)
              val isLeft = crNorm == leftNorm
              val isRight = crNorm == rightNorm
              if (isLeft || isRight) {
                c.left match {
                  case ant: AST.Exp.Unary if ant.op == AST.Exp.UnaryOp.Not =>
                    val antNorm = th.normalizeExp(ant.exp)
                    val key = (if (isLeft) rightNorm else leftNorm, antNorm)
                    posAntecedents.get(key) match {
                      case Some(v) =>
                        return Some(
                          st"""Accepted because both:
                              |
                              |* ${v.prettyST}, and
                              |
                              |* ${c.prettyST}
                              |
                              |are in the path conditions:
                              |{
                              |  ${(for (e <- pc) yield e.prettyST, ";\n")}
                              |}"""
                        )
                      case _ => negAntecedents = negAntecedents + (if (isLeft) leftNorm else rightNorm, antNorm) ~> c
                    }
                  case ant =>
                    val antNorm = th.normalizeExp(ant)
                    val key = (if (isLeft) rightNorm else leftNorm, antNorm)
                    negAntecedents.get(key) match {
                      case Some(v) =>
                        return Some(
                          st"""Accepted because both:
                              |
                              |* ${c.prettyST}, and
                              |
                              |* ${v.prettyST}
                              |
                              |are in the path conditions:
                              |{
                              |  ${(for (e <- pc) yield e.prettyST, ";\n")}
                              |}
                              |"""
                        )
                      case _ =>
                        posAntecedents = posAntecedents + (if (isLeft) leftNorm else rightNorm, antNorm) ~> c
                    }
                }
              }
            case _ =>
          }
        case _ =>
      }
    }
    return None()
  }

}

@datatype class AutoPlugin extends JustificationPlugin {

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("Algebra", "Auto", "Premise")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "AutoPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Ref =>
        return justificationIds.contains(just.idString) && just.isOwnedBy(justificationName)
      case _ => return F
    }
  }

  override def handle(logika: Logika,
                      smt2: Smt2,
                      cache: Logika.Cache,
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): Plugin.Result = {

    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Ref]

    val id = just.idString
    val posOpt = just.id.posOpt
    val pos = posOpt.get

    def checkAlgebraExp(e: AST.Exp): B = {
      val ac = AutoPlugin.MAlgebraChecker(reporter.empty)
      ac.transformExp(e)
      reporter.combine(ac.reporter)
      return !ac.reporter.hasError
    }

    def checkValid(psmt2: Smt2, stat: B, nextFresh: Z, premises: ISZ[State.Claim], conclusion: State.Claim,
                   claims: ISZ[State.Claim]): Plugin.Result = {
      if (id == "Algebra" && !checkAlgebraExp(step.claim)) {
        return Plugin.Result(F, state.nextFresh, ISZ())
      }

      var status = stat
      if (status) {
        val r = psmt2.valid(logika.context.methodName, logika.config, cache, T, s"$id Justification", pos, premises,
          conclusion, reporter)

        def error(msg: String): B = {
          reporter.error(posOpt, Logika.kind, msg)
          return F
        }

        status = r.kind match {
          case Smt2Query.Result.Kind.Unsat => T
          case Smt2Query.Result.Kind.Sat => error(s"Invalid claim of proof step ${step.id}")
          case Smt2Query.Result.Kind.Unknown => error(s"Could not deduce the claim of proof step ${step.id}")
          case Smt2Query.Result.Kind.Timeout => error(s"Timed out when deducing the claim of proof step ${step.id}")
          case Smt2Query.Result.Kind.Error => error(s"Error occurred when deducing the claim of proof step ${step.id}")
        }
      }
      return Plugin.Result(status, nextFresh, claims)
    }

    val provenClaims = HashMap ++ (for (spc <- spcMap.values if spc.isInstanceOf[StepProofContext.Regular]) yield
      (logika.th.normalizeExp(spc.asInstanceOf[StepProofContext.Regular].exp), spc.asInstanceOf[StepProofContext.Regular]))

    if (!just.hasWitness) {
      val claimNorm = logika.th.normalizeExp(step.claim)
      val spcOpt = provenClaims.get(claimNorm)
      spcOpt match {
        case Some(spc) =>
          if (logika.config.detailedInfo) {
            val spcPos = spc.stepNo.posOpt.get
            reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
              st"""Accepted by using ${Plugin.stepNoDesc(F, spc.stepNo)} at [${spcPos.beginLine}, ${spcPos.beginColumn}], i.e.:
                  |
                  |${spc.exp}
                  |""".render)
          }
          return Plugin.Result(T, state.nextFresh, spc.claims)
        case _ =>
          val (pathConditions, _) = org.sireum.logika.Util.claimsToExps(logika.jescmPlugins._4, pos,
            logika.context.methodName, state.claims, logika.th, logika.config.atLinesFresh)
          val normPathConditions = HashSSet.empty[AST.Exp] ++ (for (e <- pathConditions) yield logika.th.normalizeExp(e))
          if (normPathConditions.contains(claimNorm)) {
            if (logika.config.detailedInfo) {
              reporter.inform(pos, Logika.Reporter.Info.Kind.Verified,
                st"""Accepted because the stated claim is in the path conditions:
                    |{
                    |  ${(for (e <- pathConditions) yield e.prettyST, ";\n")}
                    |}""".render)
            }
            return Plugin.Result(T, state.nextFresh, ISZ())
          } else if (id == "Premise") {
            AutoPlugin.detectOrIntro(logika.th, step.claim, pathConditions) match {
              case Some(acceptMsg) =>
                reporter.inform(pos, Logika.Reporter.Info.Kind.Verified, acceptMsg.render)
                return Plugin.Result(T, state.nextFresh, ISZ())
              case _ =>
                reporter.error(posOpt, Logika.kind,
                  st"""The stated claim has not been proven before nor is a premise in:
                      |{
                      |  ${(for (e <- pathConditions) yield e.prettyST, ";\n")}
                      |}""".render)
                return Plugin.Result(F, state.nextFresh, ISZ())
            }
          }
      }
    }

    if (!just.hasWitness) {
      val (stat, nextFresh, premises, conclusion) =
        logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
      return checkValid(smt2, stat, nextFresh, state.claims ++ premises, conclusion, premises :+ conclusion)
    } else {
      val psmt2 = smt2.emptyCache(logika.config)
      val atMap = org.sireum.logika.Util.claimsToExps(logika.jescmPlugins._4, pos, logika.context.methodName,
        state.claims, logika.th, F)._2
      var s1 = state.unconstrainedClaims
      var ok = T
      for (arg <- just.witnesses if ok) {
        val stepNo = arg
        spcMap.get(stepNo) match {
          case Some(spc: StepProofContext.Regular) =>
            val (s2, exp) = logika.rewriteAt(atMap, s1, spc.exp, reporter)
            val ISZ((s3, v)) = logika.evalExp(Logika.Split.Disabled, psmt2, cache, T, s2, exp, reporter)
            val (s4, sym) = logika.value2Sym(s3, v, spc.exp.posOpt.get)
            s1 = s4.addClaim(State.Claim.Prop(T, sym))
          case Some(_) =>
            reporter.error(posOpt, Logika.kind, s"Cannot use compound proof step $stepNo as an argument for $id")
            ok = F
          case _ =>
            reporter.error(posOpt, Logika.kind, s"Could not find proof step $stepNo")
            ok = F
        }
      }
      if (!ok) {
        return Plugin.Result(F, state.nextFresh, ISZ())
      }
      val (s5, exp) = logika.rewriteAt(atMap, s1, step.claim, reporter)
      val (stat, nextFresh, premises, conclusion) =
        logika.evalRegularStepClaim(psmt2, cache, s5, exp, step.id.posOpt, reporter)
      val r = checkValid(psmt2, stat, nextFresh, s1.claims ++ premises, conclusion, premises :+ conclusion)
      smt2.combineWith(psmt2)
      return r
    }
  }

}
