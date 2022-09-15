// #Sireum
/*
 Copyright (c) 2017-2022, Robby, Kansas State University
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
import org.sireum.message.Position
import org.sireum.lang.{ast => AST}
import org.sireum.logika.{Logika, Smt2, Smt2Query, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

@datatype class AutoPlugin extends Plugin {

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("Auto", "Auto_*", "Premise")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val iszzTypedOpt: Option[AST.Typed] = Some(AST.Typed.Name(AST.Typed.isName, ISZ(AST.Typed.z, AST.Typed.z)))

  val name: String = "AutoPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
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

  override def handle(logika: Logika,
                      smt2: Smt2,
                      cache: Smt2.Cache,
                      log: B,
                      logDirOpt: Option[String],
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): Plugin.Result = {

    val (id, posOpt, argsOpt): (String, Option[Position], Option[ISZ[AST.ProofAst.StepId]]) = step.just match {
      case just: AST.ProofAst.Step.Justification.Ref =>
        val id = just.idString
        (id, just.id.asExp.posOpt, Some(ISZ()))
      case just: AST.ProofAst.Step.Justification.Apply =>
        val invokeId = just.invokeIdent.id.value
        val ao: Option[ISZ[AST.ProofAst.StepId]] = if (just.args.size === 1) {
          just.args(0) match {
            case arg: AST.Exp.Invoke if arg.typedOpt == iszzTypedOpt =>
              arg.attr.resOpt.get match {
                case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Constructor =>
                  AST.Util.toStepIds(arg.args, Logika.kind, reporter)
                case _ =>
                  AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
              }
            case arg: AST.Exp.LitStepId => AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
            case arg: AST.Exp.LitZ => AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
            case arg => AST.Util.toStepIds(ISZ(arg), Logika.kind, reporter)
          }
        } else {
          AST.Util.toStepIds(just.args, Logika.kind, reporter)
        }
        (invokeId, just.invokeIdent.posOpt, ao)
      case _ => halt("Infeasible")
    }

    if (argsOpt.isEmpty) {
      return Plugin.Result(F, state.nextFresh, state.claims)
    }

    val pos = posOpt.get
    val args = argsOpt.get

    val provenClaims = HashMap ++ (for (spc <- spcMap.values if spc.isInstanceOf[StepProofContext.Regular]) yield
      (AST.Util.normalizeExp(spc.asInstanceOf[StepProofContext.Regular].exp), spc.asInstanceOf[StepProofContext.Regular]))

    if (args.isEmpty) {
      val claimNorm = step.claimNorm
      val spcOpt = provenClaims.get(claimNorm)
      spcOpt match {
        case Some(spc) =>
          val spcPos = spc.stepNo.posOpt.get
          reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
            st"""Accepted by using ${Plugin.stepNoDesc(F, spc.stepNo)} at [${spcPos.beginLine}, ${spcPos.beginColumn}], i.e.:
                |
                |${spc.exp}
                |""".render)
          return Plugin.Result(T, state.nextFresh, spc.claims)
        case _ =>
          if (id === "Premise") {
            val pathConditions = org.sireum.logika.Util.claimsToExps(pos, logika.context.methodName, state.claims, logika.th, T)
            val set = HashSSet.empty[AST.Exp] ++ (for (e <- pathConditions) yield e)
            val normSet = HashSSet.empty[AST.Exp] ++ (for (e <- pathConditions) yield AST.Util.normalizeExp(e))
            if (normSet.contains(claimNorm)) {
              val q = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
              val (status, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
              reporter.inform(pos, Logika.Reporter.Info.Kind.Verified,
                st"""Accepted because the stated claim is in the path conditions:
                    |{
                    |  ${(for (e <- set.elements) yield e.prettyST, ";\n")}
                    |}""".render)
              return Plugin.Result(status, nextFresh, claims)
            } else {
              reporter.error(posOpt, Logika.kind,
                st"""The stated claim has not been proven before nor is a premise in:
                    |{
                    |  ${(for (e <- set.elements) yield e.prettyST, ";\n")}
                    |}""".render)
              return Plugin.Result(F, state.nextFresh, state.claims)
            }
          }
      }
    }

    val ((stat, nextFresh, premises, conclusion), claims): ((B, Z, ISZ[State.Claim], State.Claim), ISZ[State.Claim]) = if (args.isEmpty) {
      val q = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
      ((q._1, q._2, state.claims ++ q._3, q._4), q._3 :+ q._4)
    } else {
      var s0 = state(claims = ISZ())
      var ok = T
      for (arg <- args) {
        val stepNo = arg
        spcMap.get(stepNo) match {
          case Some(spc: StepProofContext.Regular) =>
            val ISZ((s1, v)) = logika.evalExp(Logika.Split.Disabled, smt2, cache, T, s0, spc.exp, reporter)
            val (s2, sym) = logika.value2Sym(s1, v, spc.exp.posOpt.get)
            s0 = s2.addClaim(State.Claim.Prop(T, sym))
          case Some(_) =>
            reporter.error(posOpt, Logika.kind, s"Cannot use compound proof step $stepNo as an argument for $id")
            ok = F
          case _ =>
            reporter.error(posOpt, Logika.kind, s"Could not find proof step $stepNo")
            ok = F
        }
      }
      if (!ok) {
        return Plugin.Result(F, s0.nextFresh, s0.claims)
      }
      val q = logika.evalRegularStepClaim(smt2, cache, s0, step.claim, step.id.posOpt, reporter)
      ((q._1, q._2, s0.claims ++ q._3, q._4), q._3 :+ q._4)
    }

    var status = stat
    if (status) {
      val r = smt2.valid(cache, T, log, logDirOpt, s"$id Justification", pos, premises, conclusion, reporter)

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

}
