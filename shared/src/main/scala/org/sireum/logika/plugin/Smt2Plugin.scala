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
import org.sireum.lang.symbol.Info
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, Smt2Query, State, StepProofContext}

@datatype class Smt2Plugin extends JustificationPlugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "Smt2"

  val iszzTypedOpt: Option[AST.Typed] = Some(AST.Typed.Name(AST.Typed.isName, ISZ(AST.Typed.z, AST.Typed.z)))

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return (res.id == "Smt2" || res.id == "Smt2_*") && res.owner == justificationName
          case _ => return F
        }
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
    @strictpure def err(): Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val (options, timeout, resourceLimit, argsOpt): (String, Z, Z, Option[ISZ[AST.ProofAst.StepId]]) = just.args match {
      case ISZ(s: AST.Exp.LitString, t: AST.Exp.LitZ, r: AST.Exp.LitZ) => (s.value, t.value, r.value, None())
      case ISZ(s: AST.Exp.LitString, t: AST.Exp.LitZ, r: AST.Exp.LitZ, invoke: AST.Exp.Invoke) if invoke.typedOpt == iszzTypedOpt =>
        invoke.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Constructor =>
            (s.value, t.value, r.value, AST.Util.toStepIds(invoke.args, Logika.kind, reporter))
          case _ =>
            (s.value, t.value, r.value, AST.Util.toStepIds(ISZ(invoke), Logika.kind, reporter))
        }
      case _ =>
        reporter.error(just.invoke.posOpt, Logika.kind, s"Expecting literals for SMT2 configuration, timeout (ms), and resource limit")
        return err()
    }

    val lsmt2: Smt2 = smt2.withConfig(F, options,
      if (timeout <= 0) 0 else timeout, if (resourceLimit <= 0) 0 else resourceLimit, reporter) match {
      case MEither.Left(s) => s
      case MEither.Right(msg) =>
        reporter.error(just.invoke.posOpt, Logika.kind, msg)
        return err()
    }

    val id = just.invokeIdent.id.value

    if (argsOpt.isEmpty && id == "Smt2_*") {
      return Plugin.Result(F, state.nextFresh, ISZ())
    }

    val posOpt = just.invokeIdent.posOpt

    val ((stat, nextFresh, premises, conclusion), claims): ((B, Z, ISZ[State.Claim], State.Claim), ISZ[State.Claim]) = if (argsOpt.isEmpty) {
      val q = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
      ((q._1, q._2, state.claims ++ q._3, q._4), q._3 :+ q._4)
    } else {
      var s0 = state(claims = logika.context.methodOpt.get.initClaims)
      var ok = T
      for (arg <- argsOpt.get) {
        val stepNo = arg
        spcMap.get(stepNo) match {
          case Some(spc: StepProofContext.Regular) =>
            val ISZ((s1, v)) = logika.evalExp(Logika.Split.Disabled, lsmt2, cache, T, s0, spc.exp, reporter)
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
        return Plugin.Result(F, s0.nextFresh, ISZ())
      }
      val q = logika.evalRegularStepClaim(lsmt2, cache, s0, step.claim, step.id.posOpt, reporter)
      ((q._1, q._2, s0.claims ++ q._3, q._4), q._3 :+ q._4)
    }

    val status: B = if (stat) {
      val r = lsmt2.valid(logika.context.methodName, cache, T, logika.config.logVc, logika.config.logVcDirOpt,
        s"${just.invokeIdent.id.value} Justification", posOpt.get, premises, conclusion, reporter)
      def error(msg: String): B = {
        reporter.error(posOpt, Logika.kind, msg)
        return F
      }

      r.kind match {
        case Smt2Query.Result.Kind.Unsat => T
        case Smt2Query.Result.Kind.Sat => error(s"Invalid claim of proof step ${step.id}")
        case Smt2Query.Result.Kind.Unknown => error(s"Could not deduce the claim of proof step ${step.id}")
        case Smt2Query.Result.Kind.Timeout => error(s"Timed out when deducing the claim of proof step ${step.id}")
        case Smt2Query.Result.Kind.Error => error(s"Error occurred when deducing the claim of proof step ${step.id}")
      }
    } else {
      F
    }
    smt2.updateFrom(lsmt2)
    return Plugin.Result(status, nextFresh, claims)
  }

}
