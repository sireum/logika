// #Sireum
/*
 Copyright (c) 2017-2024, Ryan Peroutka, Galois, Inc.
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
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.RewritingSystem.{Rewriter, toCondEquiv}
import org.sireum.logika.{Logika, RewritingSystem, Smt2, State, StepProofContext}

@datatype class RewritePlugin extends JustificationPlugin {

  val name: String = "RewritePlugin"

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Ref =>
        return just.id.value == "Simpl" && just.isOwnedBy(justificationName)
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invoke.ident.attr.resOpt match {
          case Some(res: AST.ResolvedInfo.Method) if (res.id == "Rewrite" || res.id == "Eval") && res.owner == justificationName => return T
          case _ =>
        }
      case _ =>
    }
    return F
  }

  override def checkMode(logika: Logika, just: AST.ProofAst.Step.Justification, reporter: Reporter): B = {
    return T
  }

  override def handle(logika: Logika, smt2: Smt2, cache: Logika.Cache,
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext], state: State,
                      step: AST.ProofAst.Step.Regular, reporter: Logika.Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())
    @strictpure def justArgs: ISZ[AST.Exp] = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply].args
    val isSimpl = step.just.id.value == "Simpl"
    val isEval = step.just.id.value == "Eval"
    val patterns: ISZ[Rewriter.Pattern] =
      if (isEval || isSimpl) ISZ()
      else RewritingSystem.retrievePatterns(logika.th, cache, justArgs(0))
    var provenClaims = HashSMap.empty[AST.ProofAst.StepId, AST.CoreExp.Base]
    if (step.just.hasWitness) {
      for (w <- step.just.witnesses) {
        spcMap.get(w) match {
          case Some(spc: StepProofContext.Regular) =>
            provenClaims = provenClaims + w ~> spc.coreExpClaim
          case Some(_) =>
            reporter.error(w.posOpt, Logika.kind, s"Expecting a regular proof step for $w")
          case _ =>
            reporter.error(w.posOpt, Logika.kind, s"Could not find proof step $w")
        }
      }
    } else {
      for (spc <- spcMap.values) {
        spc match {
          case spc: StepProofContext.Regular if !spc.stepNo.isPremise =>
            provenClaims = provenClaims + spc.stepNo ~> spc.coreExpClaim
          case _ =>
        }
      }
    }
    @strictpure def traceOpt(trace: ISZ[RewritingSystem.Trace]): Option[ST] =
      if (trace.nonEmpty && (logika.config.rwTrace || logika.config.rwEvalTrace))
        Some(st"""Trace:
            |
            |${(for (te <- trace) yield te.toST, "\n\n")}""")
      else None()
    val rwPc = Rewriter(if (logika.config.rwPar) logika.config.parCores else 1,
      logika.th, provenClaims, patterns, logika.config.rwTrace, logika.config.rwEvalTrace, F, ISZ())
    val stepClaim = RewritingSystem.translateExp(logika.th, F, step.claim)

    if (logika.config.rwEvalTrace) {
      rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Begin("simplifying", stepClaim)
    }

    val stepClaimEv: AST.CoreExp.Base = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all,
      rwPc.provenClaimStepIdMap, stepClaim, logika.config.rwEvalTrace) match {
      case Some((e, t)) =>
        rwPc.trace = t
        e
      case _ => stepClaim
    }

    if (logika.config.rwEvalTrace) {
      rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Done(stepClaim, stepClaimEv)
    }

    if (stepClaimEv == AST.CoreExp.True) {
      reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Evaluating ${stepClaim.prettyST} produces T, hence the claim holds
            |
            |${traceOpt(rwPc.trace)}""".render)
      if (isSimpl) {
        val q = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
        val (stat, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
        return Plugin.Result(stat, nextFresh, claims)
      } else {
        reporter.warn(step.just.id.attr.posOpt, Logika.kind, "The claim can be discharged by using Simpl instead")
      }
    } else if (isSimpl) {
      reporter.error(step.just.id.attr.posOpt, Logika.kind,
        st"""Could not simplify ${stepClaim.prettyST} to T
            |
            |After simplification:
            |  ${stepClaimEv.prettyST}
            |
            |${traceOpt(rwPc.trace)}""".render)
      return emptyResult
    }

    val simplTrace = rwPc.trace
    rwPc.trace = ISZ()
    val from: AST.ProofAst.StepId =
      AST.Util.toStepIds(ISZ(justArgs(if (isEval) 0 else 1)), Logika.kind, reporter) match {
        case Some(s) => s(0)
        case _ => return emptyResult
      }
    val fromClaim: AST.Exp = spcMap.get(from) match {
      case Some(spc: StepProofContext.Regular) => spc.exp
      case _ =>
        reporter.error(from.posOpt, Logika.kind, s"Expecting a regular proof step")
        return emptyResult
    }
    val fromCoreClaim = RewritingSystem.translateExp(logika.th, F, fromClaim)
    @strictpure def simplTraceOpt: Option[ST] = if (stepClaim == stepClaimEv) None() else Some(
      st"""and/or after simplifying the step claim to:
          |  ${stepClaimEv.prettyST}"""
    )

    var rwClaim = fromCoreClaim
    if (isEval) {
      if (logika.config.rwEvalTrace) {
        rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Begin("evaluating", fromCoreClaim)
      }
      rwClaim = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all,
        rwPc.provenClaimStepIdMap, rwClaim, logika.config.rwEvalTrace) match {
        case Some((c, t)) =>
          rwPc.trace = rwPc.trace ++ t
          c
        case _ => fromCoreClaim
      }
      if (logika.config.rwEvalTrace) {
        rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Done(fromCoreClaim, rwClaim)
      }
    } else {
      var done = F
      var i = 0
      while (!done && i < logika.config.rwMax && rwClaim != stepClaim) {
        rwPc.done = F
        if (logika.config.rwTrace) {
          rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Begin("rewriting", rwClaim)
        }
        rwClaim = rwPc.transformCoreExpBase(rwClaim) match {
          case MSome(c) =>
            rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Done(rwClaim, c)
            c
          case _ =>
            done = T
            rwClaim
        }
        i = i + 1
      }
    }
    if (rwClaim == stepClaim) {
      reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Matched:
            |  ${stepClaim.prettyST}
            |
            |After ${if (isEval) "evaluating" else "rewriting"} $from:
            |  ${fromCoreClaim.prettyST}
            |
            |${traceOpt(rwPc.trace)}""".render)
    } else if (rwClaim == stepClaimEv) {
      reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Matched:
            |  ${stepClaim.prettyST}
            |
            |After ${if (isEval) "evaluating" else "rewriting"} $from:
            |  ${fromCoreClaim.prettyST}
            |
            |$simplTraceOpt
            |
            |${traceOpt(rwPc.trace)}
            |
            |${traceOpt(simplTrace)}""".render)
    } else {
      reporter.error(step.just.id.attr.posOpt, Logika.kind,
        st"""Could not match:
            |  ${stepClaim.prettyST}
            |
            |After ${if (isEval) "evaluating" else "rewriting"} $from to:
            |  ${rwClaim.prettyST}
            |
            |$simplTraceOpt
            |
            |${traceOpt(rwPc.trace)}
            |
            |${traceOpt(simplTrace)}""".render)
      return emptyResult
    }
    val q = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
    val (stat, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
    return Plugin.Result(stat, nextFresh, claims)
  }
}
