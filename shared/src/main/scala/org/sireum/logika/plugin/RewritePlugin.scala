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
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val isEval = just.id.value == "Eval"
    val patterns: ISZ[Rewriter.Pattern] =
      if (isEval) ISZ()
      else RewritingSystem.retrievePatterns(logika.th, cache, just.args(0))
    val from: AST.ProofAst.StepId =
      AST.Util.toStepIds(ISZ(just.args(if (isEval) 0 else 1)), Logika.kind, reporter) match {
        case Some(s) => s(0)
        case _ => return emptyResult
      }
    val fromClaim: AST.Exp = spcMap.get(from) match {
      case Some(spc: StepProofContext.Regular) => spc.exp
      case _ =>
        reporter.error(from.posOpt, Logika.kind, s"Expecting a regular proof step")
        return emptyResult
    }
    var provenClaims = HashSMap.empty[AST.ProofAst.StepId, AST.CoreExp.Base]
    if (just.hasWitness) {
      for (w <- just.witnesses) {
        spcMap.get(w) match {
          case Some(spc: StepProofContext.Regular) =>
            provenClaims = provenClaims + w ~> spc.coreExpClaim
          case _ =>
            reporter.error(from.posOpt, Logika.kind, s"Expecting a regular proof step for $w")
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
    val rwPc = Rewriter(if (logika.config.rwPar) logika.config.parCores else 1,
      logika.th, provenClaims, patterns, logika.config.rwTrace, F, ISZ())
    val fromCoreClaim = RewritingSystem.translate(logika.th, F, fromClaim)
    var rwClaim = fromCoreClaim
    val stepClaim = RewritingSystem.translate(logika.th, F, step.claim)
    if (isEval) {
      if (logika.config.rwTrace) {
        rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Begin("evaluating", rwClaim)
      }
      rwClaim = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all,
        rwPc.provenClaimStepIdMap, rwClaim, logika.config.rwTrace) match {
        case Some((e, t)) =>
          rwPc.trace = t :+ RewritingSystem.Trace.Done(rwClaim, e)
          e
        case _ => rwClaim
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
    val traceOpt: Option[ST] = if (logika.config.rwTrace) {
      Some(
        st"""Trace:
            |
            |${(for (te <- rwPc.trace) yield te.toST, "\n\n")}""")
    } else {
      None()
    }
    if (rwClaim == stepClaim) {
      reporter.inform(just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Matched:
            |  ${stepClaim.prettyST}
            |
            |After ${if (isEval) "evaluating" else "rewriting"} $from:
            |  ${fromCoreClaim.prettyST}
            |
            |$traceOpt""".render)
      val q = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
      val (stat, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
      return Plugin.Result(stat, nextFresh, claims)
    } else {
      reporter.error(just.id.attr.posOpt, Logika.kind,
        st"""Could not match:
            |  ${stepClaim.prettyST}
            |
            |After ${if (isEval) "evaluating" else "rewriting"} $from to:
            |  ${rwClaim.prettyST}
            |
            |$traceOpt""".render)
      return emptyResult
    }
  }
}
