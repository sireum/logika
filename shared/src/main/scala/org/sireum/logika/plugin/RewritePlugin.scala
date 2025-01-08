// #Sireum
/*
 Copyright (c) 2017-2025, Ryan Peroutka, Galois, Inc.
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
import org.sireum.logika.RewritingSystem.{BacktrackingSchedule, Rewriter, toCondEquiv}
import org.sireum.logika.{Logika, RewritingSystem, Smt2, State, StepProofContext}

@datatype class RewritePlugin extends JustificationPlugin {

  val name: String = "RewritePlugin"

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Ref =>
        return (just.id.value == "Simpl" || just.id.value == "ESimpl") && just.isOwnedBy(justificationName)
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invoke.ident.attr.resOpt match {
          case Some(res: AST.ResolvedInfo.Method) if (res.id == "Rewrite" || res.id == "RSimpl" || res.id == "Eval") && res.owner == justificationName => return T
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
                      step: AST.ProofAst.Step.Regular, reporter: Logika.Reporter): State = {
    @strictpure def err: State = state(status = State.Status.Error)
    @strictpure def justArgs: ISZ[AST.Exp] = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply].args
    val isESimpl = step.just.id.value == "ESimpl"
    val isSimpl = isESimpl | step.just.id.value == "Simpl"
    val isEval = step.just.id.value == "Eval"
    val isRSimpl = step.just.id.value == "RSimpl"
    val (patterns, methodPatterns): (ISZ[Rewriter.Pattern.Claim], HashSMap[(ISZ[String], B), Rewriter.Pattern.Method]) =
      if (isEval || isSimpl) {
        (ISZ(), HashSMap.empty)
      } else {
        var r1 = ISZ[Rewriter.Pattern.Claim]()
        var r2 = HashSMap.empty[(ISZ[String], B), Rewriter.Pattern.Method]
        val (currIsInObject, currMethodName): (B, ISZ[String]) = logika.context.methodOpt match {
          case Some(m) => (m.receiverTypeOpt.isEmpty, m.name)
          case _ => (F, ISZ())
        }
        for (p <- RewritingSystem.retrievePatterns(logika.th, cache, justArgs(0), HashSet.empty)) {
          if (p.isInObject == currIsInObject && (p.name == currMethodName :+ "contract" || p.name == currMethodName)) {
            val n: Z = if (p.name(p.name.size - 1)  == "contract") 2 else 1
            reporter.error(step.just.id.attr.posOpt, Logika.kind, s"Cannot use ${p.name(p.name.size - n)} as a rewrite in itself")
            return err
          }
          p match {
            case p: Rewriter.Pattern.Claim =>
              r1 = r1 :+ p
            case p: Rewriter.Pattern.Method =>
              if (p.isAbs) {
                r2 = r2 + (p.owner :+ p.id, p.isInObject) ~> p
              } else {
                reporter.warn(justArgs(0).posOpt, Logika.kind,
                  st"Method ${(p.owner, ".")}${if (p.isInObject) "." else "#"}${p.id} is not @abs".render)
              }
          }
        }
        (r1, r2)
      }
    val stepClaim = logika.th.translateToBaseCoreExp(step.claim, F)
    val (fromOpt, fromCoreClaim): (Option[AST.ProofAst.StepId], AST.CoreExp.Base) = {
      if (isSimpl) {
        (None(), AST.CoreExp.True)
      } else if (isRSimpl) {
        (None(), stepClaim)
      } else {
        val from: AST.ProofAst.StepId =
          AST.Util.toStepIds(ISZ(justArgs(if (isEval) 0 else 1)), Logika.kind, reporter) match {
            case Some(s) => s(0)
            case _ => return err
          }
        spcMap.get(from) match {
          case Some(spc: StepProofContext.Regular) => (Some(from), spc.coreExpClaim)
          case _ =>
            reporter.error(from.posOpt, Logika.kind, s"Expecting a regular proof step")
            return err
        }
      }
    }
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

    val rwPc = Rewriter(if (logika.config.rwPar) logika.config.parCores else 1, logika.th,
      provenClaims, patterns, methodPatterns,
      if (fromOpt.isEmpty) None() else Some(fromOpt.get),
      logika.config.rwTrace, logika.config.rwEvalTrace, logika.config.rwMax, F, F, F, ISZ())
    if (logika.config.rwEvalTrace) {
      rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Begin("simplifying", stepClaim)
    }

    val schedule = BacktrackingSchedule.empty(isESimpl)

    var stepClaimEv: AST.CoreExp.Base = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all, cache,
      rwPc.methodPatterns, MBox(HashSMap.empty), logika.config.rwMax, rwPc.provenClaimStepIdMapEval, stepClaim, T,
      logika.config.rwEvalTrace, schedule) match {
      case Some((e, t)) =>
        rwPc.trace = t
        e
      case _ => stepClaim
    }

    while (stepClaimEv != AST.CoreExp.True && !schedule.done) {
      schedule.index = 0
      stepClaimEv = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all, cache,
        rwPc.methodPatterns, MBox(HashSMap.empty), logika.config.rwMax, rwPc.provenClaimStepIdMapEval, stepClaim, T,
        logika.config.rwEvalTrace, schedule) match {
        case Some((e, t)) =>
          rwPc.trace = t
          e
        case _ => stepClaim
      }
    }

    if (logika.config.rwEvalTrace) {
      rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Done(stepClaim, stepClaimEv)
    }

    if (stepClaimEv == AST.CoreExp.True) {
      if (logika.config.detailedInfo) {
        reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
          st"""Evaluating ${stepClaim.prettyST} produces T, hence the claim holds
              |
              |${traceOpt(rwPc.trace)}""".render)
      }
      if (isSimpl) {
        return logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
      } else if (rwPc.methodPatterns.isEmpty) {
        reporter.warn(step.just.id.attr.posOpt, Logika.kind, "The claim can be discharged by using Simpl instead")
      } else if (rwPc.methodPatterns.nonEmpty && !isRSimpl) {
        reporter.warn(step.just.id.attr.posOpt, Logika.kind, "The claim can be discharged by using RSimpl instead")
      }
    } else if (isSimpl) {
      reporter.error(step.just.id.attr.posOpt, Logika.kind, st"Could not simplify ${stepClaim.prettyST} to T".render)
      reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Error,
        st"""Could not simplify ${stepClaim.prettyST} to T
            |
            |After simplification:
            |  ${stepClaimEv.prettyST}
            |
            |${traceOpt(rwPc.trace)}""".render)
      return err
    } else {
      val simplTrace = rwPc.trace
      rwPc.trace = ISZ()
      @strictpure def simplTraceOpt: Option[ST] = if (stepClaim == stepClaimEv) None() else Some(
        st"""and/or after simplifying the step claim to:
            |  ${stepClaimEv.prettyST}"""
      )

      var rwClaim = fromCoreClaim
      if (isEval) {
        if (logika.config.rwEvalTrace) {
          rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Begin("evaluating", fromCoreClaim)
        }
        rwClaim = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all, cache, rwPc.methodPatterns,
          MBox(HashSMap.empty), logika.config.rwMax, rwPc.provenClaimStepIdMapEval, rwClaim, T, logika.config.rwEvalTrace,
          BacktrackingSchedule.empty(F)) match {
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
        val ld = RewritingSystem.LabeledDetector(F)
        ld.transformCoreExpBase(rwClaim)
        rwPc.labeledOnly = ld.found
        var changed = F
        def continu: B = {
          return if (isRSimpl) rwClaim != AST.CoreExp.True else rwClaim != stepClaim
        }
        while (!done && i < logika.config.rwMax && continu) {
          rwPc.done = F
          if (logika.config.rwTrace) {
            rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Begin("rewriting", rwClaim)
          }
          rwClaim = rwPc.transformCoreExpBase(cache, rwClaim) match {
            case Some(c) =>
              rwPc.trace = rwPc.trace :+ RewritingSystem.Trace.Done(rwClaim, c)
              changed = T
              c
            case _ =>
              done = T
              rwClaim
          }
          if (continu && !rwPc.labeledOnly) {
            rwClaim = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all, cache, rwPc.methodPatterns,
              MBox(HashSMap.empty), 0, rwPc.provenClaimStepIdMapEval, rwClaim, T, T, BacktrackingSchedule.empty(F)) match {
              case Some((r, t)) =>
                rwPc.trace = rwPc.trace ++ t
                r
              case _ => rwClaim
            }
          }
          i = i + 1
        }
        if (continu && !rwPc.labeledOnly) {
          rwClaim = RewritingSystem.evalBase(logika.th, RewritingSystem.EvalConfig.all, cache, rwPc.methodPatterns,
            MBox(HashSMap.empty), logika.config.rwMax, rwPc.provenClaimStepIdMapEval, rwClaim, T, T,
            BacktrackingSchedule.empty(F)) match {
            case Some((r, t)) =>
              rwPc.trace = rwPc.trace ++ t
              r
            case _ => rwClaim
          }
        }
        rwClaim = RewritingSystem.LabeledRemover().transformCoreExpBase(rwClaim).getOrElse(rwClaim)
      }
      @strictpure def fromCoreClaimST: Option[ST] = if (fromOpt.isEmpty) None() else Some(
        st"""After ${if (isEval) "evaluating" else "rewriting"}${if (fromOpt.isEmpty) st"" else st" ${fromOpt.get}"}:
            |  ${fromCoreClaim.prettyST}
            |"""
      )
      if (isRSimpl) {
        if (rwClaim == AST.CoreExp.True) {
          if (logika.config.detailedInfo) {
            reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
              st"""Rewriting ${stepClaim.prettyST} produces T, hence the claim holds
                  |
                  |${traceOpt(rwPc.trace)}""".render)
          }
        } else {
          reporter.error(step.just.id.attr.posOpt, Logika.kind, st"Could not rewrite ${stepClaim.prettyST} to T".render)
          reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Error,
            st"""Could not rewrite ${stepClaim.prettyST} to T
                |
                |After rewriting:
                |  ${rwClaim.prettyST}
                |
                |${traceOpt(rwPc.trace)}""".render)
        }
      } else {
        if (rwClaim == stepClaim) {
          if (logika.config.detailedInfo) {
            reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
              st"""Matched:
                  |  ${stepClaim.prettyST}
                  |
                  |$fromCoreClaimST
                  |${traceOpt(rwPc.trace)}""".render)
          }
        } else if (rwClaim == stepClaimEv) {
          if (logika.config.detailedInfo) {
            reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
              st"""Matched:
                  |  ${stepClaim.prettyST}
                  |
                  |$fromCoreClaimST
                  |$simplTraceOpt
                  |
                  |${traceOpt(rwPc.trace)}
                  |
                  |${traceOpt(simplTrace)}""".render)
          }
        } else {
          reporter.error(step.just.id.attr.posOpt, Logika.kind,
            st"""Could not match:
                |  ${stepClaim.prettyST}""".render)
          reporter.inform(step.just.id.attr.posOpt.get, Reporter.Info.Kind.Error,
            st"""Could not match:
                |  ${stepClaim.prettyST}
                |
                |After attempting to ${if (isEval) "evaluate" else "rewrite"}$fromOpt to:
                |  ${rwClaim.prettyST}
                |
                |$simplTraceOpt
                |
                |${if (fromCoreClaim == AST.CoreExp.True) None[ST]() else traceOpt(rwPc.trace)}
                |
                |${traceOpt(simplTrace)}""".render)
          return err
        }
      }
    }
    return logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
  }
}
