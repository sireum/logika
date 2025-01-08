// #Sireum
/*
 Copyright (c) 2017-2025, Robby, Kansas State University
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
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.{Logika, Smt2, Smt2Query, State, StepProofContext}
import org.sireum.message.Position

@datatype class SameDiffPlugin extends JustificationPlugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "SameDiffPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply if just.witnesses.isEmpty =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return res.id == "SameDiff" && res.owner == justificationName
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
                      reporter: Reporter): State = {
    @strictpure def err: State = state(status = State.Status.Error)

    val just = step.just
    val (id, posOpt, arg): (String, Option[Position], AST.ProofAst.StepId) = step.just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        val invokeId = just.invokeIdent.id.value
        val ao = AST.Util.toStepIds(just.args, Logika.kind, reporter).get
        (invokeId, just.invokeIdent.posOpt, ao(0))
      case _ => halt("Infeasible")
    }

    val fromStepId = arg
    val fromClaim: AST.Exp = spcMap.get(fromStepId) match {
      case Some(spc: StepProofContext.Regular) => spc.exp
      case Some(_) =>
        reporter.error(posOpt, Logika.kind, s"Cannot use compound proof step $fromStepId as an argument for $id")
        return err
      case _ =>
        reporter.error(posOpt, Logika.kind, s"Could not find proof step $fromStepId")
        return err
    }

    val tOpt = Plugin.commonLabeled(logika.th, posOpt, fromStepId, fromClaim, step.claim, reporter)
    if (tOpt.isEmpty) {
      return err
    }

    val Plugin.CommonLabeledResult(sortedNums, fromMap, toMap, labeled, aFromClaim, aToClaim) = tOpt.get

    val logika2 = logika(plugins = SameDiffExpPlugin(posOpt, id, fromStepId, fromMap, step.id) +: logika.plugins)

    val s0: State = if (!just.hasWitness) {
      logika2.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
    } else {
      val psmt2 = smt2.emptyCache(logika.config)
      val (suc, m) = state.unconstrainedClaims
      var s1 = suc
      var ok = T
      for (stepNo <- just.witnesses if ok) {
        spcMap.get(stepNo) match {
          case Some(spc: StepProofContext.Regular) =>
            val ISZ((s2, v)) = logika.evalExp(Logika.Split.Disabled, psmt2, cache, F, s1, spc.exp, reporter)
            val (s3, sym) = logika.value2Sym(s2, v, spc.exp.posOpt.get)
            s1 = s3.addClaim(State.Claim.Prop(T, sym))
          case Some(_) =>
            reporter.error(posOpt, Logika.kind, s"Cannot use compound proof step $stepNo as an argument for $id")
            ok = F
          case _ =>
            reporter.error(posOpt, Logika.kind, s"Could not find proof step $stepNo")
            ok = F
        }
      }
      if (!ok) {
        return err
      }
      val sClaims = state.claims.toMS
      for (p <- m) {
        val (i, j) = p
        sClaims(i) = s1.claims(j)
      }
      s1 = if (s1.ok) s1(claims = sClaims.toISZ[State.Claim] ++ ops.ISZOps(s1.claims).slice(suc.claims.size, s1.claims.size)) else err
      logika2.evalRegularStepClaim(psmt2, cache, s1, step.claim, step.id.posOpt, reporter)
    }
    if (s0.ok && logika.config.detailedInfo) {
      val eqSTs: ISZ[ST] = for (num <- sortedNums) yield
        st"""+ Labeled expression #$num:
            |
            |  ${fromMap.get(num).get}
            |  ≡
            |  ${toMap.get(num).get}"""
      val desc = st"$id (of ${(justificationName, ".")})"
      reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Accepted by using the $desc
            |proof tactic implemented in the $name, because:
            |
            |* The claims of proof steps $fromStepId and ${step.id} abstracted over matching
            |  $labeled are structurally equivalent, i.e.,
            |
            |  $aFromClaim
            |  ≡
            |  $aToClaim
            |
            |* Each of the matching labeled expressions are proven to be equivalent
            |  under their respective execution context (by SMT2 solving), i.e.,
            |
            |  ${(eqSTs, "\n\n")}
            |""".render)
    }

    return if (s0.ok) s0 else err
  }
}

@datatype class SameDiffExpPlugin(val posOpt: Option[Position],
                                  val id: String,
                                  val fromStepId: AST.ProofAst.StepId,
                                  val fromMap: HashSMap[Z, AST.Exp.Labeled],
                                  val stepId: AST.ProofAst.StepId) extends ExpPlugin {
  @strictpure override def name: String = "SameDiffExpPlugin"

  @strictpure override def canHandle(logika: Logika, exp: AST.Exp): B = exp.isInstanceOf[AST.Exp.Labeled]

  override def handle(logika: Logika, split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State,
                      exp: AST.Exp, reporter: Reporter): ISZ[(State, State.Value)] = {
    val lexp = exp.asInstanceOf[AST.Exp.Labeled]
    val num = AST.Util.labeledNumOf(lexp)
    val svs2 = logika.evalExp(split, smt2, cache, rtCheck, state, lexp.exp, reporter)
    val fromExp: AST.Exp.Labeled = fromMap.get(num) match {
      case Some(e) => e
      case _ => return svs2
    }

    val logika2 = logika(plugins = ops.ISZOps(logika.plugins).drop(1))

    var found = F
    var ok = T
    val pos = posOpt.get
    for (sv2 <- svs2 if sv2._1.ok) {
      val psmt2 = smt2
      for (sv1 <- logika2.evalExp(split, psmt2, cache, rtCheck, sv2._1, fromExp.exp, reporter) if sv1._1.ok) {
        val s3 = sv1._1
        val v1 = sv1._2
        val v2 = sv2._2
        val (_, sym) = s3.freshSym(AST.Typed.b, pos)
        val r = smt2.valid(logika.context.methodName, logika.config, cache, T,
          s"$id Justification for labeled expression #$num of proof steps $stepId and $fromStepId",
          pos, s3.claims :+ State.Claim.Let.Binary(sym, v1, AST.Exp.BinaryOp.Equiv, v2, v1.tipe),
          State.Claim.Prop(T, sym), reporter)
        r.kind match {
          case Smt2Query.Result.Kind.Unsat => found = T
          case Smt2Query.Result.Kind.Sat =>
            ok = F
            reporter.error(posOpt, Logika.kind, s"Invalid equivalence of labeled expression #$num of proof steps $stepId and $fromStepId")
          case Smt2Query.Result.Kind.Unknown =>
            ok = F
            reporter.error(posOpt, Logika.kind, s"Could not deduce the equivalence of labeled expression #$num of proof steps $stepId and $fromStepId")
          case Smt2Query.Result.Kind.Timeout =>
            ok = F
            reporter.error(posOpt, Logika.kind, s"Timed out when deducing the equivalence of labeled expression #$num of proof steps $stepId and $fromStepId")
          case Smt2Query.Result.Kind.Error =>
            ok = F
            reporter.error(posOpt, Logika.kind, s"Error occurred when deducing the equivalence of labeled expression #$num of proof steps $stepId and $fromStepId")
        }
      }
    }
    if (found && ok) {
      return svs2
    } else {
      if (!found) {
        reporter.error(posOpt, Logika.kind, s"Could not deduce the equivalence of any labeled expression proof steps $stepId and $fromStepId")
      }
      return for (sv2 <- svs2) yield (sv2._1(status = State.Status.Error), sv2._2)
    }
  }

}
