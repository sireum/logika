// #Sireum
/*
 Copyright (c) 2017-2024, Robby, Kansas State University
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
import org.sireum.lang.tipe.TypeChecker
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}


@datatype class LiftPlugin extends JustificationPlugin {

  val name: String = "LiftPlugin"

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  @pure def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case AST.ProofAst.Step.Justification.Apply(invoke, false, ISZ()) =>
        val lresOpt: Option[AST.ResolvedInfo] = invoke.ident.attr.resOpt
        lresOpt match {
          case Some(lres: AST.ResolvedInfo.Method) if lres.id == "Lift" && lres.owner == justificationName =>
            invoke.args match {
              case ISZ(invoke2: AST.Exp.Invoke) =>
                invoke2.ident.attr.resOpt match {
                  case Some(res: AST.ResolvedInfo.Method) =>
                    return logika.th.nameMap.get(res.owner :+ res.id).get.isInstanceOf[Info.Method]
                  case _ =>
                }
              case _ =>
            }
          case _ =>
        }
      case _ =>
    }
    return F
  }

  def handle(logika: Logika,
             smt2: Smt2,
             cache: Logika.Cache,
             spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
             state: State,
             step: AST.ProofAst.Step.Regular,
             reporter: Reporter): State = {
    @strictpure def err: State = state(status = State.Status.Error)

    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val AST.ProofAst.Step.Justification.Apply(AST.Exp.Invoke(_, _, _, ISZ(invoke: AST.Exp.Invoke)), _, _) = just
    val res = invoke.ident.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    val args = invoke.args
    val posOpt = invoke.ident.attr.posOpt

    val mi = logika.th.nameMap.get(res.owner :+ res.id).get.asInstanceOf[Info.Method]
    val (reads, requires, modifies, ensures): (ISZ[AST.Exp.Ref], ISZ[AST.Exp], ISZ[AST.Exp.Ref], ISZ[AST.Exp]) = {
      mi.ast.contract match {
        case c: AST.MethodContract.Simple => (c.reads, c.requires, c.modifies, c.ensures)
        case _: AST.MethodContract.Cases =>
          reporter.error(posOpt, Logika.kind, "Could not use method with contract cases")
          return err
      }
    }
    if (reads.nonEmpty) {
      reporter.error(posOpt, Logika.kind, "Could not use method with non-empty reads clause")
      return err
    }
    if (modifies.nonEmpty) {
      reporter.error(posOpt, Logika.kind, "Could not use method with non-empty modifies clause")
      return err
    }

    val smOpt = TypeChecker.unifyFun(Logika.kind, logika.th, posOpt, TypeChecker.TypeRelation.Subtype, res.tpeOpt.get,
      mi.methodType.tpe, reporter)
    val ips = org.sireum.logika.Util.Substitutor(smOpt.get, mi.name,
      HashSMap.empty[String, AST.Exp] ++ ops.ISZOps(res.paramNames).zip(args), reporter.empty)

    var provenClaims = HashMap.empty[AST.Exp, (AST.ProofAst.StepId, AST.Exp)]
    for (spc <- spcMap.values) {
      spc match {
        case spc: StepProofContext.Regular => provenClaims = provenClaims + logika.th.normalizeExp(spc.exp) ~> ((spc.stepNo, spc.exp))
        case _ =>
      }
    }

    def conjunct(exps: ISZ[AST.Exp]): AST.Exp = {
      if (exps.isEmpty) {
        return AST.Exp.LitB(T, AST.Attr(posOpt))
      }
      var r = ips.transformExp(exps(0)).getOrElseEager(exps(0))
      for (i <- 1 until exps.size) {
        r = AST.Exp.Binary(r, AST.Exp.BinaryOp.CondAnd, ips.transformExp(exps(1)).getOrElseEager(exps(1)), AST.ResolvedAttr(
          exps(i).posOpt, Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd)), AST.Typed.bOpt),
          exps(i).posOpt)
      }
      return r
    }

    val iclaim: AST.Exp = if (requires.nonEmpty) {
      AST.Exp.Binary(conjunct(requires), AST.Exp.BinaryOp.CondImply, conjunct(ensures), AST.ResolvedAttr(
        ensures(ensures.size - 1).posOpt, Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply)),
        AST.Typed.bOpt), ensures(ensures.size - 1).posOpt
      )
    } else {
      conjunct(ensures)
    }

    if (ips.reporter.messages.nonEmpty) {
      reporter.reports(ips.reporter.messages)
      return err
    }

    if (logika.th.normalizeExp(step.claim) != logika.th.normalizeExp(iclaim)) {
      reporter.error(posOpt, Logika.kind, s"Could not lift ${mi.methodRes.id} to produce the stated claim")
      return err
    }

    val s0 = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
    if (s0.ok && logika.config.detailedInfo) {
      val ipsSubst: ST = st"[${(for (pair <- ips.paramMap.entries) yield st"${pair._2.prettyST} / ${pair._1}", ", ")}]"
      reporter.inform(step.claim.posOpt.get, Logika.Reporter.Info.Kind.Verified,
        st"""Accepted by contract lifting because:
            |
            |= Lift($invoke)$ipsSubst
            |
            |= $iclaim
            |
            |≈ ${step.claim}
            |""".render)
    }

    return s0
  }
}
