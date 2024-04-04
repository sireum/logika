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
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}

object PredNatDedPlugin {

  @record class LocalSubstitutor(val map: HashMap[(ISZ[String], String), AST.Exp]) extends AST.MTransformer {
    override def preExpIdent(o: AST.Exp.Ident): AST.MTransformer.PreResult[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.LocalVar =>
          map.get((res.context, res.id)) match {
            case Some(exp) => return AST.MTransformer.PreResult(F, MSome(exp))
            case _ =>
          }
        case _ =>
      }
      return AST.MTransformer.PreResultExpIdent
    }
  }
}

@datatype class PredNatDedPlugin extends JustificationPlugin {

  val name: String = "PredNatDedPlugin"

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("AllI", "ExistsE")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification", "natded", "pred")

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply if !just.hasWitness =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return justificationIds.contains(res.id) && res.owner == justificationName
          case _ => return F
        }
      case _ => return F
    }
  }

  override def checkMode(logika: Logika, just: AST.ProofAst.Step.Justification, reporter: Reporter): B = {
    return T
  }

  override def handle(logika: Logika,
                      smt2: Smt2,
                      cache: Logika.Cache,
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): State = {
    @strictpure def err: State = state(status = State.Status.Error)
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    var acceptedMsg = st"""Accepted by using the ${res.id}, because"""
    res.id match {
      case string"AllI" =>
        val quant: AST.Exp.QuantType = step.claim match {
          case stepClaim@AST.Exp.QuantType(T, AST.Exp.Fun(_, _, _: AST.Stmt.Expr)) =>
            logika.th.normalizeQuantType(stepClaim).asInstanceOf[AST.Exp.QuantType]
          case stepClaim@AST.Exp.QuantRange(T, _, _, _, AST.Exp.Fun(_, _, _: AST.Stmt.Expr)) =>
            logika.th.normalizeQuantType(stepClaim).asInstanceOf[AST.Exp.QuantType]
          case _ =>
            reporter.error(step.claim.posOpt, Logika.kind, "Expecting a simple universal quantified type/range claim")
            return err
        }
        val argsOpt = AST.Util.toStepIds(just.args, Logika.kind, reporter)
        if (argsOpt.isEmpty) {
          return err
        }
        if (quant.fun.params(0).typedOpt != just.invoke.targs(0).typedOpt) {
          reporter.error(just.invoke.targs(0).posOpt, Logika.kind, s"Expecting type '${quant.fun.params(0).typedOpt.get}', but '${just.invoke.targs(0).typedOpt.get}' found")
          return err
        }
        val ISZ(subProofNo) = argsOpt.get
        val (params, subProof): (ISZ[AST.ProofAst.Step.Let.Param], HashSet[AST.Exp]) = spcMap.get(subProofNo) match {
          case Some(sp@StepProofContext.FreshSubProof(_, ps, _)) => (ps, HashSet ++ sp.claims)
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a parameterized let sub-proof step")
            return err
        }
        val size = params.size
        if (quant.fun.params.size < params.size) {
          reporter.error(step.id.posOpt, Logika.kind, s"Expecting at most ${quant.fun.params.size} fresh variables in sub-proof $subProofNo, but found ${params.size}")
          return err
        }
        var substMap = HashMap.empty[(ISZ[String], String), AST.Exp]
        for (p <- ops.ISZOps(ops.ISZOps(quant.fun.params).slice(0, size)).zip(ops.ISZOps(params).slice(0, size))) {
          val (funParam, funArg) = p
          funParam.idOpt match {
            case Some(id) =>
              substMap = substMap + (quant.fun.context, id.value) ~> AST.Exp.Ident(
                funArg.id,
                AST.ResolvedAttr(
                  funArg.id.attr.posOpt,
                  Some(AST.ResolvedInfo.LocalVar(logika.context.methodName, AST.ResolvedInfo.LocalVar.Scope.Closure, T,
                    T, funArg.id.value)),
                  funArg.tipeOpt.get.typedOpt
                )
              )
            case _ =>
          }
        }
        var quantClaim = quant.fun.exp.asInstanceOf[AST.Stmt.Expr].exp
        if (quant.fun.params.size > size) {
          quantClaim = quant(fun = quant.fun(
            params = ops.ISZOps(quant.fun.params).drop(size),
            exp = AST.Stmt.Expr(quantClaim, AST.TypedAttr(quantClaim.posOpt, quantClaim.typedOpt))))
        }
        val substClaim = PredNatDedPlugin.LocalSubstitutor(substMap).transformExp(quantClaim).getOrElse(quantClaim)
        val substClaimNorm = logika.th.normalizeExp(substClaim)
        if (subProof.contains(substClaimNorm)) {
          acceptedMsg =
            st"""$acceptedMsg sub-proof $subProofNo:
                |
                |* starts with assuming a fresh value of type ${quant.fun.params(0).typedOpt.get}
                |
                |* proves that the instantiation of ${step.claim}'s universally quantified claim
                |  using the fresh value holds, i.e., ${substClaim.prettyST}
                |"""
        } else {
          reporter.error(step.claim.posOpt, Logika.kind, s"Could not infer the stated claim using ${just.invokeIdent.id.value}")
          return err
        }
      case string"ExistsE" =>
        val argsOpt = AST.Util.toStepIds(just.args, Logika.kind, reporter)
        if (argsOpt.isEmpty) {
          return err
        }
        val ISZ(existsP, subProofNo) = argsOpt.get
        val quant: AST.Exp.QuantType = spcMap.get(existsP) match {
          case Some(StepProofContext.Regular(_, _, q@AST.Exp.QuantType(F, AST.Exp.Fun(_, _, _: AST.Stmt.Expr)))) =>
            logika.th.normalizeQuantType(q).asInstanceOf[AST.Exp.QuantType]
          case Some(StepProofContext.Regular(_, _, q@AST.Exp.QuantRange(F, _, _, _, AST.Exp.Fun(_, _, _: AST.Stmt.Expr)))) =>
            logika.th.normalizeQuantType(q).asInstanceOf[AST.Exp.QuantType]
          case _ =>
            reporter.error(existsP.posOpt, Logika.kind, "Expecting a simple existential quantified type/range claim")
            return err
        }
        if (quant.fun.params(0).typedOpt != just.invoke.targs(0).typedOpt) {
          reporter.error(just.invoke.targs(0).posOpt, Logika.kind, s"Expecting type '${quant.fun.params(0).typedOpt.get}', but '${just.invoke.targs(0).typedOpt.get}' found")
          return err
        }
        val (params, assumption, subProof): (ISZ[AST.ProofAst.Step.Let.Param], AST.Exp, HashSet[AST.Exp]) = spcMap.get(subProofNo) match {
          case Some(sp@StepProofContext.FreshAssumeSubProof(_, ps, ac, _)) => (ps, ac, HashSet ++ sp.claims)
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a parameterized let sub-proof assume step")
            return err
        }
        val size = params.size
        if (quant.fun.params.size < params.size) {
          reporter.error(step.id.posOpt, Logika.kind, s"Expecting at most ${quant.fun.params.size} fresh variables in sub-proof $subProofNo, but found ${params.size}")
          return err
        }
        var substMap = HashMap.empty[(ISZ[String], String), AST.Exp]
        for (p <- ops.ISZOps(ops.ISZOps(quant.fun.params).slice(0, size)).zip(ops.ISZOps(params).slice(0, size))) {
          val (funParam, funArg) = p
          funParam.idOpt match {
            case Some(id) =>
              substMap = substMap + (quant.fun.context, id.value) ~> AST.Exp.Ident(
                funArg.id,
                AST.ResolvedAttr(
                  funArg.id.attr.posOpt,
                  Some(AST.ResolvedInfo.LocalVar(logika.context.methodName, AST.ResolvedInfo.LocalVar.Scope.Closure, T,
                    T, funArg.id.value)),
                  funArg.tipeOpt.get.typedOpt
                )
              )
            case _ =>
          }
        }
        var quantClaim = quant.fun.exp.asInstanceOf[AST.Stmt.Expr].exp
        if (quant.fun.params.size > size) {
          quantClaim = quant.fun(
            params = ops.ISZOps(quant.fun.params).drop(size),
            exp = AST.Stmt.Expr(quantClaim, AST.TypedAttr(quantClaim.posOpt, quantClaim.typedOpt)))
        }
        val substClaim = PredNatDedPlugin.LocalSubstitutor(substMap).transformExp(quantClaim).getOrElse(quantClaim)
        if (logika.th.normalizeExp(substClaim) != assumption) {
          reporter.error(step.claim.posOpt, Logika.kind, s"Could not match the assumption in let sub-proof $subProofNo")
          return err
        }
        val stepClaim = logika.th.normalizeExp(step.claim)
        if (subProof.contains(stepClaim) && stepClaim != assumption) {
          acceptedMsg =
            st"""$acceptedMsg sub-proof $subProofNo:
                |
                |* starts with assuming a fresh value of type ${quant.fun.params(0).typedOpt.get} and
                |  $existsP's instantiated claim using the fresh value
                |
                |* proves ${step.claim}'s claim, i.e., $stepClaim
                |"""
        } else {
          reporter.error(step.claim.posOpt, Logika.kind, s"Could not find the stated claim in let sub-proof $subProofNo")
          return err
        }
    }
    val s0 = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
    if (s0.ok) {
      reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified, acceptedMsg.render)
    }
    return s0
  }
}