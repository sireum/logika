// #Sireum
/*
 Copyright (c) 2021, Robby, Kansas State University
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
import org.sireum.lang.ast.{Exp, MTransformer}
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}

object PredNatDedPlugin {

  @record class LocalSubstitutor(map: HashMap[(ISZ[String], String), AST.Exp]) extends AST.MTransformer {
    override def preExpIdent(o: Exp.Ident): MTransformer.PreResult[Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.LocalVar =>
          map.get((res.context, res.id)) match {
            case Some(exp) => return MTransformer.PreResult(F, MSome(exp))
            case _ =>
          }
        case _ =>
      }
      return super.preExpIdent(o)
    }
  }
}

@datatype class PredNatDedPlugin extends Plugin {

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("AllI", "ExistsE")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification", "natded", "pred")

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Incept =>
        val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
        return justificationIds.contains(res.id) && res.owner == justificationName
      case _ => return F
    }
  }

  override def handle(logika: Logika,
                      smt2: Smt2,
                      log: B,
                      logDirOpt: Option[String],
                      spcMap: HashSMap[Z, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, state.claims)
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Incept]
    val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    res.id match {
      case string"AllI" =>
        val quant: AST.Exp.QuantType = step.claim match {
          case stepClaim@AST.Exp.QuantType(_, AST.Exp.Fun(_, _, _: AST.Stmt.Expr)) if stepClaim.isForall =>
            AST.Util.normalizeQuantType(stepClaim).asInstanceOf[AST.Exp.QuantType]
          case _ =>
            reporter.error(step.claim.posOpt, Logika.kind, "Expecting a simple universal quantified type claim")
            return emptyResult
        }
        val ISZ(subProofNo: AST.Exp.LitZ) = just.args
        val (params, subProof): (ISZ[AST.ProofAst.Step.Let.Param], HashSet[AST.Exp]) = spcMap.get(subProofNo.value) match {
          case Some(sp@StepProofContext.FreshSubProof(_, ps, _)) => (ps, HashSet ++ sp.claims)
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a parameterized let sub-proof step")
            return emptyResult
        }
        val size = params.size
        if (quant.fun.params.size < params.size) {
          reporter.error(step.no.posOpt, Logika.kind, s"Expecting at most ${quant.fun.params.size} fresh variables in sub-proof #${subProofNo.value}, but found ${params.size}")
          return emptyResult
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
                  funArg.tipeOpt.get.typedOpt,
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
        if (!subProof.contains(AST.Util.deBruijn(substClaim))) {
          reporter.error(step.claim.posOpt, Logika.kind, s"Could not infer the stated claim using ${just.invokeIdent.id.value}")
          return emptyResult
        }
      case string"ExistsE" =>
        val ISZ(existsP: AST.Exp.LitZ, subProofNo: AST.Exp.LitZ) = just.args
        val quant: AST.Exp.QuantType = spcMap.get(existsP.value) match {
          case Some(StepProofContext.Regular(_, q@AST.Exp.QuantType(F, AST.Exp.Fun(_, _, _: AST.Stmt.Expr)), _)) => q
          case _ =>
            reporter.error(existsP.posOpt, Logika.kind, "Expecting a simple existential quantified type claim")
            return emptyResult
        }
        val (params, assumption, subProof): (ISZ[AST.ProofAst.Step.Let.Param], AST.Exp, HashSet[AST.Exp]) = spcMap.get(subProofNo.value) match {
          case Some(sp@StepProofContext.FreshAssumeSubProof(_, ps, ac, _)) => (ps, ac, HashSet ++ sp.claims)
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a parameterized let sub-proof assume step")
            return emptyResult
        }
        val size = params.size
        if (quant.fun.params.size < params.size) {
          reporter.error(step.no.posOpt, Logika.kind, s"Expecting at most ${quant.fun.params.size} fresh variables in sub-proof #${subProofNo.value}, but found ${params.size}")
          return emptyResult
        }
        var substMap = HashMap.empty[(ISZ[String], String), AST.Exp]
        for (p <- ops.ISZOps(ops.ISZOps(quant.fun.params).slice(0, size)).zip(ops.ISZOps(params).slice(0, size))) {
          val (funParam, funArg) = p
          funParam.idOpt match {
            case Some(id) =>
              substMap = substMap + ((quant.fun.context, id.value)) ~> AST.Exp.Ident(
                funArg.id,
                AST.ResolvedAttr(
                  funArg.id.attr.posOpt,
                  Some(AST.ResolvedInfo.LocalVar(logika.context.methodName, AST.ResolvedInfo.LocalVar.Scope.Closure, T,
                    T, funArg.id.value)),
                  funArg.tipeOpt.get.typedOpt,
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
        if (AST.Util.deBruijn(substClaim) != assumption) {
          reporter.error(step.claim.posOpt, Logika.kind, s"Could not match the assumption in let sub-proof #${subProofNo.value}")
          return emptyResult
        }
        val stepClaim = step.claimDeBruijn
        if (!subProof.contains(stepClaim) && stepClaim != assumption) {
          reporter.error(step.claim.posOpt, Logika.kind, s"Could not find the stated claim in let sub-proof #${subProofNo.value}")
          return emptyResult
        }
    }
    val (status, nextFresh, claims, claim) = logika.evalRegularStepClaim(smt2, state, step.claim, step.no.posOpt, reporter)
    return Plugin.Result(status, nextFresh, claims :+ claim)
  }
}