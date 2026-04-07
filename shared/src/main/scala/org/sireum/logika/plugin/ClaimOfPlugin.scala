// #Sireum
/*
 Copyright (c) 2017-2026,Robby, Kansas State University
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
import org.sireum.logika.{Config, Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

@datatype class ClaimOfPlugin extends JustificationPlugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "ClaimOfPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return res.id == "ClaimOf" && res.owner == justificationName
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
    @pure def isTheoremMethod(res: AST.ResolvedInfo.Method): B = {
      if (!res.isInObject) {
        return F
      }
      val fun = res.tpeOpt.get
      if (!fun.isPureFun) {
        return F
      }
      if (fun.ret != AST.Typed.unit) {
        return F
      }
      val m = logika.th.nameMap.get(res.owner :+ res.id).get.asInstanceOf[Info.Method]
      return m.ast.contract.modifies.isEmpty
    }
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val arg: AST.Exp = just.args(0) match {
      case a: AST.Exp.Eta => a.ref.asExp
      case a =>
        reporter.error(a.posOpt, Logika.kind, s"Expecting an eta expansion of a fact, theorem, or lemma")
        return err
    }
    val (name, targs): (ISZ[String], ISZ[AST.Typed]) = arg match {
      case arg: AST.Exp.Ident =>
        arg.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Fact => (res.name, ISZ())
          case res: AST.ResolvedInfo.Theorem => (res.name, ISZ())
          case res: AST.ResolvedInfo.Method if isTheoremMethod(res) => (res.owner :+ res.id, ISZ())
          case _ =>
            reporter.error(arg.posOpt, Logika.kind, s"Expecting a fact, theorem, or lemma")
            return err
        }
      case arg: AST.Exp.Select =>
        val tArgs: ISZ[AST.Typed] = for (t <- arg.targs) yield t.typedOpt.get
        arg.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Fact => (res.name, tArgs)
          case res: AST.ResolvedInfo.Theorem => (res.name, tArgs)
          case res: AST.ResolvedInfo.Method if isTheoremMethod(res) => (res.owner :+ res.id, tArgs)
          case _ =>
            reporter.error(arg.posOpt, Logika.kind, s"Expecting a fact, theorem, or lemma")
            return err
        }
      case arg =>
        reporter.error(arg.posOpt, Logika.kind, s"Expecting a name, but found $arg")
        return err
    }

    val (kind, typeParams, claims): (String, ISZ[AST.TypeParam], ISZ[AST.Exp]) = logika.th.nameMap.get(name).get match {
      case inf: Info.Fact => ("Fact", inf.ast.typeParams, inf.ast.claims)
      case inf: Info.Theorem => (if (inf.ast.isLemma) "Lemma" else "Theorem", inf.ast.typeParams, ISZ(inf.ast.claim))
      case inf: Info.Method =>
        val params: ISZ[AST.Exp.Fun.Param] = for (p <- inf.ast.sig.params) yield AST.Exp.Fun.Param(Some(p.id), Some(p.tipe), p.tipe.typedOpt)
        val funTypedAttr = AST.TypedAttr(inf.posOpt, Some(AST.Typed.Fun(AST.Purity.Pure, F,
          for (p <- inf.ast.sig.params) yield p.tipe.typedOpt.get, AST.Typed.b)))
        @pure def constructClaim(requires: ISZ[AST.Exp], ensures: ISZ[AST.Exp]): AST.Exp = {
          val body = AST.Util.bigImply(T, ISZ(AST.Util.bigAndCond(T, requires, inf.posOpt), AST.Util.bigAndCond(T, ensures, inf.posOpt)), inf.posOpt)
          val fun = AST.Exp.Fun(inf.owner :+ inf.ast.sig.id.value, params, AST.Stmt.Expr(body, ISZ(), AST.TypedAttr(inf.posOpt, AST.Typed.bOpt)), ISZ(), funTypedAttr)
          return AST.Exp.QuantType(T, fun, AST.Attr(inf.posOpt))
        }
        var claims = ISZ[AST.Exp]()
        inf.ast.contract match {
          case contract: AST.MethodContract.Simple => claims = claims :+ constructClaim(contract.requires, contract.ensures)
          case contract: AST.MethodContract.Cases =>
            for (c <- contract.cases) {
              claims = claims :+ constructClaim(c.requires, c.ensures)
            }
        }
        ("Method", inf.ast.sig.typeParams, claims)
      case _ => halt("Infeasible")
    }
    val sm = lang.tipe.TypeChecker.buildTypeSubstMap(name, arg.posOpt, typeParams, targs, reporter).get
    val stepClaim = logika.th.normalizeExp(step.claim)
    for (claim <- claims) {
      val normClaim = logika.th.normalizeExp(claim)
      val substNormClaim = AST.Util.substExpSkipResolvedInfo(normClaim, sm)
      if (stepClaim == substNormClaim) {
        val claimPos = claim.posOpt.get
        val s0 = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
        if (s0.ok && logika.config.detailedInfo) {
          reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
            st"""Accepted by using $kind ${(name, ".")}'s claim at [${claimPos.beginLine}, ${claimPos.beginColumn}], i.e.:
                |
                |$claim
                |""".render)
        }
        return s0
      }
    }

    reporter.error(step.claim.posOpt, Logika.kind, st"Could not find the stated claim in $kind ${(name, ".")}".render)
    return err
  }

}
