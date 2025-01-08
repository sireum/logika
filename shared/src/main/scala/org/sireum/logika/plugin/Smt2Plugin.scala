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
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, Smt2Config, Smt2Query, State, StepProofContext}

@datatype class Smt2Plugin extends JustificationPlugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "Smt2Plugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return res.id == "Smt2" && res.owner == justificationName
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
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val (options, timeout, resourceLimit): (AST.Exp.LitString, Z, Z) = just.args match {
      case ISZ(s: AST.Exp.LitString, t: AST.Exp.LitZ, r: AST.Exp.LitZ) => (s, t.value, r.value)
      case _ =>
        reporter.error(just.invoke.posOpt, Logika.kind, s"Expecting literals for SMT2 configuration, timeout (ms), and resource limit")
        return err
    }

    val smt2Configs: ISZ[Smt2Config] = Smt2.parseConfigs(logika.context.nameExePathMap, F, options.value) match {
      case Either.Left(cs) => cs
      case Either.Right(msg) =>
        reporter.error(options.posOpt, Logika.kind, msg)
        return err
    }

    val rlimit: Z = if (resourceLimit <= 0) 0 else resourceLimit
    val logikaSmt2 = logika(config = logika.config(timeoutInMs = if (timeout <= 0) 0 else timeout, rlimit = rlimit,
      smt2Configs = smt2Configs ++ (for (c <- logika.config.smt2Configs if c.isSat) yield c)))
    val posOpt = just.invokeIdent.posOpt

    @pure def computeProvenClaims(spcs: ISZ[StepProofContext]): HashSMap[AST.ProofAst.StepId, (B, AST.Exp)] = {
      var r = HashSMap.empty[AST.ProofAst.StepId, (B, AST.Exp)]
      for (spc <- spcs) {
        spc match {
          case spc: StepProofContext.Regular =>
            val claim = spc.exp
            r = r + spc.stepNo ~> (T, claim)
          case spc: StepProofContext.SubProof =>
            val claims: ISZ[AST.Exp] = for (p <- computeProvenClaims(spc.spcs).entries) yield p._2._2
            val claim = AST.Util.bigImply(T, ISZ(spc.assumption, AST.Util.bigAnd(claims, spc.stepNo.posOpt)), spc.stepNo.posOpt)
            r = r + spc.stepNo ~> (F, claim)
          case spc: StepProofContext.FreshSubProof =>
            val claims: ISZ[AST.Exp] = for (p <- computeProvenClaims(spc.spcs).entries) yield p._2._2
            val tattr = AST.TypedAttr(spc.stepNo.posOpt, AST.Typed.bOpt)
            var params = ISZ[AST.Exp.Fun.Param]()
            for (p <- spc.params) {
              params = params :+ AST.Exp.Fun.Param(Some(p.id), p.tipeOpt, p.tipeOpt.get.typedOpt)
            }
            val claim = AST.Exp.QuantType(T, AST.Exp.Fun(spc.context, params,
              AST.Stmt.Expr(AST.Util.bigAnd(claims, spc.stepNo.posOpt), tattr), tattr), AST.Attr(spc.stepNo.posOpt))
            r = r + spc.stepNo ~> (F, claim)
          case spc: StepProofContext.FreshAssumeSubProof =>
            val claims: ISZ[AST.Exp] = for (p <- computeProvenClaims(spc.spcs).entries) yield p._2._2
            val tattr = AST.TypedAttr(spc.stepNo.posOpt, AST.Typed.bOpt)
            var params = ISZ[AST.Exp.Fun.Param]()
            for (p <- spc.params) {
              params = params :+ AST.Exp.Fun.Param(Some(p.id), p.tipeOpt, p.tipeOpt.get.typedOpt)
            }
            val claim = AST.Exp.QuantType(F, AST.Exp.Fun(spc.context, params,
              AST.Stmt.Expr(AST.Util.bigImply(T, ISZ(spc.assumption, AST.Util.bigAnd(claims, spc.stepNo.posOpt)),
                spc.stepNo.posOpt), tattr), tattr), AST.Attr(spc.stepNo.posOpt))
            r = r + spc.stepNo ~> (F, claim)
        }
      }
      return r
    }

    val provenClaims = computeProvenClaims(spcMap.values)
    var _atMapInit = F
    var _atMap: org.sireum.logika.Util.ClaimsToExps.AtMap = HashMap.empty
    def atMap: org.sireum.logika.Util.ClaimsToExps.AtMap = {
      if (!_atMapInit) {
        _atMapInit = T
        _atMap = org.sireum.logika.Util.claimsToExps(logika.jescmPlugins._4, posOpt.get, logika.context.methodName,
          state.claims, logika.th, F, logika.config.atRewrite)._2
      }
      return _atMap
    }

    def checkValid(s6: State, conclusion: State.Value.Sym): State = {
      val prop = State.Claim.Prop(T, conclusion)
      val r = smt2.valid(logikaSmt2.context.methodName, logikaSmt2.config, cache, T,
        s"${just.invokeIdent.id.value} Justification", posOpt.get, s6.claims, prop, reporter)
      def error(msg: String): B = {
        reporter.error(posOpt, Logika.kind, msg)
        return F
      }

      val status: B = r.kind match {
        case Smt2Query.Result.Kind.Unsat => T
        case Smt2Query.Result.Kind.Sat => error(s"Invalid claim of proof step ${step.id}")
        case Smt2Query.Result.Kind.Unknown => error(s"Could not deduce the claim of proof step ${step.id}")
        case Smt2Query.Result.Kind.Timeout => error(s"Timed out when deducing the claim of proof step ${step.id}")
        case Smt2Query.Result.Kind.Error => error(s"Error occurred when deducing the claim of proof step ${step.id}")
      }
      val s7 = s6.addClaim(prop)
      return if (status) s7 else err
    }

    if (!just.hasWitness) {
      var s0 = state
      for (p <- provenClaims.entries) {
        if (p._2._1) {
          val (s1, exp) = logikaSmt2.rewriteAt(atMap, s0, p._2._2, reporter)
          s0 = logikaSmt2.evalAssume(smt2, cache, T, "", s1, exp, p._2._2.posOpt, reporter)._1
        }
      }
      val (s6, conclusion) = logikaSmt2.evalRegularStepClaimValue(smt2, cache, s0, step.claim, step.id.posOpt, reporter)
      if (s6.ok) {
        val s7 = checkValid(s6, conclusion)
        if (s7.ok) {
          return s7(claims = state.claims ++ ops.ISZOps(s7.claims).slice(s0.claims.size, s7.claims.size), nextFresh = s7.nextFresh)
        }
      }
      return err
    } else {
      val (suc, _) = state.unconstrainedClaims
      var s0 = suc
      var ok = T
      for (arg <- just.witnesses) {
        val stepNo = arg
        provenClaims.get(stepNo) match {
          case Some((_, spcExp)) =>
            val (s1, exp) = logikaSmt2.rewriteAt(atMap, s0, spcExp, reporter)
            s0 = logikaSmt2.evalAssume(smt2, cache, T, "", s1, exp, exp.posOpt, reporter)._1
          case _ =>
            reporter.error(posOpt, Logika.kind, s"Could not find proof step $stepNo")
            ok = F
        }
      }
      if (!ok) {
        return err
      }
      val (s4, exp) = logikaSmt2.rewriteAt(atMap, s0, step.claim, reporter)
      val (s6, conclusion) = logikaSmt2.evalRegularStepClaimValue(smt2, cache, s4, exp, step.id.posOpt, reporter)
      if (s6.ok) {
        val s7 = checkValid(s6, conclusion)
        if (s7.ok) {
          return s7(claims = state.claims ++ ops.ISZOps(s7.claims).slice(s0.claims.size, s7.claims.size), nextFresh = s7.nextFresh)
        }
      }
      return err
    }
  }

}
