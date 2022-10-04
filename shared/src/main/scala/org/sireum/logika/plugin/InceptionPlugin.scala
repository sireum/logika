// #Sireum
/*
 Copyright (c) 2017-2022, Robby, Kansas State University
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
import org.sireum.message.Position
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Info
import org.sireum.lang.tipe.TypeChecker
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

@datatype class InceptionPlugin extends JustificationPlugin {

  val name: String = "InceptionPlugin"

  @pure def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    @strictpure def canHandleRes(res: AST.ResolvedInfo): B = res match {
      case res: AST.ResolvedInfo.Method =>
        logika.th.nameMap.get(res.owner :+ res.id).get match {
          case _: Info.Method => return T
          case info: Info.JustMethod if info.ast.etaOpt.nonEmpty => return T
          case _ => return F
        }
      case _: AST.ResolvedInfo.Fact => T
      case _: AST.ResolvedInfo.Theorem => T
      case _ => F
    }
    just match {
      case just: AST.ProofAst.Step.Justification.Apply => return canHandleRes(just.invokeIdent.attr.resOpt.get)
      case just: AST.ProofAst.Step.Justification.ApplyNamed => return canHandleRes(just.invokeIdent.attr.resOpt.get)
      case _ => return F
    }
  }

  def handle(logika: Logika,
             smt2: Smt2,
             cache: Smt2.Cache,
             spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
             state: State,
             step: AST.ProofAst.Step.Regular,
             reporter: Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Inception]
    def handleH(conc: String, sm: HashMap[String, AST.Typed], name: ISZ[String], context: ISZ[String], paramNames: ISZ[String],
                args: ISZ[AST.Exp], requires: ISZ[AST.Exp], ensures: ISZ[AST.Exp], posOpt: Option[Position]): Plugin.Result = {
      val id = st"${(name, ".")}".render
      val ips = org.sireum.logika.Util.Substitutor(sm, context,
        HashSMap.empty[String, AST.Exp] ++ ops.ISZOps(paramNames).zip(args), Reporter.create)
      val ipsSubst: ST = st"[${(for (pair <- ips.paramMap.entries) yield st"${pair._2.prettyST} / ${pair._1}", ", ")}]"
      var evidence = ISZ[ST]()
      if (just.witnesses.isEmpty) {
        var provenClaims = HashMap.empty[AST.Exp, (AST.ProofAst.StepId, AST.Exp)]
        for (spc <- spcMap.values) {
          spc match {
            case spc: StepProofContext.Regular => provenClaims = provenClaims + logika.th.normalizeExp(spc.exp) ~> ((spc.stepNo, spc.exp))
            case _ =>
          }
        }
        var ok = T
        for (require <- requires) {
          val req = ips.transformExp(require).getOrElseEager(require)
          val stepNoExpOpt = provenClaims.get(logika.th.normalizeExp(req))
          val pos = require.posOpt.get
          if (ips.reporter.messages.isEmpty && stepNoExpOpt.isEmpty) {
            reporter.error(posOpt, Logika.kind, s"Could not find a claim satisfying $id's assumption at [${pos.beginLine}, ${pos.beginColumn}]")
            ok = F
          } else {
            val (stepNo, exp) = stepNoExpOpt.get
            evidence = evidence :+
              st"""* [Inferred] ${Plugin.stepNoDesc(T, stepNo)} satisfies $id's assumption at [${pos.beginLine}, ${pos.beginColumn}], i.e.,
                  |  ${exp.prettyST}
                  |  ≈ $ipsSubst(${require.prettyST})
                  |  = ${req.prettyST}"""
          }
        }
        if (!ok || ips.reporter.messages.nonEmpty) {
          reporter.reports(ips.reporter.messages)
          return emptyResult
        }
      } else {
        var witnesses = HashMap.empty[AST.Exp, (AST.ProofAst.StepId, AST.Exp)]
        var ok = T
        for (w <- just.witnesses) {
          spcMap.get(w) match {
            case Some(spc: StepProofContext.Regular) => witnesses = witnesses + logika.th.normalizeExp(spc.exp) ~> ((spc.stepNo, spc.exp))
            case Some(_) =>
              reporter.error(w.posOpt, Logika.kind, s"Cannot use compound proof step $w as an argument for inception")
              ok = F
            case _ =>
              reporter.error(w.posOpt, Logika.kind, s"Could not find proof step $w")
              ok = F
          }
        }
        if (!ok) {
          return emptyResult
        }
        val rs: ISZ[AST.Exp] = for (require <- requires) yield ips.transformExp(require).getOrElseEager(require)
        if (ips.reporter.messages.nonEmpty) {
          reporter.reports(ips.reporter.messages)
          return emptyResult
        }
        for (i <- 0 until rs.size) {
          val pos = requires(i).posOpt.get
          val require = logika.th.normalizeExp(rs(i))
          witnesses.get(require) match {
            case Some((stepNo, exp)) =>
              evidence = evidence :+
                st"""* ${Plugin.stepNoDesc(T, stepNo)} satisfies $id's assumption at [${pos.beginLine}, ${pos.beginColumn}], i.e.,
                    |  ${exp.prettyST}
                    |  ≈ $ipsSubst(${requires(i).prettyST})
                    |  = ${rs(i).prettyST}"""
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Could not find a claim satisfying $id's assumption at [${pos.beginLine}, ${pos.beginColumn}]")
              ok = F
          }
        }
        if (!ok) {
          return emptyResult
        }
      }
      if (ips.reporter.messages.nonEmpty) {
        reporter.reports(ips.reporter.messages)
        return emptyResult
      }
      @pure def esMapEntry(ensure: AST.Exp): (AST.Exp, (Position, AST.Exp, AST.Exp)) = {
        val tensure = ips.transformExp(ensure).getOrElseEager(ensure)
        val dbensure = logika.th.normalizeExp(tensure)
        return (dbensure, (ensure.posOpt.get, ensure, tensure))
      }
      val esMap = HashMap ++ (for (e <- ensures) yield esMapEntry(e))
      val ePosExpTExpOpt = esMap.get(logika.th.normalizeExp(step.claim))
      if (ePosExpTExpOpt.isEmpty) {
        reporter.error(step.claim.posOpt, Logika.kind, st"Could not derive the stated claim from $id's $conc${if (ensures.size > 1) "s" else ""}".render)
        return emptyResult
      }
      val (status, nextFresh, claims, claim) = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
      if (status) {
        val (ePos, ensure, tensure) = ePosExpTExpOpt.get
        evidence = evidence :+
          st"""* The stated claim is guaranteed by $id's $conc at [${ePos.beginLine}, ${ePos.beginColumn}], i.e.,
              |  ${step.claim.prettyST}
              |  ≈ $ipsSubst(${ensure.prettyST})
              |  = ${tensure.prettyST}
              |"""
        reporter.inform(step.claim.posOpt.get, Logika.Reporter.Info.Kind.Verified,
          st"""Accepted by inception because:
              |
              |${(evidence, "\n\n")}
              |""".render
        )
      }
      return Plugin.Result(status, nextFresh, claims :+ claim)
    }
    def handleMethod(res: AST.ResolvedInfo.Method, posOpt: Option[Position], args: ISZ[AST.Exp]): Plugin.Result = {
      val mi: Info.Method = logika.th.nameMap.get(res.owner :+ res.id).get match {
        case info: Info.Method => info
        case _: Info.JustMethod =>
          reporter.error(posOpt, Logika.kind, "Inception on a @just method application is currently unsupported")
          return emptyResult
        case info => halt(s"Infeasible: $info")
      }
      val (reads, requires, modifies, ensures): (ISZ[AST.Exp.Ref], ISZ[AST.Exp], ISZ[AST.Exp.Ref], ISZ[AST.Exp]) = {
        mi.ast.contract match {
          case c: AST.MethodContract.Simple => (c.reads, c.requires, c.modifies, c.ensures)
          case _: AST.MethodContract.Cases =>
            reporter.error(posOpt, Logika.kind, "Could not use method with contract cases")
            return emptyResult
        }
      }
      if (reads.nonEmpty) {
        reporter.error(posOpt, Logika.kind, "Could not use method with non-empty reads clause")
        return emptyResult
      }
      if (modifies.nonEmpty) {
        reporter.error(posOpt, Logika.kind, "Could not use method with non-empty modifies clause")
        return emptyResult
      }
      val sm = TypeChecker.unifyFun(Logika.kind, logika.th, posOpt, TypeChecker.TypeRelation.Subtype, res.tpeOpt.get,
        mi.methodType.tpe, reporter).get
      return handleH("conclusion", sm, mi.name, mi.name, res.paramNames, args, requires, ensures, posOpt)
    }
    def handleFactTheorem(name: ISZ[String], posOpt: Option[Position], args: ISZ[AST.Exp]): Plugin.Result = {
      if (args.isEmpty) {
        reporter.error(posOpt, Logika.kind, "Please use ClaimOf justification for empty arguments")
        return Plugin.Result(F, state.nextFresh, ISZ())
      }
      logika.th.nameMap.get(name) match {
        case Some(info: Info.Fact) =>
          val fun = info.ast.claims(0).asInstanceOf[AST.Exp.Quant].fun
          val argTypes: ISZ[AST.Typed] = for (arg <- args) yield arg.typedOpt.get
          val paramTypes: ISZ[AST.Typed] = for (p <- fun.params) yield p.typedOpt.get
          val paramNames: ISZ[String] = for (p <- fun.params) yield p.idOpt.get.value
          val oldIgnore = reporter.ignore
          reporter.setIgnore(T)
          val smOpt = TypeChecker.unifies(logika.th, posOpt, TypeChecker.TypeRelation.Equal, paramTypes, argTypes, reporter)
          reporter.setIgnore(oldIgnore)
          smOpt match {
            case Some(sm) =>
              var claims = ISZ[AST.Exp]()
              for (c <- info.ast.claims) {
                claims = claims :+ c.asInstanceOf[AST.Exp.Quant].fun.exp.asInstanceOf[AST.Stmt.Expr].exp
              }
              return handleH("claim", sm, info.name, fun.context, paramNames, args, ISZ(), claims, posOpt)
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Inception on a Fact requires argument types ($argTypes) to be equal to parameter types ($paramTypes)")
              return emptyResult
          }
        case Some(info: Info.Theorem) =>
          val fun = info.ast.claim.asInstanceOf[AST.Exp.Quant].fun
          val claims = ISZ(fun.exp.asInstanceOf[AST.Stmt.Expr].exp)
          val argTypes: ISZ[AST.Typed] = for (arg <- args) yield arg.typedOpt.get
          val paramTypes: ISZ[AST.Typed] = for (p <- fun.params) yield p.typedOpt.get
          val paramNames: ISZ[String] = for (p <- fun.params) yield p.idOpt.get.value
          val oldIgnore = reporter.ignore
          reporter.setIgnore(T)
          val smOpt = TypeChecker.unifies(logika.th, posOpt, TypeChecker.TypeRelation.Equal, paramTypes, argTypes, reporter)
          reporter.setIgnore(oldIgnore)
          smOpt match {
            case Some(sm) =>
              return handleH("claim", sm, info.name, fun.context, paramNames, args, ISZ(), claims, posOpt)
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Inception on a ${if (info.ast.isLemma) "Lemma" else "Theorem"} requires equal argument types to parameter types")
              return emptyResult
          }
        case _ => halt("Infeasible")
      }
    }
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invoke.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return handleMethod(res, just.invoke.ident.posOpt, just.args)
          case res: AST.ResolvedInfo.Fact => return handleFactTheorem(res.name, just.invoke.ident.posOpt, just.args)
          case res: AST.ResolvedInfo.Theorem => return handleFactTheorem(res.name, just.invoke.ident.posOpt, just.args)
          case _ => halt("Infeasible")
        }
      case just: AST.ProofAst.Step.Justification.ApplyNamed =>
        just.invoke.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return handleMethod(res, just.invoke.ident.posOpt, just.args)
          case res: AST.ResolvedInfo.Fact => return handleFactTheorem(res.name, just.invoke.ident.posOpt, just.args)
          case res: AST.ResolvedInfo.Theorem => return handleFactTheorem(res.name, just.invoke.ident.posOpt, just.args)
          case _ => halt("Infeasible")
        }
      case _: AST.ProofAst.Step.Justification.ApplyEta =>
        halt("TODO") // TODO
    }
  }
}
