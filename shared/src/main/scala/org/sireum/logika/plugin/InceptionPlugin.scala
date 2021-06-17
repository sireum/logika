// #Sireum
/*
 Copyright (c) 2017-2021, Robby, Kansas State University
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
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.TypeChecker
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

object InceptionPlugin {
  @record class Substitutor(val substMap: HashMap[String, AST.Typed],
                            val context: QName,
                            val paramMap: HashSMap[String, AST.Exp],
                            val reporter: Reporter) extends AST.MTransformer {
    override def preTyped(o: AST.Typed): AST.MTransformer.PreResult[AST.Typed] = {
      o match {
        case o: AST.Typed.TypeVar =>
          substMap.get(o.id) match {
            case Some(t) => return AST.MTransformer.PreResult(F, MSome(t))
            case _ =>
          }
        case _ =>
      }
      return AST.MTransformer.PreResultTypedTypeVar
    }

    override def preExpIdent(o: AST.Exp.Ident): AST.MTransformer.PreResult[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.LocalVar if paramMap.contains(res.id) && res.context == context =>
          return AST.MTransformer.PreResult(F, MSome(paramMap.get(res.id).get))
        case _ =>
      }
      return AST.MTransformer.PreResultExpIdent
    }

    override def preExpInvoke(o: AST.Exp.Invoke): AST.MTransformer.PreResult[AST.Exp] = {
      val res: AST.ResolvedInfo.LocalVar = o.ident.attr.resOpt.get match {
        case lv: AST.ResolvedInfo.LocalVar if paramMap.contains(lv.id) && lv.context == context => lv
        case _ => return AST.MTransformer.PreResultExpInvoke
      }
      val arg = paramMap.get(res.id).get
      arg match {
        case arg: AST.Exp.Fun =>
          arg.exp match {
            case argExp: AST.Stmt.Expr =>
              var fParamMap = HashSMap.empty[String, AST.Exp]
              for (pArg <- ops.ISZOps(arg.params).zip(o.args)) {
                pArg._1.idOpt match {
                  case Some(id) => fParamMap = fParamMap + id.value ~> pArg._2
                  case _ =>
                }
              }
              val subst = Substitutor(substMap, arg.context, fParamMap, Reporter.create)
              val expOpt = subst.transformExp(argExp.exp)
              reporter.reports(subst.reporter.messages)
              if (expOpt.isEmpty) {
                return AST.MTransformer.PreResult(T, MSome(o(receiverOpt = paramMap.get(res.id),
                  ident = o.ident(id = AST.Id("apply", o.ident.id.attr), attr = o.ident.attr(resOpt = TypeChecker.applyResOpt)))))
              } else {
                return AST.MTransformer.PreResult(T, expOpt)
              }
            case _ =>
              reporter.error(arg.posOpt, Logika.kind, "Invalid argument form for inception")
          }
        case AST.Exp.Eta(ref) =>
          ref match {
            case ref: AST.Exp.Ident =>
              return AST.MTransformer.PreResult(T, MSome(o(receiverOpt = None(), ident = ref)))
            case ref: AST.Exp.Select =>
              return AST.MTransformer.PreResult(T, MSome(o(receiverOpt = ref.receiverOpt, ident = AST.Exp.Ident(ref.id, ref.attr))))
          }
        case _ =>
          reporter.error(arg.posOpt, Logika.kind, "Invalid argument form for inception")
      }
      return AST.MTransformer.PreResult(F, MSome(paramMap.get(res.id).get))
    }
  }
}

@datatype class InceptionPlugin extends Plugin {

  val name: String = "InceptionPlugin"

  @pure def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    val res: AST.ResolvedInfo.Method = just match {
      case just: AST.ProofAst.Step.Justification.Incept =>
        just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      case just: AST.ProofAst.Step.Justification.InceptNamed =>
        just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      case _ => return F
    }
    logika.th.nameMap.get(res.owner :+ res.id).get match {
      case _: Info.Method => return T
      case info: Info.JustMethod if info.ast.etaOpt.nonEmpty => return T
      case _ => return F
    }
  }

  def handle(logika: Logika,
             smt2: Smt2,
             log: B,
             logDirOpt: Option[String],
             spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
             state: State,
             step: AST.ProofAst.Step.Regular,
             reporter: Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Inception]
    def handleH(res: AST.ResolvedInfo.Method, posOpt: Option[Position], args: ISZ[AST.Exp]): Plugin.Result = {
      val mi = logika.th.nameMap.get(res.owner :+ res.id).get.asInstanceOf[Info.Method]
      val (reads, requires, modifies, ensures): (ISZ[AST.Exp.Ident], ISZ[AST.Exp], ISZ[AST.Exp.Ident], ISZ[AST.Exp]) = {
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

      val smOpt = TypeChecker.unifyFun(Logika.kind, logika.th, posOpt, TypeChecker.TypeRelation.Subtype, res.tpeOpt.get,
        mi.methodType.tpe, reporter)
      val ips = InceptionPlugin.Substitutor(smOpt.get, mi.name,
        HashSMap.empty[String, AST.Exp] ++ ops.ISZOps(res.paramNames).zip(args), Reporter.create)
      val ipsSubst: ST = st"[${(for (pair <- ips.paramMap.entries) yield st"${pair._2.prettyST} / ${pair._1}", ", ")}]"
      var evidence = ISZ[ST]()
      if (just.witnesses.isEmpty) {
        var provenClaims = HashMap.empty[AST.Exp, (AST.ProofAst.StepId, AST.Exp)]
        for (spc <- spcMap.values) {
          spc match {
            case spc: StepProofContext.Regular => provenClaims = provenClaims + AST.Util.deBruijn(spc.exp) ~> ((spc.stepNo, spc.exp))
            case _ =>
          }
        }
        var ok = T
        for (require <- requires) {
          val req = ips.transformExp(require).getOrElseEager(require)
          val stepNoExpOpt = provenClaims.get(AST.Util.deBruijn(req))
          val pos = require.posOpt.get
          if (ips.reporter.messages.isEmpty && stepNoExpOpt.isEmpty) {
            reporter.error(posOpt, Logika.kind, s"Could not find a claim satisfying ${mi.methodRes.id}'s assumption at [${pos.beginLine}, ${pos.beginColumn}]")
            ok = F
          } else {
            val (stepNo, exp) = stepNoExpOpt.get
            evidence = evidence :+
              st"""* [Inferred] ${Plugin.stepNoDesc(T, stepNo)} satisfies ${mi.methodRes.id}'s assumption at [${pos.beginLine}, ${pos.beginColumn}], i.e.,
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
            case Some(spc: StepProofContext.Regular) => witnesses = witnesses + AST.Util.deBruijn(spc.exp) ~> ((spc.stepNo, spc.exp))
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
          val require = AST.Util.deBruijn(rs(i))
          witnesses.get(require) match {
            case Some((stepNo, exp)) =>
              evidence = evidence :+
                st"""* ${Plugin.stepNoDesc(T, stepNo)} satisfies ${mi.methodRes.id}'s assumption at [${pos.beginLine}, ${pos.beginColumn}], i.e.,
                    |  ${exp.prettyST}
                    |  ≈ $ipsSubst(${requires(i).prettyST})
                    |  = ${rs(i).prettyST}"""
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Could not find a claim satisfying ${mi.methodRes.id}'s assumption at [${pos.beginLine}, ${pos.beginColumn}]")
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
        val dbensure = AST.Util.deBruijn(tensure)
        return (dbensure, (ensure.posOpt.get, ensure, tensure))
      }
      val esMap = HashMap ++ (for (e <- ensures) yield esMapEntry(e))
      val ePosExpTExpOpt = esMap.get(step.claimDeBruijn)
      if (ePosExpTExpOpt.isEmpty) {
        reporter.error(step.claim.posOpt, Logika.kind, st"Could not derive the stated claim from any of ${mi.methodRes.id}'s conclusions".render)
        return emptyResult
      }
      val (status, nextFresh, claims, claim) = logika.evalRegularStepClaim(smt2, state, step.claim, step.id.posOpt, reporter)
      if (status) {
        val (ePos, ensure, tensure) = ePosExpTExpOpt.get
        evidence = evidence :+
          st"""* The stated claim is guaranteed by ${mi.methodRes.id}'s conclusion at [${ePos.beginLine}, ${ePos.beginColumn}], i.e.,
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
    just match {
      case just: AST.ProofAst.Step.Justification.Incept => return handleH(just.invoke.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method], just.invoke.ident.posOpt, just.args)
      case just: AST.ProofAst.Step.Justification.InceptNamed => return handleH(just.invoke.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method], just.invoke.ident.posOpt, just.args)
      case _: AST.ProofAst.Step.Justification.InceptEta =>
        halt("TODO") // TODO
    }
  }
}
