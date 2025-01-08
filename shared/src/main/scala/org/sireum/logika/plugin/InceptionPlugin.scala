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
import org.sireum.message.Position
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Info
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

object InceptionPlugin {

  def extractIdExpMapping(th: TypeHierarchy, from: AST.Exp, to: AST.Exp, init: HashSMap[String, AST.Exp],
                          context: ISZ[String], ids: HashSSet[String], sm: HashMap[String, AST.Typed]): Option[HashSMap[String, AST.Exp]] = {
    @pure def shouldExtract(resOpt: Option[AST.ResolvedInfo]): B = {
      resOpt match {
        case Some(res: AST.ResolvedInfo.LocalVar) => return res.context == context && ids.contains(res.id)
        case _ => return F
      }
    }
    var r = init
    var ok = T
    def addResult(id: String, exp: AST.Exp): Unit = {
      r.get(id) match {
        case Some(e) => ok = th.normalizeExp(exp) == th.normalizeExp(e)
        case _ => r = r + id ~> exp
      }
    }
    def recInvoke(fe: AST.Exp.Invoke, te: AST.Exp.Invoke): Unit = {
      ok = fe.receiverOpt.isEmpty == te.receiverOpt.isEmpty && fe.args.size == te.args.size
      if (!ok) {
        return
      }
      (fe.receiverOpt, te.receiverOpt) match {
        case (Some(fre), Some(tre)) => rec(fre, tre)
        case (_, _) =>
      }
      rec(fe.ident, te.ident)
      for (p <- ops.ISZOps(fe.args).zip(te.args) if ok) {
        val (farg, targ) = p
        rec(farg, targ)
      }
    }
    def rec(fe: AST.Exp, te: AST.Exp): Unit = {
      def recAssignExp(fae: AST.AssignExp, tae: AST.AssignExp): Unit = {
        (fae, tae) match {
          case (fae: AST.Stmt.Expr, tae: AST.Stmt.Expr) => rec(fae.exp, tae.exp)
          case _ =>
            ok = F
        }
      }

      def recQuant(fq: AST.Exp.QuantType, tq: AST.Exp.QuantType): Unit = {
        var fen = fq
        var ten = tq
        ok = fen.isForall == ten.isForall
        if (fen.fun.params.size != ten.fun.params.size) {
          val n: Z = if (fen.fun.params.size < ten.fun.params.size) fen.fun.params.size else ten.fun.params.size
          fen = if (fen.fun.params.size == n) fen else
            fen(fun = fen.fun(params = ops.ISZOps(fen.fun.params).slice(0, n), exp = AST.Stmt.Expr(
              AST.Exp.QuantType(fen.isForall, AST.Exp.Fun(fen.fun.context,
                ops.ISZOps(fen.fun.params).slice(n, fen.fun.params.size), fen.fun.exp, fen.fun.attr), fen.attr),
              AST.TypedAttr(fen.fun.exp.asStmt.posOpt, AST.Typed.bOpt))))
          ten = if (ten.fun.params.size == n) fen else ten(fun = ten.fun(params =
            ops.ISZOps(ten.fun.params).slice(0, n), exp = AST.Stmt.Expr(AST.Exp.QuantType(ten.isForall,
            AST.Exp.Fun(ten.fun.context, ops.ISZOps(ten.fun.params).slice(n, ten.fun.params.size), ten.fun.exp,
              ten.fun.attr), ten.attr), AST.TypedAttr(ten.fun.exp.asStmt.posOpt, AST.Typed.bOpt))))
        }
        if (!ok) {
          return
        }
        recAssignExp(fen.fun.exp, ten.fun.exp)
      }
      if (!ok) {
        return
      }
      (fe, te) match {
        case (fe: AST.Exp.LitB, te: AST.Exp.LitB) =>
          ok = fe.value == te.value
        case (fe: AST.Exp.LitZ, te: AST.Exp.LitZ) =>
          ok = fe.value == te.value
        case (fe: AST.Exp.Ident, te) =>
          te match {
            case te: AST.Exp.Ident if fe.resOpt == te.resOpt =>
              return
            case _ =>
          }
          if (shouldExtract(fe.resOpt)) {
            addResult(fe.id.value, te)
          } else {
            ok = th.normalizeExp(fe) == th.normalizeExp(te)
          }
        case (fe: AST.Exp.Unary, te: AST.Exp.Unary) =>
          ok = fe.attr.resOpt == te.attr.resOpt
          rec(fe.exp, te.exp)
        case (fe: AST.Exp.Binary, te: AST.Exp.Binary) =>
          ok = fe.attr.resOpt == te.attr.resOpt
          rec(fe.left, te.left)
          rec(fe.right, te.right)
        case (fe: AST.Exp.QuantType, te: AST.Exp.QuantRange) =>
          recQuant(th.normalizeExp(fe).asInstanceOf[AST.Exp.QuantType],
            th.normalizeExp(te).asInstanceOf[AST.Exp.QuantType])
        case (fe: AST.Exp.QuantType, te: AST.Exp.QuantType) =>
          recQuant(th.normalizeExp(fe).asInstanceOf[AST.Exp.QuantType],
            th.normalizeExp(te).asInstanceOf[AST.Exp.QuantType])
        case (fe: AST.Exp.Invoke, te) if ids.contains(fe.ident.id.value) =>
          val id = fe.ident.id.value
          val fcontext = ISZ(id)
          var params = ISZ[AST.Exp.Fun.Param]()
          var paramTypes = ISZ[AST.Typed]()
          var argParamRefMap = HashMap.empty[AST.Exp, AST.Exp]
          for (i <- 0 until fe.args.size) {
            val arg = fe.args(i)
            val pid = s"${id}X$i"
            val ptOpt = Some(arg.typedOpt.get.subst(sm))
            params = params :+ AST.Exp.Fun.Param(Some(AST.Id(pid, AST.Attr(arg.posOpt))), None(), ptOpt)
            paramTypes = paramTypes :+ ptOpt.get
            argParamRefMap = argParamRefMap + arg ~> AST.Exp.Ident(AST.Id(pid, AST.Attr(arg.posOpt)),
              AST.ResolvedAttr(arg.posOpt, Some(AST.ResolvedInfo.LocalVar(fcontext,
                AST.ResolvedInfo.LocalVar.Scope.Current, F, T, pid)), ptOpt))
          }
          AST.Util.ExpSubstitutor(argParamRefMap).transformExp(te) match {
            case MSome(te2) =>
              val fun = AST.Exp.Fun(fcontext, params, AST.Stmt.Expr(te2, AST.TypedAttr(te.posOpt, te.typedOpt)),
                AST.TypedAttr(fe.posOpt, Some(AST.Typed.Fun(AST.Purity.Pure, F, paramTypes, fe.typedOpt.get))))
              addResult(id, fun)
              if (!ok) {
                te match {
                  case te: AST.Exp.Invoke =>
                    ok = T
                    recInvoke(fe, te)
                  case _ =>
                }
              }
            case _ =>
          }
          r.get(id) match {
            case Some(AST.Exp.Fun(_, _, e: AST.Stmt.Expr)) =>
              val paramRefArgMap = HashMap ++ (for (p <- argParamRefMap.entries) yield (p._2, p._1))
              val e2 = AST.Util.ExpSubstitutor(paramRefArgMap).transformExp(e.exp).getOrElseEager(e.exp)
              (e2, te) match {
                case (e2: AST.Exp.Invoke, te: AST.Exp.Invoke) => recInvoke(e2, te)
                case _ => rec(e2, te)
              }
              ok = T
            case _ =>
          }
          te match {
            case te: AST.Exp.Invoke if id == te.ident.id.value && fe.args.size == te.args.size =>
              for (p <- ops.ISZOps(fe.args).zip(te.args)) {
                rec(p._1, p._2)
              }
            case _ =>
          }
        case (fe: AST.Exp.Invoke, te: AST.Exp.Invoke) => recInvoke(fe, te)
        case (_, _) => ok = F
      }
    }
    rec(from, to)
    return if (ok) Some(r) else None()
  }
}

import InceptionPlugin._

@datatype class InceptionPlugin extends JustificationPlugin {

  val name: String = "InceptionPlugin"

  @pure def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    @pure def canHandleRes(res: AST.ResolvedInfo): B = {
      val r: B = res match {
        case res: AST.ResolvedInfo.Method =>
          logika.th.nameMap.get(res.owner :+ res.id).get match {
            case _: Info.Method => T
            case _ => F
          }
        case _: AST.ResolvedInfo.Fact => T
        case _: AST.ResolvedInfo.Theorem => T
        case _ => F
      }
      return r
    }
    just match {
      case just: AST.ProofAst.Step.Justification.Apply => return canHandleRes(just.invokeIdent.attr.resOpt.get)
      case just: AST.ProofAst.Step.Justification.ApplyEta => return canHandleRes(just.eta.ref.resOpt.get)
      case _ => return F
    }
  }

  override def checkMode(logika: Logika, just: AST.ProofAst.Step.Justification, reporter: Reporter): B = {
    return T
  }

  def handle(logika: Logika,
             smt2: Smt2,
             cache: Logika.Cache,
             spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
             state: State,
             step: AST.ProofAst.Step.Regular,
             reporter: Reporter): State = {
    @strictpure def err: State = state(status = State.Status.Error)
    val just = step.just

    def handleH(conc: String, sm: HashMap[String, AST.Typed], name: ISZ[String], context: ISZ[String],
                paramNames: ISZ[String], args: ISZ[AST.Exp], requires: ISZ[AST.Exp], ensures: ISZ[AST.Exp],
                posOpt: Option[Position], evidenceInit: ISZ[ST]): State = {
      val id = name(name.size - 1)
      val ips = org.sireum.logika.Util.Substitutor(sm, context,
        HashSMap.empty[String, AST.Exp] ++ ops.ISZOps(paramNames).zip(args), reporter.empty)
      val ipsSubst: ST = st"[${(for (pair <- ips.paramMap.entries) yield st"${pair._2.prettyST} / ${pair._1}", ", ")}]"
      var evidence = evidenceInit
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
          } else if (logika.config.detailedInfo) {
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
          return err
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
          return err
        }
        val rs: ISZ[AST.Exp] = for (require <- requires) yield ips.transformExp(require).getOrElseEager(require)
        if (ips.reporter.messages.nonEmpty) {
          reporter.reports(ips.reporter.messages)
          return err
        }
        for (i <- 0 until rs.size) {
          val pos = requires(i).posOpt.get
          val require = logika.th.normalizeExp(rs(i))
          witnesses.get(require) match {
            case Some((stepNo, exp)) =>
              if (logika.config.detailedInfo) {
                evidence = evidence :+
                  st"""* ${Plugin.stepNoDesc(T, stepNo)} satisfies $id's assumption at [${pos.beginLine}, ${pos.beginColumn}], i.e.,
                      |  ${exp.prettyST}
                      |  ≈ $ipsSubst(${requires(i).prettyST})
                      |  = ${rs(i).prettyST}"""
              }
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Could not find a claim satisfying $id's assumption at [${pos.beginLine}, ${pos.beginColumn}]")
              ok = F
          }
        }
        if (!ok) {
          return err
        }
      }
      if (ips.reporter.messages.nonEmpty) {
        reporter.reports(ips.reporter.messages)
        return err
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
        return err
      }
      val s0 = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
      if (s0.ok && logika.config.detailedInfo) {
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
              |""".render)
      }
      return s0
    }

    def handleEtaH(conc: String, sm: HashMap[String, AST.Typed], name: ISZ[String], context: ISZ[String], paramNames: ISZ[String],
                   requires: ISZ[AST.Exp], ensures: ISZ[AST.Exp], posOpt: Option[Position]): State = {
      if (requires.size != just.witnesses.size) {
        reporter.error(posOpt, Logika.kind, s"Requires ${requires.size} witnesses, but found ${just.witnesses}")
        return err
      }
      val id = name(name.size - 1)
      if (id == "AllE") {
        println("Here")
      }
      var ok = T
      var idExpMap = HashSMap.empty[String, AST.Exp]
      val paramIds = HashSSet ++ paramNames
      var fromToStepIdChecks = ISZ[(AST.Exp, AST.Exp, AST.ProofAst.StepId, B)]()
      for (p <- ops.ISZOps(just.witnesses).zip(requires)) {
        val (w, r) = p
        spcMap.get(w) match {
          case Some(spc: StepProofContext.Regular) =>
            fromToStepIdChecks = fromToStepIdChecks :+ (r, spc.exp, spc.stepNo, T)
          case Some(_) =>
            reporter.error(w.posOpt, Logika.kind, s"Cannot use compound proof step $w as an argument for inception")
            ok = F
          case _ =>
            reporter.error(w.posOpt, Logika.kind, s"Could not find proof step $w")
            ok = F
        }
      }
      if (!ok) {
        return err
      }

      for (e <- ensures) {
        fromToStepIdChecks = fromToStepIdChecks :+ (e, step.claim, step.id, F)
      }

      var done = F
      for (_ <- 0 until 2 if !done; q <- fromToStepIdChecks) {
        val (from, to, stepId, check) = q
        extractIdExpMapping(logika.th, from, to, idExpMap, context, paramIds, sm) match {
          case Some(newIdExpMap) => idExpMap = newIdExpMap
          case _ =>
            if (check) {
              reporter.error(posOpt, Logika.kind, st"Could not infer { ${(paramNames -- idExpMap.keys, ", ")} } from witness $stepId for ${from.prettyST}".render)
              ok = F
            }
        }
        done = paramNames.size == idExpMap.size
      }

      var args = ISZ[AST.Exp]()
      for (p <- paramNames) {
        idExpMap.get(p) match {
          case Some(e) => args = args :+ e
          case _ =>
            reporter.error(posOpt, Logika.kind, st"Could not infer argument for $id's parameter $p".render)
            ok = F
        }
      }

      // Uncomment to test RewritingSystem unification algorithm
      /*
      {
        var patterns = ISZ[AST.CoreExp.Base]()
        var exps = ISZ[AST.CoreExp.Base]()
        for (q <- fromToStepIdChecks) {
          val (from, to, _, _) = q
          patterns = patterns :+ org.sireum.logika.RewritingSystem.translate(logika.th, T, from)
          exps = exps :+ org.sireum.logika.RewritingSystem.translate(logika.th, F, to)
        }
        val localPatternSet = HashSSet ++ (for (id <- paramIds.elements) yield (context, id))
        org.sireum.logika.RewritingSystem.unify(F, logika.th, localPatternSet, patterns, exps) match {
          case Either.Left(m) if !ok =>
            reporter.error(posOpt, Logika.kind,
              st"""Diff result: {
                  |  ${(for (p <- m.entries) yield st"${p._1._2} ~> ${p._2.prettyST}", ",\n")}
                  |}""".render)
          case Either.Right(ms) if ok =>
            reporter.error(posOpt, Logika.kind,
              st"""Unexpected unification error(s):
                  |${(ms, "\n")}""".render)
          case _ =>
        }
      }
      */

      if (ok) {
        return handleH(conc, sm, name, context, paramNames, args, requires, ensures, posOpt, ISZ(
          st"""* [Inferred] $id's parameter(s) and argument(s)
              |
              |  ${(for (p <- ops.ISZOps(paramNames).zip(args)) yield st"+ ${p._1} ≡ ${p._2.prettyST}", "\n\n")}
              |"""))
      } else {
        return err
      }
    }

    def handleMethod(isEta: B, res: AST.ResolvedInfo.Method, posOpt: Option[Position], args: ISZ[AST.Exp]): State = {
      val mi: Info.Method = logika.th.nameMap.get(res.owner :+ res.id).get match {
        case info: Info.Method => info
        case _: Info.JustMethod =>
          reporter.error(posOpt, Logika.kind, "Inception on a @just method application is currently unsupported")
          return err
        case info => halt(s"Infeasible: $info")
      }
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
      val sm = TypeChecker.unifyFun(Logika.kind, logika.th, posOpt, TypeChecker.TypeRelation.Subtype, res.tpeOpt.get,
        mi.methodType.tpe, reporter).get
      if (isEta) {
        return handleEtaH("conclusion", sm, mi.name, mi.name, res.paramNames, requires, ensures, posOpt)
      } else {
        return handleH("conclusion", sm, mi.name, mi.name, res.paramNames, args, requires, ensures, posOpt, ISZ())
      }
    }
    def handleFactTheorem(name: ISZ[String], posOpt: Option[Position], args: ISZ[AST.Exp]): State = {
      if (args.isEmpty) {
        reporter.error(posOpt, Logika.kind, "Please use ClaimOf justification for empty arguments")
        return err
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
              return handleH("claim", sm, info.name, fun.context, paramNames, args, ISZ(), claims, posOpt, ISZ())
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Inception on a Fact requires argument types ($argTypes) to be equal to parameter types ($paramTypes)")
              return err
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
              return handleH("claim", sm, info.name, fun.context, paramNames, args, ISZ(), claims, posOpt, ISZ())
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Inception on a ${if (info.ast.isLemma) "Lemma" else "Theorem"} requires equal argument types to parameter types")
              return err
          }
        case _ => halt("Infeasible")
      }
    }
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invoke.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return handleMethod(F, res, just.invoke.ident.posOpt, just.args)
          case res: AST.ResolvedInfo.Fact => return handleFactTheorem(res.name, just.invoke.ident.posOpt, just.args)
          case res: AST.ResolvedInfo.Theorem => return handleFactTheorem(res.name, just.invoke.ident.posOpt, just.args)
          case _ => halt("Infeasible")
        }
      case just: AST.ProofAst.Step.Justification.ApplyEta =>
        just.eta.ref.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return handleMethod(T, res, just.eta.ref.posOpt, ISZ())
          case _: AST.ResolvedInfo.Fact =>
            reporter.error(just.eta.posOpt, Logika.kind, "Cannot use argument-less justifications on facts")
            return err
          case _: AST.ResolvedInfo.Theorem =>
            reporter.error(just.eta.posOpt, Logika.kind, "Cannot use argument-less justifications on theorems")
            return err
          case _ => halt("Infeasible")
        }
      case _ => halt("Infeasible")
    }
  }
}
