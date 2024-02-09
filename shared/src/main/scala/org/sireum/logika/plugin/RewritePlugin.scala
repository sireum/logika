// #Sireum
/*
 Copyright (c) 2017-2024, Ryan Peroutka, Galois, Inc.
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
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.RewritingSystem.Rewriter
import org.sireum.logika.{Logika, RewritingSystem, Smt2, State, StepProofContext}

@datatype class RewritePlugin extends JustificationPlugin {

  val name: String = "RewritePlugin"

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invoke.ident.attr.resOpt match {
          case Some(res: AST.ResolvedInfo.Method) if res.id == "Rewrite" && res.owner == justificationName => return T
          case _ =>
        }
      case _ =>
    }
    return F
  }

  override def checkMode(logika: Logika, just: AST.ProofAst.Step.Justification, reporter: Reporter): B = {
    return T
  }

  def getPatterns(th: TypeHierarchy, exp: AST.Exp): ISZ[Rewriter.Pattern] = {
    def rec(rightToLeft: B, e: AST.Exp): HashSMap[ISZ[String], B] = {
      e match {
        case e: AST.Exp.Ref =>
          e.resOpt.get match {
            case res: AST.ResolvedInfo.Theorem =>
              return HashSMap.empty[ISZ[String], B] + res.name ~> rightToLeft
            case res: AST.ResolvedInfo.Fact =>
              return HashSMap.empty[ISZ[String], B] + res.name ~> rightToLeft
            case res: AST.ResolvedInfo.Method =>
              th.nameMap.get(res.owner :+ res.id).get match {
                case info: Info.Method =>
                  return HashSMap.empty[ISZ[String], B] + info.name ~> rightToLeft
                case _ => halt("Infeasible")
              }
            case res: AST.ResolvedInfo.Var =>
              th.nameMap.get(res.owner :+ res.id).get match {
                case info: Info.RsVal =>
                  return rec(F, info.ast.init)
                case _ => halt("Infeasible")
              }
            case _ => halt("Infeasible")
          }
        case e: AST.Exp.Binary =>
          var r = rec(rightToLeft, e.left)
          if (e.op == "++") {
            r = r ++ rec(rightToLeft, e.right).entries
          } else {
            r = r -- rec(rightToLeft, e.right).keys
          }
          return r
        case e: AST.Exp.RS =>
          var r = HashSMap.empty[ISZ[String], B]
          for (ref <- e.refs) {
            r = r ++ rec(e.rightToLeft, ref.asExp).entries
          }
          return r
        case _ => halt("Infeasible")
      }
    }
    var r = ISZ[Rewriter.Pattern]()
    for (p <- rec(F, exp).entries) {
      val (name, rightToLeft) = p
      th.nameMap.get(name).get match {
        case info: Info.Theorem =>
          var localPatternSet: RewritingSystem.LocalPatternSet = HashSSet.empty
          val claim: AST.CoreExp = info.ast.claim match {
            case AST.Exp.QuantType(true, AST.Exp.Fun(_, params, AST.Stmt.Expr(c))) =>
              for (p <- params) {
                localPatternSet = localPatternSet + (info.name, p.idOpt.get.value)
              }
              RewritingSystem.translate(th, c)
            case c => RewritingSystem.translate(th, c)
          }
          r = r :+ Rewriter.Pattern(name, rightToLeft, localPatternSet, claim)
        case info: Info.Fact => halt("TODO")
        case info: Info.Method => halt("TODO")
        case _ => halt("Infeasible")
      }
    }
    return r
  }

  override def handle(logika: Logika, smt2: Smt2, cache: Logika.Cache,
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext], state: State,
                      step: AST.ProofAst.Step.Regular, reporter: Logika.Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val patterns = getPatterns(logika.th, just.args(0))
    val from: AST.ProofAst.StepId = AST.Util.toStepIds(ISZ(just.args(1)), Logika.kind, reporter) match {
      case Some(s) => s(0)
      case _ => return emptyResult
    }
    val fromClaim: AST.Exp = spcMap.get(from) match {
      case Some(spc: StepProofContext.Regular) => spc.exp
      case _ =>
        reporter.error(from.posOpt, Logika.kind, s"Expecting a regular proof step")
        return emptyResult
    }
    val rw = Rewriter(logika.th, patterns, ISZ())
    val fromCoreClaim = RewritingSystem.translate(logika.th, fromClaim)
    val rwClaim = rw.transformCoreExp(fromCoreClaim).getOrElse(fromCoreClaim)
    val stepClaim = RewritingSystem.translate(logika.th, step.claim)
    @pure def traceElementST(q: (ISZ[String], B, AST.CoreExp, AST.CoreExp)): ST = {
      return st"""* ${if (q._2) "~" else ""}${(q._1, ".")}: ${q._3.prettyST}
                 |  = ${q._4}"""
    }
    if (rwClaim == stepClaim) {
      reporter.inform(just.id.attr.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Matched:
            |  ${stepClaim.prettyST}
            |
            |After rewriting $from:
            |  ${fromCoreClaim.prettyST}
            |
            |Rewriting trace:
            |${(for (q <- rw.trace) yield traceElementST(q), "\n")}
            |""".render)
      val q = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
      val (stat, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
      return Plugin.Result(stat, nextFresh, claims)
    } else {
      reporter.error(just.id.attr.posOpt, Logika.kind,
        st"""Could not match:
            |  ${stepClaim.prettyST}
            |
            |After rewriting $from to:
            |  ${rwClaim.prettyST}
            |
            |Rewriting trace:
            |${(for (q <- rw.trace) yield traceElementST(q), "\n")}
            |""".render)
      return emptyResult
    }
  }
}
