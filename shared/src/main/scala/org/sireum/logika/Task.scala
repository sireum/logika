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

package org.sireum.logika

import org.sireum._
import org.sireum.message.Message
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.plugin.Plugin
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy

@datatype trait Task {
  def compute(smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): ISZ[Message]
}

object Task {

  @record class IndexTypeVarCollector(var s: HashSet[AST.Typed.TypeVar]) extends AST.MTransformer {
    override def postTypedName(o: AST.Typed.Name): MOption[AST.Typed] = {
      if (o.ids == AST.Typed.isName || o.ids == AST.Typed.msName) {
        o.args(0) match {
          case t: AST.Typed.TypeVar => s = s + t
          case _ =>
        }
      }
      return AST.MTransformer.PostResultTypedName
    }
  }

  @datatype class Fact(val th: TypeHierarchy,
                       val config: Config,
                       val fact: AST.Stmt.Fact,
                       val plugins: ISZ[Plugin]) extends Task {
    override def compute(smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): ISZ[Message] = {
      val logika = Logika(th, config, Context.empty, plugins)
      for (tp <- fact.typeParams) {
        smt2.addType(AST.Typed.TypeVar(tp.id.value), reporter)
      }
      var s0 = State.create
      val claims: ISZ[AST.Exp] = if (fact.isFun) {
        val first = fact.claims(0).asInstanceOf[AST.Exp.Quant]
        for (p <- first.fun.params) {
          val id = p.idOpt.get
          val pos = id.attr.posOpt.get
          val s1 = Util.idIntro(pos, s0, first.fun.context, id.value, p.typedOpt.get, Some(pos))._1
          s0 = s1
        }
        for (c <- fact.claims) yield c.asInstanceOf[AST.Exp.Quant].fun.exp.asInstanceOf[AST.Stmt.Expr].exp
      } else {
        fact.claims
      }
      var i = 1
      for (claim <- claims if s0.status) {
        val pos = claim.posOpt.get
        val ISZ((s1, v)) = logika.evalExp(Logika.Split.Disabled, smt2, cache, T, s0, claim, reporter)
        val (s2, sym) = logika.value2Sym(s1, v, pos)
        val s3 = s2.addClaim(State.Claim.Prop(T, sym))
        if (smt2.satResult(cache, T, config.logVc, config.logVcDirOpt, s"Fact claim #$i at [${pos.beginLine}, ${pos.beginColumn}]", pos,
          s3.claims, reporter)._2.kind === Smt2Query.Result.Kind.Unsat) {
          reporter.error(claim.posOpt, Logika.kind, s"Unsatisfiable fact claim")
          s0 = s3(status = F)
        } else {
          s0 = s3
        }
        i = i + 1
      }
      return reporter.messages
    }
  }

  @datatype class Theorem(val th: TypeHierarchy,
                       val config: Config,
                       val theorem: AST.Stmt.Theorem,
                       val plugins: ISZ[Plugin]) extends Task {
    override def compute(smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): ISZ[Message] = {
      val logika = Logika(th, config, Context.empty, plugins)
      for (tp <- theorem.typeParams) {
        smt2.addType(AST.Typed.TypeVar(tp.id.value), reporter)
      }
      var p = (State.create, HashSMap.empty[AST.ProofAst.StepId, StepProofContext])
      for (step <- theorem.proof.steps if p._1.status) {
        p = logika.evalProofStep(smt2, cache, p, step, reporter)
      }
      if (!p._1.status) {
        return reporter.messages
      }
      val normClaim: AST.Exp = AST.Util.normalizeExp(
        if (theorem.isFun) theorem.claim.asInstanceOf[AST.Exp.Quant].fun.exp.asInstanceOf[AST.Stmt.Expr].exp
        else theorem.claim)
      val spcEntries = p._2.entries
      for (i <- spcEntries.size - 1 to 0 by -1 if spcEntries(i)._2.isInstanceOf[StepProofContext.Regular]) {
        val StepProofContext.Regular(stepNo, claim, _) = spcEntries(i)._2
        val spcPos = stepNo.posOpt.get
        if (normClaim == AST.Util.normalizeExp(claim)) {
          reporter.inform(normClaim.posOpt.get, Logika.Reporter.Info.Kind.Verified,
            st"""Accepted by using ${Plugin.stepNoDesc(F, spcEntries(i)._1)}, i.e.:
                |
                |$claim
                |""".render)
          return reporter.messages
        }
      }
      return reporter.messages
    }
  }

  @datatype class Stmts(val th: TypeHierarchy,
                        val config: Config,
                        val stmts: ISZ[AST.Stmt],
                        val plugins: ISZ[Plugin]) extends Task {
    override def compute(smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): ISZ[Message] = {
      val logika = Logika(th, config, Context.empty, plugins)
      val itvc = IndexTypeVarCollector(HashSet.empty)
      for (stmt <- stmts) {
        itvc.transformStmt(stmt)
      }
      val csmt2 = smt2
      for (tv <- itvc.s.elements) {
        csmt2.addTypeVarIndex(tv)
      }
      for (state <- logika.evalStmts(Logika.Split.Default, csmt2, cache, None(), T, State.create, stmts, reporter) if state.status) {
        if (stmts.nonEmpty) {
          val lastPos = stmts(stmts.size - 1).posOpt.get
          logika.logPc(config.logPc, config.logRawPc, state(status = F), reporter, Some(lastPos))
        }
      }
      return reporter.messages
    }
  }

  @datatype class Method(val par: Z,
                         val th: TypeHierarchy,
                         val config: Config,
                         val method: AST.Stmt.Method,
                         val caseIndex: Z,
                         val plugins: ISZ[Plugin]) extends Task {
    override def compute(smt2: Smt2, cache: Smt2.Cache, reporter: Reporter): ISZ[Message] = {
      val ms = Util.detectUnsupportedFeatures(method)
      if (ms.nonEmpty) {
        reporter.reports(ms)
        return reporter.messages
      }
      val itvc = IndexTypeVarCollector(HashSet.empty)
      itvc.transformStmt(method)
      val tvs = itvc.s.elements
      val csmt2 = smt2
      for (tv <- tvs) {
        csmt2.addTypeVarIndex(tv)
      }
      Util.checkMethod(th, plugins, method, caseIndex, config, csmt2, cache, reporter)
      return reporter.messages
    }
  }

}

