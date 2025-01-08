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

package org.sireum.logika

import org.sireum._
import org.sireum.lang.ast.{Attr, ResolvedAttr, TypedAttr}
import org.sireum.message.Message
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.plugin.Plugin
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy

@datatype trait Task {
  @strictpure def th: TypeHierarchy
  def compute(nameExePathMap: HashMap[String, String], maxCores: Z, fileOptions: LibUtil.FileOptionMap,
              smt2: Smt2, cache: Logika.Cache, reporter: Reporter): ISZ[Message]
}

object Task {

  @datatype class Fact(val th: TypeHierarchy,
                       val config: Config,
                       val fact: AST.Stmt.Fact,
                       val plugins: ISZ[Plugin]) extends Task {
    override def compute(nameExePathMap: HashMap[String, String], maxCores: Z, fileOptions: LibUtil.FileOptionMap,
                         smt2: Smt2, cache: Logika.Cache, reporter: Reporter): ISZ[Message] = {
      val context = Context.empty(nameExePathMap, maxCores, fileOptions)(methodOpt = Some(Context.Method(
        isHelper = F,
        hasInline = F,
        owner = ops.ISZOps(fact.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Fact].name).dropRight(1),
        id = fact.id.value,
        receiverTypeOpt = None(),
        params = ISZ(),
        retType = AST.Typed.b,
        reads = ISZ(),
        requires = ISZ(),
        modifies = ISZ(),
        ensures = ISZ(),
        objectVarInMap = HashMap.empty,
        fieldVarInMap = HashMap.empty,
        localInMap = HashMap.empty,
        posOpt = fact.posOpt,
        storage = HashMap.empty
      )))
      val csmt2 = smt2
      val logika = Logika(th, config, context, plugins)
      for (tp <- fact.typeParams) {
        csmt2.addType(config, AST.Typed.TypeVar(tp.id.value, tp.kind), reporter)
      }
      var s0 = State.create
      var ctx = logika.context.methodName
      val claims: ISZ[AST.Exp] = if (fact.isFun) {
        val first = fact.claims(0).asInstanceOf[AST.Exp.Quant]
        ctx = first.fun.context
        for (p <- first.fun.params) {
          val id = p.idOpt.get
          val pos = id.attr.posOpt.get
          val s1 = Util.idIntro(pos, s0, ctx, id.value, p.typedOpt.get, Some(pos))._1
          s0 = s1
        }
        for (c <- fact.claims) yield c.asInstanceOf[AST.Exp.Quant].fun.exp.asInstanceOf[AST.Stmt.Expr].exp
      } else {
        fact.claims
      }
      var i = 1
      for (claim <- claims if s0.ok) {
        val pos = claim.posOpt.get
        val ISZ((s1, v)) = logika.evalExp(Logika.Split.Disabled, csmt2, cache, T, s0, claim, reporter)
        if (s1.ok) {
          val (s2, sym) = logika.value2Sym(s1, v, pos)
          val s3 = s2.addClaim(State.Claim.Prop(T, sym))
          val r = csmt2.satResult(ctx, config, cache, Smt2.satTimeoutInMs, T,
            s"Fact claim #$i at [${pos.beginLine}, ${pos.beginColumn}]", pos, s3.claims, reporter)
          if (r._2.kind ==Smt2Query.Result.Kind.Unsat) {
            reporter.error(claim.posOpt, Logika.kind, s"Unsatisfiable fact claim")
            s0 = s3(status = State.Status.Error)
          } else {
            s0 = s3
          }
        } else {
          s0 = s1
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
    override def compute(nameExePathMap: HashMap[String, String], maxCores: Z, fileOptions: LibUtil.FileOptionMap,
                         smt2: Smt2, cache: Logika.Cache, reporter: Reporter): ISZ[Message] = {
      val context = Context.empty(nameExePathMap, maxCores, fileOptions)(methodOpt = Some(Context.Method(
        isHelper = F,
        hasInline = F,
        owner = ops.ISZOps(theorem.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Theorem].name).dropRight(1),
        id = theorem.id.value,
        receiverTypeOpt = None(),
        params = ISZ(),
        retType = AST.Typed.b,
        reads = ISZ(),
        requires = ISZ(),
        modifies = ISZ(),
        ensures = ISZ(),
        objectVarInMap = HashMap.empty,
        fieldVarInMap = HashMap.empty,
        localInMap = HashMap.empty,
        posOpt = theorem.posOpt,
        storage = HashMap.empty
      )))
      val csmt2 = smt2
      val logika = Logika(th, config, context, plugins)
      for (tp <- theorem.typeParams) {
        csmt2.addType(config, AST.Typed.TypeVar(tp.id.value, tp.kind), reporter)
      }
      if (theorem.proof.steps.isEmpty) {
        logika.evalAssert(csmt2, cache, T, theorem.id.value, State.create, theorem.claim, theorem.claim.posOpt, ISZ(),
          reporter)
        return reporter.messages
      }
      var p = (State.create, HashSMap.empty[AST.ProofAst.StepId, StepProofContext])
      for (step <- theorem.proof.steps if p._1.ok) {
        p = logika.evalProofStep(csmt2, cache, p, step, reporter)
      }
      if (!p._1.ok) {
        return reporter.messages
      }
      val normClaim: AST.Exp = th.normalizeExp(
        if (theorem.isFun) theorem.claim.asInstanceOf[AST.Exp.Quant].fun.exp.asInstanceOf[AST.Stmt.Expr].exp
        else theorem.claim)
      val spcEntries = p._2.entries
      for (i <- spcEntries.size - 1 to 0 by -1 if spcEntries(i)._2.isInstanceOf[StepProofContext.Regular]) {
        val StepProofContext.Regular(_, _, claim) = spcEntries(i)._2
        if (normClaim == th.normalizeExp(claim)) {
          if (logika.config.detailedInfo) {
            reporter.inform(normClaim.posOpt.get, Logika.Reporter.Info.Kind.Verified,
              st"""Accepted by using ${Plugin.stepNoDesc(F, spcEntries(i)._1)}, i.e.:
                  |
                  |$claim
                  |""".render)
          }
          return reporter.messages
        }
      }
      reporter.error(theorem.id.attr.posOpt, Logika.kind, "The theorem's claim has not been proven")
      return reporter.messages
    }
  }

  @datatype class Stmts(val th: TypeHierarchy,
                        val config: Config,
                        val stmts: ISZ[AST.Stmt],
                        val plugins: ISZ[Plugin]) extends Task {
    override def compute(nameExePathMap: HashMap[String, String], maxCores: Z, fileOptions: LibUtil.FileOptionMap,
                         smt2: Smt2, cache: Logika.Cache, reporter: Reporter): ISZ[Message] = {
      val logika = Logika(th, config, Context.empty(nameExePathMap, maxCores, fileOptions), plugins)
      val csmt2 = smt2
      for (p <- plugins) {
        p match {
          case p: plugin.StmtsPlugin =>
            val (done, ss) = p.handle(th, plugins, stmts, config, csmt2, cache, reporter)
            for (state <- ss if state.ok) {
              if (stmts.nonEmpty && stmts(stmts.size - 1).isInstruction) {
                val lastPos = stmts(stmts.size - 1).posOpt.get
                logika.logPc(state(status = State.Status.End), reporter, Some(lastPos))
              }
            }
            if (done) {
              return reporter.messages
            }
          case _ =>
        }
      }
      for (state <- Util.evalStmts(logika, Logika.Split.Default, csmt2, cache, None(), T, State.create, stmts, reporter) if state.ok) {
        if (stmts.nonEmpty && stmts(stmts.size - 1).isInstruction) {
          val lastPos = stmts(stmts.size - 1).posOpt.get
          logika.logPc(state(status = State.Status.End), reporter, Some(lastPos))
        }
      }
      return reporter.messages
    }
  }

  @record class LineCollector(var set: HashSSet[message.Position]) extends AST.MTransformer {
    def addPosOpt(posOpt: Option[message.Position]): Unit = {
      posOpt match {
        case Some(pos) => set = set + pos
        case _ =>
      }
    }

    override def postAttr(o: Attr): MOption[Attr] = {
      addPosOpt(o.posOpt)
      return MNone()
    }

    override def postTypedAttr(o: TypedAttr): MOption[TypedAttr] = {
      addPosOpt(o.posOpt)
      return MNone()
    }

    override def postResolvedAttr(o: ResolvedAttr): MOption[ResolvedAttr] = {
      addPosOpt(o.posOpt)
      return MNone()
    }
  }

  @datatype class Claim(val th: TypeHierarchy,
                        val config: Config,
                        val title: String,
                        val exp: AST.Exp,
                        val plugins: ISZ[Plugin]) extends Task {
    override def compute(nameExePathMap: HashMap[String, String], maxCores: Z, fileOptions: LibUtil.FileOptionMap,
                         smt2: Smt2, cache: Logika.Cache, reporter: Reporter): ISZ[Message] = {
      val logika = Logika(th, config, Context.empty(nameExePathMap, maxCores, fileOptions), plugins)
      val csmt2 = smt2
      var svs = ISZ[(State, State.Value)]()
      var isPlugin = F
      for (p <- plugins) {
        p match {
          case p: plugin.ExpPlugin =>
            isPlugin = T
            svs = p.handle(logika, Logika.Split.Default, csmt2, cache, T, State.create, exp, reporter)
          case _ =>
        }
      }
      if (!isPlugin) {
        svs = logika.evalExp(Logika.Split.Default, csmt2, cache, T, State.create, exp, reporter)
      }
      for (sv <- svs) {
        val (state, sym) = logika.value2Sym(sv._1, sv._2, exp.posOpt.get)
        logika.evalAssertH(T, csmt2, cache, title, state, sym, exp.posOpt, ISZ(), reporter)
      }
      val lc = LineCollector(HashSSet.empty)
      lc.transformExp(exp)
      for (pos <- lc.set.elements) {
        reporter.coverage(F, conversions.Z.toU64(0), pos)
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
    override def compute(nameExePathMap: HashMap[String, String], maxCores: Z,
                         fileOptions: LibUtil.FileOptionMap,
                         smt2: Smt2, cache: Logika.Cache, reporter: Reporter): ISZ[Message] = {
      val ms = Util.detectUnsupportedFeatures(method)
      if (ms.nonEmpty) {
        reporter.reports(ms)
        return reporter.messages
      }
      val csmt2 = smt2
      for (p <- plugins) {
        p match {
          case p: plugin.MethodPlugin if p.canHandle(th, method) =>
            if (p.handle(nameExePathMap, maxCores, fileOptions, th, plugins, method, caseIndex, config, csmt2, cache, reporter)) {
              return reporter.messages
            }
          case _ =>
        }
      }
      Util.checkMethod(nameExePathMap, maxCores, fileOptions, th, plugins, method, caseIndex, config, csmt2, cache, reporter)
      return reporter.messages
    }
  }

}

