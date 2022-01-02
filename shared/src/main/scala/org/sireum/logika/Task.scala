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
          logika.logPc(config.logPc, config.logRawPc, state, reporter, Some(Util.afterPos(lastPos)))
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

