// #Sireum
/*
 Copyright (c) 2019, Robby, Kansas State University
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
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy

object Z3 {
  object Result {
    @enum object Kind {
      'Sat
      'Unsat
      'Unknown
      'Timeout
      'Error
    }
  }

  @datatype class Result(kind: Result.Kind.Type, output: String)

}

@record class Z3(val z3Exe: String,
                 val typeHierarchy: TypeHierarchy)
  extends Smt2 {

  var types: HashSet[AST.Typed] = basicTypes

  var poset: Poset[AST.Typed.Name] = Poset.empty

  var sorts: ISZ[ST] = ISZ()

  var typeDecls: ISZ[ST] = ISZ()

  var typeHierarchyIds: ISZ[ST] = ISZ()

  var typeConstructors: ISZ[ST] = ISZ()

  var seqLits: HashSSet[Smt2.SeqLit] = HashSSet.empty

  def sortsUp(newSorts: ISZ[ST]): Unit = {
    sorts = newSorts
  }

  def typeDeclsUp(newTypeDecls: ISZ[ST]): Unit = {
    typeDecls = newTypeDecls
  }

  def typeHierarchyIdsUp(newTypeHierarchyIds: ISZ[ST]): Unit = {
    typeHierarchyIds = newTypeHierarchyIds
  }

  def typeConstructorsUp(newConstructors: ISZ[ST]): Unit = {
    typeConstructors = newConstructors
  }

  def typesUp(newTypes: HashSet[AST.Typed]): Unit = {
    types = newTypes
  }

  def posetUp(newPoset: Poset[AST.Typed.Name]): Unit = {
    poset = newPoset
  }

  def seqLitsUp(newSeqLits: HashSSet[Smt2.SeqLit]): Unit = {
    seqLits = newSeqLits
  }

  def checkSat(query: String, timeoutInMs: Z): B = {
    return checkQuery(query, timeoutInMs).kind != Z3.Result.Kind.Unsat
  }

  def checkUnsat(query: String, timeoutInMs: Z): B = {
    return checkQuery(query, timeoutInMs).kind == Z3.Result.Kind.Unsat
  }

  def checkQuery(query: String, timeoutInMs: Z): Z3.Result = {
    def err(out: String): Unit = {
      halt(
        st"""Error encountered when running $z3Exe query:
            |$query
            |
            |Z3 output:
            |$out""".render)
    }
    //println(s"Z3 Query:")
    //println(query)
    val pr = Os.proc(ISZ(z3Exe, "-smt2", s"-t:$timeoutInMs", "-in")).input(query).redirectErr.run()
    val out = ops.StringOps(pr.out).split(c => c == '\n' || c == '\r')
    if (out.size == 0) {
      err(pr.out)
    }
    val firstLine = out(0)
    val r: Z3.Result = firstLine match {
      case string"sat" => Z3.Result(Z3.Result.Kind.Sat, pr.out)
      case string"unsat" => Z3.Result(Z3.Result.Kind.Unsat, pr.out)
      case string"timeout" => Z3.Result(Z3.Result.Kind.Timeout, pr.out)
      case string"unknown" => Z3.Result(Z3.Result.Kind.Unknown, pr.out)
      case _ => Z3.Result(Z3.Result.Kind.Error, pr.out)
    }
    //println(s"Z3 Result (${r.kind}):")
    //println(r.output)
    if (r.kind == Z3.Result.Kind.Error) {
      err(pr.out)
    }

    return r
  }
}
