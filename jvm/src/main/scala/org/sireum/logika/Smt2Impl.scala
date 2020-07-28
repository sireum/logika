// #Sireum
/*
 Copyright (c) 2020, Robby, Kansas State University
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

object Smt2Impl {
  @pure def z3ArgF(timeoutInMs: Z): ISZ[String] = {
    return ISZ("-smt2", s"-t:$timeoutInMs", "-in")
  }
}

@record class Smt2Impl(val exe: String,
                       argsF: Z => ISZ[String] @pure,
                       val typeHierarchy: TypeHierarchy,
                       val charBitWidth: Z,
                       val intBitWidth: Z)
  extends Smt2 {

  var types: HashSet[AST.Typed] = Smt2.basicTypes

  var poset: Poset[AST.Typed.Name] = Poset.empty

  var sorts: ISZ[ST] = ISZ()

  var adtDecls: ISZ[ST] = ISZ()

  var sTypeDecls: ISZ[ST] = ISZ()

  var typeDecls: ISZ[ST] = ISZ()

  var typeHierarchyIds: ISZ[ST] = ISZ()

  var shortIds: HashMap[ISZ[String], ISZ[String]] = HashMap.empty

  var strictPureMethods: HashSMap[State.ProofFun, (ST, ST)] = HashSMap.empty

  def shortIdsUp(newShortIds: HashMap[ISZ[String], ISZ[String]]): Unit = {
    shortIds = newShortIds
  }

  var seqLits: HashSSet[Smt2.SeqLit] = HashSSet.empty

  def sortsUp(newSorts: ISZ[ST]): Unit = {
    sorts = newSorts
  }

  def adtDeclsUp(newAdtDecls: ISZ[ST]): Unit = {
    adtDecls = newAdtDecls
  }

  def sTypeDeclsUp(newSTypeDecls: ISZ[ST]): Unit = {
    sTypeDecls = newSTypeDecls
  }

  def typeDeclsUp(newTypeDecls: ISZ[ST]): Unit = {
    typeDecls = newTypeDecls
  }

  def typeHierarchyIdsUp(newTypeHierarchyIds: ISZ[ST]): Unit = {
    typeHierarchyIds = newTypeHierarchyIds
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

  def strictPureMethodsUp(newProofFuns: HashSMap[State.ProofFun, (ST, ST)]): Unit = {
    strictPureMethods = newProofFuns
  }

  def checkSat(query: String, timeoutInMs: Z): (B, Smt2Query.Result) = {
    val r = checkQuery(query, timeoutInMs)
    return (r.kind != Smt2Query.Result.Kind.Unsat, r)
  }

  def checkUnsat(query: String, timeoutInMs: Z): (B, Smt2Query.Result) = {
    val r = checkQuery(query, timeoutInMs)
    return (r.kind == Smt2Query.Result.Kind.Unsat, r)
  }

  def checkQuery(query: String, timeoutInMs: Z): Smt2Query.Result = {
    def err(out: String): Unit = {
      halt(
        st"""Error encountered when running $exe query:
            |$query
            |
            |$exe output:
            |$out""".render)
    }
    //println(s"$exe Query:")
    //println(query)
    val pr = Os.proc(exe +: argsF(timeoutInMs)).input(query).redirectErr.run()
    val out = ops.StringOps(pr.out).split(c => c == '\n' || c == '\r')
    if (out.size == 0) {
      err(pr.out)
    }
    val firstLine = out(0)
    val r: Smt2Query.Result = firstLine match {
      case string"sat" => Smt2Query.Result(Smt2Query.Result.Kind.Sat, query, pr.out)
      case string"unsat" => Smt2Query.Result(Smt2Query.Result.Kind.Unsat, query, pr.out)
      case string"timeout" => Smt2Query.Result(Smt2Query.Result.Kind.Timeout, query, pr.out)
      case string"unknown" => Smt2Query.Result(Smt2Query.Result.Kind.Unknown, query, pr.out)
      case _ => Smt2Query.Result(Smt2Query.Result.Kind.Error, query, pr.out)
    }
    //println(s"$exe Result (${r.kind}):")
    //println(r.output)
    if (r.kind == Smt2Query.Result.Kind.Error) {
      err(pr.out)
    }

    return r
  }

  def formatVal(format: String, n: Z): ST = {
    return Smt2Formatter.formatVal(format, n)
  }

  def formatF32(value: F32): ST = {
    return Smt2Formatter.formatF32(value)
  }

  def formatF64(value: F64): ST = {
    return Smt2Formatter.formatF64(value)
  }
}

