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

  @pure def cvc4ArgF(timeoutInMs: Z): ISZ[String] = {
    return ISZ(s"--tlimit=$timeoutInMs", "--lang=smt2.6")
  }
}

@record class Smt2Impl(val configs: ISZ[Smt2Config],
                       val typeHierarchy: TypeHierarchy,
                       val charBitWidth: Z,
                       val intBitWidth: Z,
                       val simplifiedQuery: B)
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

  def writeFile(dir: String, filename: String, content: String): Unit = {
    val p = Os.path(dir)
    if (!p.exists) {
      p.mkdirAll()
    }
    val fname = ops.StringOps(ops.StringOps(ops.StringOps(ops.StringOps(ops.StringOps(ops.StringOps(filename).
      replaceAllLiterally(", ", "-")).replaceAllLiterally(" [", "-")).replaceAllChars(' ', '-')).
      replaceAllChars('[', '-')).replaceAllLiterally("]", "")).toLower
    val f = p / fname
    f.writeOver(content)
    println(s"Wrote $f")
  }

  def checkSat(query: String, timeoutInMsOpt: Option[Z]): (B, Smt2Query.Result) = {
    val r = checkQuery(T, query, timeoutInMsOpt)
    return (r.kind != Smt2Query.Result.Kind.Unsat, r)
  }

  def checkUnsat(query: String, timeoutInMsOpt: Option[Z]): (B, Smt2Query.Result) = {
    val r = checkQuery(F, query, timeoutInMsOpt)
    return (r.kind == Smt2Query.Result.Kind.Unsat, r)
  }

  def checkQuery(firstOnly: B, query: String, timeoutInMsOpt: Option[Z]): Smt2Query.Result = {
    def checkQueryH(config: Smt2Config): Smt2Query.Result = {
      def err(out: String): Unit = {
        halt(
          st"""Error encountered when running ${config.exe} query:
              |$query
              |
              |${config.exe} output:
              |$out""".render)
      }
      //println(s"$exe Query:")
      //println(query)
      val args = config.args(timeoutInMsOpt)
      val pr = Os.proc(config.exe +: args).input(query).redirectErr.run()
      val out = ops.StringOps(pr.out).split(c => c == '\n' || c == '\r')
      if (out.size == 0) {
        err(pr.out)
      }
      val firstLine = out(0)
      val r: Smt2Query.Result = firstLine match {
        case string"sat" => Smt2Query.Result(Smt2Query.Result.Kind.Sat, config.name,
          st"""$query
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}
              |; Result: sat""".render, pr.out)
        case string"unsat" => Smt2Query.Result(Smt2Query.Result.Kind.Unsat, config.name,
          st"""$query
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}
              |; Result: unsat""".render, pr.out)
        case string"timeout" => Smt2Query.Result(Smt2Query.Result.Kind.Timeout, config.name,
          st"""$query
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}
              |; Result: timeout""".render, pr.out)
        case string"unknown" => Smt2Query.Result(Smt2Query.Result.Kind.Unknown, config.name,
          st"""$query
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}
              |; Result: unknown""".render, pr.out)
        case _ => Smt2Query.Result(Smt2Query.Result.Kind.Error, config.name, query, pr.out)
      }
      //println(s"$exe Result (${r.kind}):")
      //println(r.output)
      if (r.kind == Smt2Query.Result.Kind.Error) {
        err(pr.out)
      }

      return r
    }

    for (i <- 0 until configs.size - 1) {
      val r = checkQueryH(configs(i))
      val stop: B = r.kind match {
        case Smt2Query.Result.Kind.Sat => T
        case Smt2Query.Result.Kind.Unsat => T
        case Smt2Query.Result.Kind.Unknown => F
        case Smt2Query.Result.Kind.Timeout => F
        case Smt2Query.Result.Kind.Error => T
      }
      if (firstOnly || stop) {
        return r
      }
    }
    return checkQueryH(configs(configs.size - 1))
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

