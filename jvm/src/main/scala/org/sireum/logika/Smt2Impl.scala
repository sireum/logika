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
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy

object Smt2Impl {

  val timeoutCodes: Set[Z] = Set.empty[Z] ++ ISZ(-101, -100, 1, 6, 132)

  def create(configs: ISZ[Smt2Config], typeHierarchy: TypeHierarchy, timeoutInMs: Z, cvcRLimit: Z,
             fpRoundingMode: String, charBitWidth: Z, intBitWidth: Z, useReal: B, simplifiedQuery: B,
             reporter: Logika.Reporter): Smt2 = {
    val r = Smt2Impl(typeHierarchy, timeoutInMs, charBitWidth, intBitWidth, useReal, simplifiedQuery, cvcRLimit,
      fpRoundingMode, configs, HashSet.empty[AST.Typed] + AST.Typed.b, Poset.empty, ISZ(), ISZ(), ISZ(), ISZ(), ISZ(),
      ISZ(), HashMap.empty, HashSMap.empty, HashMap.empty, HashSSet.empty)
    r.addType(AST.Typed.z, reporter)
    return r
  }
}

@record class Smt2Impl(val typeHierarchy: TypeHierarchy,
                       val timeoutInMs: Z,
                       val charBitWidth: Z,
                       val intBitWidth: Z,
                       val useReal: B,
                       val simplifiedQuery: B,
                       val cvcRLimit: Z,
                       val fpRoundingMode: String,
                       val configs: ISZ[Smt2Config],
                       var types: HashSet[AST.Typed],
                       var poset: Poset[AST.Typed.Name],
                       var sorts: ISZ[ST],
                       var adtDecls: ISZ[ST],
                       var sTypeDecls: ISZ[ST],
                       var typeDecls: ISZ[ST],
                       var constraints: ISZ[ST],
                       var typeHierarchyIds: ISZ[ST],
                       var shortIds: HashMap[ISZ[String], ISZ[String]],
                       var strictPureMethods: HashSMap[State.ProofFun, (ST, ST)],
                       var filenameCount: HashMap[String, Z],
                       var seqLits: HashSSet[Smt2.SeqLit]) extends Smt2 {

 val satArgs: ISZ[String] = {
   var r = ISZ[String]()
   for (config <- configs) {
     r = (r :+ config.exe) ++ config.args(T, timeoutInMs)
   }
   r
 }

  val validArgs: ISZ[String] = {
    var r = ISZ[String]()
    for (config <- configs) {
      r = (r :+ config.exe) ++ config.args(F, timeoutInMs)
    }
    r
  }

 def shortIdsUp(newShortIds: HashMap[ISZ[String], ISZ[String]]): Unit = {
    shortIds = newShortIds
  }

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

  def constraintsUp(newConstraints: ISZ[ST]): Unit = {
    constraints = newConstraints
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

    @strictpure def replaceChar(c: C): C =
      if (('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')) c else '-'

    val fname = conversions.String.fromCis(for (c <- conversions.String.toCis(filename)) yield replaceChar(c))
    val countOpt: Option[ST] = filenameCount.get(fname) match {
      case Some(n) =>
        filenameCount = filenameCount + fname ~> (n + 1)
        Some(st".$n")
      case _ =>
        filenameCount = filenameCount + fname ~> 1
        None()
    }
    val f = p / st"$fname$countOpt.smt2".render
    f.writeOver(content)
    println(s"Wrote $f")
  }

  def checkSat(cache: Smt2.Cache, query: String, timeoutInMs: Z): (B, Smt2Query.Result) = {
    val r = checkQuery(cache, T, query, timeoutInMs)
    return (r.kind != Smt2Query.Result.Kind.Unsat, r)
  }

  def checkUnsat(cache: Smt2.Cache, query: String, timeoutInMs: Z): (B, Smt2Query.Result) = {
    val r = checkQuery(cache, F, query, timeoutInMs)
    return (r.kind == Smt2Query.Result.Kind.Unsat, r)
  }

  def checkQuery(cache: Smt2.Cache, isSat: B, query: String, timeoutInMs: Z): Smt2Query.Result = {
    def checkQueryH(config: Smt2Config): Smt2Query.Result = {
      def err(out: String, exitCode: Z): Unit = {
        halt(
          st"""Error encountered when running ${config.exe} query:
              |$query
              |
              |${config.exe} output (exit code $exitCode):
              |$out""".render)
      }
      //println(s"$exe Query:")
      //println(query)
      val args = config.args(isSat, timeoutInMs)
      var proc = Os.proc(config.exe +: args).input(query).redirectErr
      proc = proc.timeout(timeoutInMs * 2)
      val startTime = extension.Time.currentMillis
      val pr = proc.run()
      val pout: String = pr.out
      val isTimeout: B = Smt2Impl.timeoutCodes.contains(pr.exitCode)
      if (pout.size == 0 && pr.exitCode != 0 && !isTimeout) {
        err(pout, pr.exitCode)
      }
      val duration = extension.Time.currentMillis - startTime
      val out = ops.StringOps(pout).split((c: C) => c.isWhitespace)
      val firstLine: String = if (isTimeout) "timeout" else out(0)
      val r: Smt2Query.Result = firstLine match {
        case string"sat" => Smt2Query.Result(Smt2Query.Result.Kind.Sat, config.name, query,
          st"""; Result: ${if (isSat) "Sat" else "Invalid"}
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case string"unsat" => Smt2Query.Result(Smt2Query.Result.Kind.Unsat, config.name, query,
          st"""; Result: ${if (isSat) "Unsat" else "Valid"}
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case string"timeout" => Smt2Query.Result(Smt2Query.Result.Kind.Timeout, config.name, query,
          st"""; Result: Timeout
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case string"unknown" => Smt2Query.Result(Smt2Query.Result.Kind.Unknown, config.name, query,
          st"""; Result: Don't Know
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case _ => Smt2Query.Result(Smt2Query.Result.Kind.Error, config.name, query,
          st"""; Result: Error
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
      }
      //println(s"$exe Result (${r.kind}):")
      //println(r.output)
      if (r.kind == Smt2Query.Result.Kind.Error) {
        err(pout, pr.exitCode)
      }

      return r
    }
    def checkH(): Smt2Query.Result = {
      for (i <- 0 until configs.size - 1) {
        val r = checkQueryH(configs(i))
        val stop: B = r.kind match {
          case Smt2Query.Result.Kind.Sat => T
          case Smt2Query.Result.Kind.Unsat => T
          case Smt2Query.Result.Kind.Unknown => F
          case Smt2Query.Result.Kind.Timeout => F
          case Smt2Query.Result.Kind.Error => T
        }
        if (isSat || stop) {
          return r
        }
      }
      return checkQueryH(configs(configs.size - 1))
    }
    val args: ISZ[String] = if (isSat) satArgs else validArgs
    cache.get(isSat, query, args) match {
      case Some(r) => return r
      case _ =>
    }
    val r = checkH()
    cache.set(isSat, query, args, r(cached = T, info = ops.StringOps(r.info).replaceAllLiterally("Result:", "Result (cached):")))
    return r
  }

  def formatVal(width: Z, n: Z): ST = {
    return Smt2Formatter.formatVal(width, n)
  }

  def formatF32(value: F32): ST = {
    return Smt2Formatter.formatF32(useReal, value)
  }

  def formatF64(value: F64): ST = {
    return Smt2Formatter.formatF64(useReal, value)
  }

  def formatR(value: R): ST = {
    return Smt2Formatter.formatR(value)
  }
}

