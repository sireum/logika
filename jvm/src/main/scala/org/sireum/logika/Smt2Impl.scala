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

  def create(configs: ISZ[Smt2Config], typeHierarchy: TypeHierarchy, timeoutInMs: Z,
             fpRoundingMode: String, charBitWidth: Z, intBitWidth: Z, useReal: B, simplifiedQuery: B, smt2Seq: B,
             reporter: Logika.Reporter): Smt2 = {
    val r = Smt2Impl(typeHierarchy, timeoutInMs, charBitWidth, intBitWidth, useReal, simplifiedQuery, smt2Seq,
      fpRoundingMode, configs, HashSet.empty[AST.Typed] + AST.Typed.b, Poset.empty, ISZ(), ISZ(), ISZ(), ISZ(), ISZ(),
      ISZ(), HashMap.empty, HashSMap.empty, HashMap.empty, HashSSet.empty, HashSet.empty)
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
                       val smt2Seq: B,
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
                       var seqLits: HashSSet[Smt2.SeqLit],
                       var typeOfSeqSet: HashSet[(String, AST.Typed)]) extends Smt2 {

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

  def typeOfSeqSetUp(newTypeOfSeqSet: HashSet[(String, AST.Typed)]): Unit = {
    typeOfSeqSet = newTypeOfSeqSet
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

  def checkSat(cache: Smt2.Cache, query: String): (B, Smt2Query.Result) = {
    val r = checkQuery(cache, T, query)
    return (r.kind != Smt2Query.Result.Kind.Unsat, r)
  }

  def checkUnsat(cache: Smt2.Cache, query: String): (B, Smt2Query.Result) = {
    val r = checkQuery(cache, F, query)
    return (r.kind == Smt2Query.Result.Kind.Unsat, r)
  }

  def checkQuery(cache: Smt2.Cache, isSat: B, query: String): Smt2Query.Result = {
    return Smt2Invoke.query(configs, cache, isSat, smt2Seq, query, if (isSat) Smt2.satTimeoutInMs else timeoutInMs)
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

  def withConfig(isSat: B, options: String, timeout: Z, resourceLimit: Z, reporter: Logika.Reporter): MEither[Smt2, String] = {
    Smt2.parseConfigs(Smt2Invoke.nameExePathMap(Os.path(Os.env("SIREUM_HOME").get)), isSat, options, timeout,
      resourceLimit) match {
      case Either.Left(smt2Configs) =>
        val thisL = this
        return MEither.Left(thisL(configs = smt2Configs))
      case Either.Right(msg) => return MEither.Right(msg)
    }
  }
}

