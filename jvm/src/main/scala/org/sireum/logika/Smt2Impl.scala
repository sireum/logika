// #Sireum
/*
 Copyright (c) 2017-2023, Robby, Kansas State University
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
import org.sireum.lang.symbol.Info
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy

object Smt2Impl {

  def create(configs: ISZ[Smt2Config], plugins: ISZ[plugin.ClaimPlugin], typeHierarchy: TypeHierarchy, timeoutInMs: Z,
             fpRoundingMode: String, charBitWidth: Z, intBitWidth: Z, useReal: B, simplifiedQuery: B, smt2Seq: B,
             rawInscription: B, elideEncoding: B, includeFreshLines: B, reporter: Logika.Reporter): Smt2 = {
    val r = Smt2Impl(plugins, typeHierarchy, timeoutInMs, charBitWidth, intBitWidth, useReal, simplifiedQuery, smt2Seq,
      fpRoundingMode, rawInscription, elideEncoding, includeFreshLines, configs, HashSet.empty[AST.Typed] + AST.Typed.b,
      Poset.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty,
      HashMap.empty, HashSMap.empty, HashMap.empty, HashSSet.empty)
    r.addType(AST.Typed.z, reporter)
    return r
  }

}

@record class Smt2Impl(val plugins: ISZ[plugin.ClaimPlugin],
                       var typeHierarchy: TypeHierarchy,
                       val timeoutInMs: Z,
                       val charBitWidth: Z,
                       val intBitWidth: Z,
                       val useReal: B,
                       val simplifiedQuery: B,
                       val smt2Seq: B,
                       val fpRoundingMode: String,
                       val rawInscription: B,
                       val elideEncoding: B,
                       val includeFreshLines: B,
                       val configs: ISZ[Smt2Config],
                       var types: HashSet[AST.Typed],
                       var poset: Poset[AST.Typed.Name],
                       var sorts: HashSMap[AST.Typed, ISZ[ST]],
                       var adtDecls: HashSMap[AST.Typed.Name, ISZ[ST]],
                       var sTypeDecls: HashSMap[AST.Typed.Name, ISZ[ST]],
                       var typeDecls: HashSMap[AST.Typed, ISZ[ST]],
                       var constraints: HashSMap[AST.Typed, ISZ[ST]],
                       var typeHierarchyIds: HashSMap[AST.Typed, ST],
                       var shortIds: HashMap[ISZ[String], ISZ[String]],
                       var strictPureMethods: HashSMap[State.ProofFun, (ST, ST)],
                       var filenameCount: HashMap[String, Z],
                       var seqLits: HashSSet[Smt2.SeqLit]) extends Smt2 {

  @pure def emptyCache: Smt2 = {
    val r = Smt2Impl(
      plugins = plugins,
      typeHierarchy = typeHierarchy,
      timeoutInMs = timeoutInMs,
      charBitWidth = charBitWidth,
      intBitWidth = intBitWidth,
      useReal = useReal,
      simplifiedQuery = simplifiedQuery,
      smt2Seq = smt2Seq,
      fpRoundingMode = fpRoundingMode,
      rawInscription = rawInscription,
      elideEncoding = elideEncoding,
      includeFreshLines = includeFreshLines,
      configs = configs,
      types = HashSet.empty[AST.Typed] + AST.Typed.b,
      poset = Poset.empty,
      sorts = HashSMap.empty,
      adtDecls = HashSMap.empty,
      sTypeDecls = HashSMap.empty,
      typeDecls = HashSMap.empty,
      constraints = HashSMap.empty,
      typeHierarchyIds = HashSMap.empty,
      shortIds = shortIds,
      strictPureMethods = HashSMap.empty,
      filenameCount = filenameCount,
      seqLits = HashSSet.empty
    )
    r.addType(AST.Typed.z, Logika.Reporter.create)
    return r
  }

  def typeHierarchyNamesUp(entry : (ISZ[String], Info)): Unit = {
    typeHierarchy = typeHierarchy(nameMap = typeHierarchy.nameMap + entry)
  }

  def combineWith(that: Smt2): Unit = {
    types = types ++ that.types.elements
    poset = poset ++ that.poset
    sorts = sorts ++ (that.sorts -- sorts.keys).entries
    adtDecls = adtDecls ++ (that.adtDecls -- adtDecls.keys).entries
    sTypeDecls = sTypeDecls ++ (that.sTypeDecls -- sTypeDecls.keys).entries
    typeDecls = typeDecls ++ (that.typeDecls -- typeDecls.keys).entries
    constraints = constraints ++ (that.constraints -- constraints.keys).entries
    typeHierarchyIds = typeHierarchyIds ++ (that.typeHierarchyIds -- typeHierarchyIds.keys).entries
    shortIds = shortIds ++ (that.shortIds -- shortIds.keys).entries
    strictPureMethods = strictPureMethods ++ (that.strictPureMethods -- strictPureMethods.keys).entries
    for (p <- that.filenameCount.entries) {
      val count = filenameCount.get(p._1).getOrElse(0)
      if (count < p._2) {
        filenameCount = filenameCount + p
      }
    }
    seqLits = seqLits ++ that.seqLits.elements
  }

  def updateFrom(that: Smt2): Unit = {
    types = that.types
    poset = that.poset
    sorts = that.sorts
    adtDecls = that.adtDecls
    sTypeDecls = that.sTypeDecls
    typeDecls = that.typeDecls
    constraints = that.constraints
    typeHierarchyIds = that.typeHierarchyIds
    shortIds = that.shortIds
    strictPureMethods = that.strictPureMethods
    filenameCount = that.filenameCount
    seqLits = that.seqLits
  }

  def shortIdsUp(newShortIds: HashMap[ISZ[String], ISZ[String]]): Unit = {
    shortIds = newShortIds
  }

  def sortsUp(newSorts: HashSMap[AST.Typed, ISZ[ST]]): Unit = {
    sorts = newSorts
  }

  def adtDeclsUp(newAdtDecls: HashSMap[AST.Typed.Name, ISZ[ST]]): Unit = {
    adtDecls = newAdtDecls
  }

  def sTypeDeclsUp(newSTypeDecls: HashSMap[AST.Typed.Name, ISZ[ST]]): Unit = {
    sTypeDecls = newSTypeDecls
  }

  def typeDeclsUp(newTypeDecls: HashSMap[AST.Typed, ISZ[ST]]): Unit = {
    typeDecls = newTypeDecls
  }

  def constraintsUp(newConstraints: HashSMap[AST.Typed, ISZ[ST]]): Unit = {
    constraints = newConstraints
  }

  def typeHierarchyIdsUp(newTypeHierarchyIds: HashSMap[AST.Typed, ST]): Unit = {
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

    val fname = Smt2Formatter.formatFilename(filename)
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

  def checkSat(cache: Logika.Cache, query: String): (B, Smt2Query.Result) = {
    val r = checkQuery(cache, T, query)
    val b: B = r.kind match {
      case Smt2Query.Result.Kind.Unsat => F
      case Smt2Query.Result.Kind.Sat => T
      case Smt2Query.Result.Kind.Error => F
      case Smt2Query.Result.Kind.Timeout => T
      case Smt2Query.Result.Kind.Unknown => T
    }
    return (b, r)
  }

  def checkUnsat(cache: Logika.Cache, query: String): (B, Smt2Query.Result) = {
    val r = checkQuery(cache, F, query)
    return (r.kind == Smt2Query.Result.Kind.Unsat, r)
  }

  def checkQuery(cache: Logika.Cache, isSat: B, query: String): Smt2Query.Result = {
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

  def formatTime(value: Z): ST = {
    return Smt2Formatter.formatTime(value)
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

