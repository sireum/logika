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
import org.sireum.lang.symbol.Info
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy

object Smt2Impl {

  def create(config: Config, plugins: ISZ[plugin.ClaimPlugin], typeHierarchy: TypeHierarchy, reporter: Logika.Reporter): Smt2 = {
    val r = Smt2Impl(plugins, typeHierarchy, HashSet.empty[AST.Typed] + AST.Typed.b,
      Poset.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty, HashSMap.empty,
      HashMap.empty, HashSMap.empty, HashMap.empty, HashSSet.empty)
    r.addType(config, AST.Typed.z, reporter)
    return r
  }

}

@record class Smt2Impl(val plugins: ISZ[plugin.ClaimPlugin],
                       var typeHierarchy: TypeHierarchy,
                       var types: HashSet[AST.Typed],
                       var poset: Poset[AST.Typed.Name],
                       var sorts: HashSMap[AST.Typed, ISZ[ST]],
                       var adtDecls: HashSMap[AST.Typed.Name, ISZ[ST]],
                       var sTypeDecls: HashSMap[AST.Typed.Name, ISZ[ST]],
                       var typeDecls: HashSMap[AST.Typed, ISZ[ST]],
                       var constraints: HashSMap[AST.Typed, ISZ[ST]],
                       var typeHierarchyIds: HashSMap[AST.Typed, ST],
                       var shortIds: HashMap[ISZ[String], ISZ[String]],
                       var pureFuns: HashSMap[State.ProofFun, (ST, ST)],
                       var filenameCount: HashMap[String, Z],
                       var seqLits: HashSSet[Smt2.SeqLit]) extends Smt2 {

  def minimize: Smt2 = {
    return this(plugins = ISZ(), typeHierarchy = TypeHierarchy.empty)
  }

  def emptyCache(config: Config): Smt2 = {
    val r = Smt2Impl(
      plugins = plugins,
      typeHierarchy = typeHierarchy,
      types = HashSet.empty[AST.Typed] + AST.Typed.b,
      poset = Poset.empty,
      sorts = HashSMap.empty,
      adtDecls = HashSMap.empty,
      sTypeDecls = HashSMap.empty,
      typeDecls = HashSMap.empty,
      constraints = HashSMap.empty,
      typeHierarchyIds = HashSMap.empty,
      shortIds = shortIds,
      pureFuns = HashSMap.empty,
      filenameCount = filenameCount,
      seqLits = HashSSet.empty
    )
    r.addType(config, AST.Typed.z, message.Reporter.create)
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
    pureFuns = pureFuns ++ (that.pureFuns -- pureFuns.keys).entries
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
    pureFuns = that.pureFuns
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

  def pureFunsUp(newProofFuns: HashSMap[State.ProofFun, (ST, ST)]): Unit = {
    pureFuns = newProofFuns
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

  def checkSat(config: Config, timeOutInMs: Z, query: String): Smt2Query.Result = {
    return checkQuery(config, T, timeOutInMs, query)
  }

  def checkUnsat(config: Config, timeOutInMs: Z, query: String): Smt2Query.Result = {
    return checkQuery(config, F, timeOutInMs, query)
  }

  def checkQuery(config: Config, isSat: B, timeoutInMs: Z, query: String): Smt2Query.Result = {
    return Smt2Invoke.query(config.smt2Configs, isSat, config.smt2Seq, query, timeoutInMs, config.rlimit)
  }

  def formatVal(width: Z, n: Z): ST = {
    return Smt2Formatter.formatVal(width, n)
  }

  def formatF32(config: Config, value: F32): ST = {
    return Smt2Formatter.formatF32(config.useReal, value)
  }

  def formatF64(config: Config, value: F64): ST = {
    return Smt2Formatter.formatF64(config.useReal, value)
  }

  def formatR(value: R): ST = {
    return Smt2Formatter.formatR(value)
  }

  def formatTime(value: Z): ST = {
    return Smt2Formatter.formatTime(value)
  }

}

