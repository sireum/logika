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
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.Smt2.stTrue

object Smt2 {

  @datatype class SeqLit(t: AST.Typed.Name, size: Z)

  @datatype class AdtFieldInfo(isParam: B,
                               isSpec: B,
                               fieldId: String,
                               fieldLookupId: ST,
                               fieldStoreId: ST,
                               fieldAdtType: ST,
                               fieldType: AST.Typed)

  @datatype class MemPrinter(defs: HashMap[Z, ISZ[State.Claim.Def]]) {
  }

  val basicTypes: HashSet[AST.Typed] = HashSet ++ ISZ[AST.Typed](
    AST.Typed.b,
    AST.Typed.z,
    AST.Typed.c,
    AST.Typed.f32,
    AST.Typed.f64,
    AST.Typed.r,
    AST.Typed.string,
  )

  val imsOps: HashSet[String] =
    HashSet.empty[String] ++
      ISZ(
        AST.Exp.BinaryOp.Append,
        AST.Exp.BinaryOp.AppendAll,
        AST.Exp.BinaryOp.Prepend,
        AST.Exp.BinaryOp.RemoveAll,
      )

  val stTrue: ST = st"true"
  val stFalse: ST = st"false"

  val bvFormats: Map[Z, String] = Map.empty[Z, String] ++ ISZ[(Z, String)](
    8 ~> "#x%02X",
    16 ~> "#x%04X",
    32 ~> "#x%08X",
    64 ~> "#x%016X",
  )

  @strictpure def quotedEscape(s: String): String = ops.StringOps(s).replaceAllChars('|', '│')

}

@msig trait Smt2 {

  def configs: ISZ[Smt2Config]

  def simplifiedQuery: B

  def charBitWidth: Z

  def intBitWidth: Z

  def types: HashSet[AST.Typed]

  def typesUp(newTypes: HashSet[AST.Typed]): Unit

  def poset: Poset[AST.Typed.Name]

  def posetUp(newPoset: Poset[AST.Typed.Name]): Unit

  def sorts: ISZ[ST]

  def sortsUp(newSorts: ISZ[ST]): Unit

  def seqLits: HashSSet[Smt2.SeqLit]

  def seqLitsUp(newSeqLits: HashSSet[Smt2.SeqLit]): Unit

  def addSort(sort: ST): Unit = {
    sortsUp(sorts :+ sort)
  }

  def adtDecls: ISZ[ST]

  def adtDeclsUp(newAdtDecls: ISZ[ST]): Unit

  def typeDecls: ISZ[ST]

  def typeDeclsUp(newTypeDecls: ISZ[ST]): Unit

  def sTypeDecls: ISZ[ST]

  def sTypeDeclsUp(newTypeDecls: ISZ[ST]): Unit

  def strictPureMethods: HashSMap[State.ProofFun, (ST, ST)]

  def strictPureMethodsUp(newProofFuns: HashSMap[State.ProofFun, (ST, ST)]): Unit

  def writeFile(dir: String, filename: String, content: String): Unit

  @strictpure def proofFunId(pf: State.ProofFun): ST =
    if (pf.context.isEmpty) st"|${pf.id}|"
    else st"|${(pf.context, ".")}${if (pf.receiverTypeOpt.isEmpty) "." else "#"}${pf.id}|"

  def injectAdditionalClaims(v: State.Value.Sym, claims: ISZ[State.Claim],
                             additionalClaims: ISZ[State.Claim]): Option[ISZ[State.Claim]] = {
    if (claims.size == 0) {
      return None()
    }
    var newClaims = ISZ[State.Claim]()
    var changed = F
    for (c <- claims) {
      c match {
        case c: State.Claim.And =>
          injectAdditionalClaims(v, c.claims, additionalClaims) match {
            case Some(cs) =>
              newClaims = newClaims :+ State.Claim.And(cs)
              changed = T
            case _ => newClaims = newClaims :+ c
          }
        case c: State.Claim.Imply =>
          injectAdditionalClaims(v, c.claims, additionalClaims) match {
            case Some(cs) =>
              newClaims = newClaims :+ State.Claim.Imply(cs)
              changed = T
            case _ => newClaims = newClaims :+ c
          }
        case c: State.Claim.Or =>
          injectAdditionalClaims(v, c.claims, additionalClaims) match {
            case Some(cs) =>
              newClaims = newClaims :+ State.Claim.Or(cs)
              changed = T
            case _ => newClaims = newClaims :+ c
          }
        case c: State.Claim.If =>
          val newTClaimsOpt = injectAdditionalClaims(v, c.tClaims, additionalClaims)
          val newFClaimsOpt = injectAdditionalClaims(v, c.fClaims, additionalClaims)
          if (newTClaimsOpt.isEmpty && newFClaimsOpt.isEmpty) {
            newClaims = newClaims :+ c
          } else {
            newClaims = newClaims :+ c(tClaims = newTClaimsOpt.getOrElse(c.tClaims), fClaims = newFClaimsOpt.getOrElse(c.fClaims))
            changed = T
          }
        case c: State.Claim.Prop => newClaims = newClaims :+ c
        case c: State.Claim.Def =>
          if (c.sym.num == v.num) {
            newClaims = newClaims :+ State.Claim.And(c +: additionalClaims)
            changed = T
          } else {
            newClaims = newClaims :+ c
          }
        case c: State.Claim.Label => newClaims = newClaims :+ c
      }
    }
    return if (changed) Some(newClaims) else None()
  }

  def addStrictPureMethod(pos: message.Position, pf: State.ProofFun, svs: ISZ[(State, State.Value)],
                          res: State.Value.Sym, statePrefix: Z): Unit = {
    val id = proofFunId(pf)
    var paramTypes: ISZ[ST] = for (pt <- pf.paramTypes) yield typeId(pt)
    var paramIds: ISZ[ST] = for (id <- pf.paramIds) yield currentLocalIdString(id)
    var params: ISZ[ST] = for (p <- ops.ISZOps(paramIds).zip(paramTypes)) yield st"(${p._1} ${p._2})"
    pf.receiverTypeOpt match {
      case Some(receiverType) =>
        val thisType = typeId(receiverType)
        paramTypes = thisType +: paramTypes
        paramIds = st"|l:this|" +: paramIds
        params = st"(|l:this| $thisType)" +: params
      case _ =>
    }
    val decl = st"(declare-fun $id (${(paramTypes, " ")}) ${typeId(pf.returnType)})"

    var claimss = ISZ[ISZ[State.Claim]]()
    for (sv <- svs) {
      val (s0, v) = sv
      val s0Claims = ops.ISZOps(s0.claims).slice(statePrefix, s0.claims.size)
      val acs: ISZ[State.Claim] = ISZ(State.Claim.Let.Eq(res, v))
      v match {
        case v: State.Value.Sym =>
          if (s0.status) {
            claimss = claimss :+ injectAdditionalClaims(v, s0Claims, acs).get
          } else {
            claimss = claimss :+ s0Claims
          }
        case _ =>
          claimss = claimss :+ (s0Claims ++ acs)
      }
    }
    val ecs: ISZ[ST] = {
      val prefixClaims = State.Claim.And(ops.ISZOps(svs(0)._1.claims).slice(0, statePrefix))
      if (prefixClaims.claims.size > 0) {
        for (cs <- claimss) yield embeddedClaims(F, ISZ(State.Claim.Imply(ISZ(prefixClaims, State.Claim.And(cs)))), None())
      } else {
        for (cs <- claimss) yield embeddedClaims(F, ISZ(State.Claim.And(cs)), None())
      }
    }

    val claim: ST = if (ecs.size == 1)
      st"""(assert (forall (${(params, " ")} (|l:Res| ${adtId(pf.returnType)})) (=>
          |  (= |l:Res| ($id ${(paramIds, " ")}))
          |  ${ecs(0)}
          |)))"""
    else
      st"""(assert (forall (${(params, " ")} (|l:Res| ${adtId(pf.returnType)})) (=>
          |  (= |l:Res| ($id ${(paramIds, " ")}))
          |  (and
          |    ${(ecs, "\n")}
          |  )
          |)))"""

    strictPureMethodsUp(strictPureMethods + pf ~> ((decl, claim)))
  }

  def addAdtDecl(adtDecl: ST): Unit = {
    adtDeclsUp(adtDecls :+ adtDecl)
  }

  def addAdtDecls(adtDecls: ISZ[ST]): Unit = {
    adtDeclsUp(this.adtDecls ++ adtDecls)
  }

  def addSTypeDecl(sTypeDecl: ST): Unit = {
    sTypeDeclsUp(sTypeDecls :+ sTypeDecl)
  }

  def addSTypeDecls(sTypeDecls: ISZ[ST]): Unit = {
    sTypeDeclsUp(this.sTypeDecls ++ sTypeDecls)
  }

  def addTypeDecl(typeDecl: ST): Unit = {
    typeDeclsUp(typeDecls :+ typeDecl)
  }

  def addTypeDecls(typeDecls: ISZ[ST]): Unit = {
    typeDeclsUp(this.typeDecls ++ typeDecls)
  }

  def typeHierarchyIds: ISZ[ST]

  def typeHierarchyIdsUp(newTypeHierarchyIds: ISZ[ST]): Unit

  def addTypeHiearchyId(tId: ST): Unit = {
    typeHierarchyIdsUp(typeHierarchyIds :+ tId)
  }

  def shortIds: HashMap[ISZ[String], ISZ[String]]

  def shortIdsUp(newShortIds: HashMap[ISZ[String], ISZ[String]]): Unit

  def addShortIds(ids: ISZ[String], shortenedIds: ISZ[String]): Unit = {
    shortIdsUp(shortIds + ids ~> shortenedIds)
  }

  def addSeqLit(t: AST.Typed.Name, n: Z): Unit = {
    seqLitsUp(seqLits + Smt2.SeqLit(t, n))
  }

  def typeHierarchy: TypeHierarchy

  def checkSat(query: String, timeoutInMsOpt: Option[Z]): (B, Smt2Query.Result)

  def checkUnsat(query: String, timeoutInMsOpt: Option[Z]): (B, Smt2Query.Result)

  def formatVal(format: String, n: Z): ST

  def formatF32(value: F32): ST

  def formatF64(value: F64): ST

  @memoize def adtId(tipe: AST.Typed): ST = {
    @pure def isAdt(t: AST.Typed.Name): B = {
      typeHierarchy.typeMap.get(t.ids).get match {
        case _: TypeInfo.Adt => return T
        case _: TypeInfo.Sig =>
          if (Smt2.basicTypes.contains(t)) {
            return F
          } else if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
            return F
          }
          return T
        case _ => return F
      }
    }
    tipe match {
      case tipe: AST.Typed.Name if isAdt(tipe) => return st"ADT"
      case _ => typeId(tipe)
    }
  }

  @memoize def typeOpId(tipe: AST.Typed, op: String): ST = {
    return st"|${typeIdRaw(tipe)}.${Smt2.quotedEscape(op)}|"
  }

  @memoize def adtTypeOpId(t: AST.Typed, op: String): ST = {
    return if (adtId(t).render == "ADT") st"|ADT.${Smt2.quotedEscape(op)}|" else typeOpId(t, op)
  }

  @memoize def globalId(owner: ISZ[String], id: String): ST = {
    return st"|g:${(shorten(owner), ".")}.$id|"
  }

  def sat(log: B, logDirOpt: Option[String], title: String, pos: message.Position, claims: ISZ[State.Claim],
          reporter: Reporter): B = {
    val headers = st"Satisfiability Check for $title:" +: State.Claim.claimsSTs(claims, ClaimDefs.empty)
    val (r, res) = checkSat(satQuery(headers, claims, None(), reporter).render, Some(500))
    reporter.query(pos, res)
    if (log) {
      reporter.info(None(), Logika.kind,
        st"""Satisfiability: ${res.kind}
            |  ${res.query}""".render)
    }
    logDirOpt match {
      case Some(logDir) =>
        val filename: String =
          if (ops.StringOps(title).contains("[")) s"sat-$title"
          else s"sat-$title-at-${pos.beginLine}-${pos.beginColumn}"
        writeFile(logDir, filename, res.query)
      case _ =>
    }
    return r
  }

  def toVal(t: AST.Typed.Name, n: Z): ST = {
    val bw: Z = if (t == AST.Typed.z) {
      intBitWidth
    } else {
      val ast = typeHierarchy.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.SubZ].ast
      if (!ast.isBitVector) intBitWidth else ast.bitWidth
    }
    return if (bw == 0) if (n < 0) st"(- ${n * -1})" else st"$n"
    else formatVal(Smt2.bvFormats.get(bw).get, n)
  }

  def addType(tipe: AST.Typed, reporter: Reporter): Unit = {
    def addS(t: AST.Typed.Name): Unit = {
      val it = t.args(0).asInstanceOf[AST.Typed.Name]
      addType(it, reporter)
      val et = t.args(1)
      addType(et, reporter)
      val tId = typeId(t)
      val itId = typeId(it)
      val etId = adtId(et)
      val atId = typeOpId(t, "at")
      val sizeId = typeOpId(t, "size")
      val appendId = typeOpId(t, ":+")
      val appendsId = typeOpId(t, "++")
      val prependId = typeOpId(t, "+:")
      val upId = typeOpId(t, "up")
      val eqId = typeOpId(t, "==")
      val isInBoundId = typeOpId(t, "isInBound")
      val itLeId = typeOpId(it, "<=")
      val itGeId = typeOpId(it, ">=")
      val itEqId = typeOpId(it, "==")
      val itAddId = typeOpId(it, "+")
      val itSubId = typeOpId(it, "-")
      val it2zId = typeOpId(it, "toZ")
      val firstIndexId = typeOpId(t, "firstIndex")
      val lastIndexId = typeOpId(t, "lastIndex")
      val zZero = toVal(AST.Typed.z, 0)
      val zOne = toVal(AST.Typed.z, 1)
      val itOne = toVal(it, 1)
      val itMin: ST = toVal(it, 0)
      addSTypeDecl(st"(define-sort $tId () (Array $itId $etId))")
      addSTypeDecl(st"(declare-fun $sizeId ($tId) Z)")
      addSTypeDecl(st"(assert (forall ((x $tId)) ($itGeId ($sizeId x) $zZero)))")
      addSTypeDecl(st"(define-fun $firstIndexId ((s $tId)) $itId $itMin)")
      addSTypeDecl(st"(declare-fun $lastIndexId ($tId) $itId)")
      val zSubId = typeOpId(AST.Typed.z, "-")
      if (it == AST.Typed.z) {
        addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not (|Z.==| ($sizeId x) $zZero)) (= ($lastIndexId x) ($zSubId ($sizeId x) $zOne)))))")
      } else {
        addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not (|Z.==| ($sizeId x) $zZero)) (= ($it2zId ($lastIndexId x)) ($zSubId ($sizeId x) $zOne)))))")
      }
      addSTypeDecl(st"(define-fun $isInBoundId ((x $tId) (y $itId)) B (and ($itGeId ($sizeId x) $zOne) ($itLeId ($firstIndexId x) y) ($itLeId y ($lastIndexId x))))")
      addSTypeDecl(st"(define-fun $atId ((x $tId) (y $itId)) $etId (select x y))")
      addSTypeDecl(
        st"""(define-fun $appendId ((x $tId) (y $etId) (z $tId)) B
            |  (and
            |    ($itEqId ($sizeId z) ($itAddId ($sizeId x) $zOne))
            |    ($itEqId ($lastIndexId z) ($itAddId ($lastIndexId x) $itOne))
            |    (forall ((i $itId)) (=> ($isInBoundId x i)
            |                        (= ($atId z i) ($atId x i))))
            |    (= ($atId z ($lastIndexId z)) y)))""")
      addSTypeDecl(
        st"""(define-fun $appendsId ((x $tId) (y $tId) (z $tId)) B
            |  (and
            |    (= ($sizeId z) (+ ($sizeId x) ($sizeId y)))
            |    ($itEqId ($lastIndexId z) ($itAddId ($lastIndexId x) ($itSubId ($lastIndexId y) ($firstIndexId y))))
            |    (forall ((i $itId)) (=> ($isInBoundId x i)
            |                            (= ($atId z i) ($atId x i))))
            |    (forall ((i $itId)) (=> ($isInBoundId y i)
            |                            (= ($atId z ($itAddId ($itAddId ($lastIndexId x) ($itSubId i ($firstIndexId y))) $itOne)) ($atId y i))))))""")
      addSTypeDecl(
        st"""(define-fun $prependId ((x $etId) (y $tId) (z $tId)) B
            |  (and
            |    (= ($sizeId z) (+ ($sizeId y) 1))
            |    ($itEqId ($lastIndexId z) ($itAddId ($lastIndexId y) $itOne))
            |    (forall ((i $itId)) (=> ($isInBoundId y i)
            |                            (= ($atId z ($itAddId i $itOne)) ($atId y i))))
            |    (= ($atId z ($firstIndexId z)) x)))""")
      addSTypeDecl(
        st"""(define-fun $upId ((x $tId) (y $itId) (z $etId) (x2 $tId)) B
            |  (and
            |    (= ($sizeId x2) ($sizeId x))
            |    ($itEqId ($lastIndexId x2) ($lastIndexId x))
            |    (= x2 (store x y z))))""")
      addSTypeDecl(
        st"""(define-fun $eqId ((x $tId) (y $tId)) B
            |  (and
            |    (= ($sizeId x) ($sizeId y))
            |    ($itEqId ($lastIndexId x) ($lastIndexId y))
            |    (forall ((i $itId)) (=> (and (<= 0 i) (< i ($sizeId x))) (= (select x i) (select y i))))))""")
      if (isAdtType(et)) {
        addSTypeDecl(
          st"""(assert (forall ((x $tId) (i $itId) (v ADT))
              |  (=> ($isInBoundId x i)
              |      (= ($atId x i) v)
              |      (sub-type (type-of v) ${typeHierarchyId(et)}))))""")
      }
    }

    def addSub(isRoot: B,
               t: AST.Typed.Name,
               tTypeParams: ISZ[AST.TypeParam],
               tId: ST,
               parents: ISZ[AST.Typed.Name]): HashMap[String, AST.Typed] = {
      @pure def sortName(names: ISZ[ISZ[String]]): ISZ[ISZ[String]] = {
        return ops.ISZOps(names).sortWith((n1, n2) => st"${(n1, ".")}".render <= st"${(n2, ".")}".render)
      }

      val rep = Reporter.create
      val tsm = TypeChecker.buildTypeSubstMap(t.ids, None(), tTypeParams, t.args, rep).get
      assert(!rep.hasMessage)
      for (parent <- parents) {
        addType(parent.subst(tsm), reporter)
      }
      if (isRoot) {
        var children = ISZ[AST.Typed.Name]()
        for (sub <- sortName(typeHierarchy.poset.childrenOf(t.ids).elements)) {
          val (parents, tpSize, tipe): (ISZ[AST.Typed.Name], Z, AST.Typed.Name) = typeHierarchy.typeMap.get(sub).get match {
            case childTi: TypeInfo.Adt => (childTi.parents, childTi.ast.typeParams.size, childTi.tpe)
            case childTi: TypeInfo.Sig => (childTi.parents, childTi.ast.typeParams.size, childTi.tpe)
            case _ => halt(s"Infeasible: $sub")
          }
          for (parent <- parents if parent.ids == t.ids) {
            val sm = TypeChecker.unify(typeHierarchy, None(), TypeChecker.TypeRelation.Equal, t, parent, reporter).get
            assert(sm.size == tpSize)
            val childT = tipe.subst(sm)
            children = children :+ childT
            addType(childT, reporter)
          }
        }
        posetUp(poset.addChildren(t, children))
        addTypeDecls(for (child <- children) yield st"(assert (sub-type ${typeHierarchyId(child)} $tId))")
      }
      return tsm
    }

    def addAdt(t: AST.Typed.Name, ti: TypeInfo.Adt): Unit = {
      for (arg <- t.args) {
        addType(arg, reporter)
      }
      for (v <- ti.vars.values) {
        addType(v.typedOpt.get, reporter)
      }
      for (v <- ti.specVars.values) {
        addType(v.typedOpt.get, reporter)
      }
      posetUp(poset.addNode(t))
      val tId = typeId(t)
      addAdtDecl(st"(define-sort $tId () ADT)")
      val thId = typeHierarchyId(t)
      addTypeHiearchyId(thId)
      addAdtDecl(st"(declare-const $thId Type)")
      if (!ti.ast.isRoot) {
        addAdtDecl(st"(assert (forall ((x ${typeId(t)})) (= (sub-type (type-of x) $thId) (= (type-of x) $thId))))")
      }
      val sm = addSub(ti.ast.isRoot, t, ti.ast.typeParams, thId, ti.parents)

      @pure def fieldInfo(isParam: B, f: Info.Var): Smt2.AdtFieldInfo = {
        val ft = f.typedOpt.get.subst(sm)
        val id = f.ast.id.value
        return Smt2.AdtFieldInfo(isParam, F, id, typeOpId(t, id), typeOpId(t, s"${id}_="), adtId(ft), ft)
      }

      @pure def specFieldInfo(f: Info.SpecVar): Smt2.AdtFieldInfo = {
        val ft = f.typedOpt.get.subst(sm)
        val id = f.ast.id.value
        return Smt2.AdtFieldInfo(F, T, id, typeOpId(t, id), typeOpId(t, s"${id}_="), adtId(ft), ft)
      }

      if (ti.ast.isRoot) {
        var leaves: ISZ[ST] = ISZ()
        for (child <- poset.childrenOf(t).elements) {
          typeHierarchy.typeMap.get(child.ids) match {
            case Some(info: TypeInfo.Adt) if !info.ast.isRoot => leaves = leaves :+ typeHierarchyId(child)
            case _ =>
          }
        }
        if (leaves.isEmpty) {
          reporter.warn(ti.ast.posOpt, Logika.kind, s"$t does not have any concrete implementation")
        } else {
          addAdtDecl(
            st"""(assert (forall ((x $tId))
                |  (let ((t (type-of x)))
                |  (=> (sub-type t $thId)
                |      (or
                |        ${(for (leaf <- leaves) yield st"(= t $leaf)", "\n")})))))"""
          )
        }
      } else {
        val newId = typeOpId(t, "new")
        val eqId = typeOpId(t, "==")
        val neId = typeOpId(t, "!=")
        val params = HashSet.empty[String] ++ (for (p <- ti.ast.params) yield p.id.value)
        val fieldInfos: ISZ[Smt2.AdtFieldInfo] =
          (for (f <- ti.vars.values) yield fieldInfo(params.contains(f.ast.id.value), f)) ++ (for (f <- ti.specVars.values) yield specFieldInfo(f))
        for (q <- fieldInfos) {
          addTypeDecl(st"(declare-fun ${q.fieldLookupId} ($tId) ${q.fieldAdtType})")
        }
        for (q <- fieldInfos) {
          val upOp = typeOpId(t, s"${q.fieldId}_=")
          val feqs: ISZ[ST] = for (q2 <- fieldInfos) yield
            if (q2.fieldId == q.fieldId) st"(= (${q2.fieldLookupId} x!2) x!1)"
            else st"(= (${q2.fieldLookupId} x!2) (${q2.fieldLookupId} x!0))"
          addTypeDecl(
            st"""(define-fun $upOp ((x!0 $tId) (x!1 ${q.fieldAdtType}) (x!2 $tId)) B
                |  (and
                |    (= (type-of x!2) (type-of x!0))
                |    ${(feqs, "\n")}
                |  )
                |)"""
          )
        }
        addTypeDecl(
          st"""(define-fun $newId (${(for (q <- fieldInfos if q.isParam) yield st"(${q.fieldId} ${q.fieldAdtType})", " ")} (x!0 $tId)) B
              |  (and
              |    (= (type-of x!0) $thId)
              |    ${(for (q <- fieldInfos if q.isParam) yield st"(= (${q.fieldLookupId} x!0) ${q.fieldId})", "\n")}))""")
        addTypeDecl(
          st"""(define-fun $eqId ((x!0 $tId) (x!1 $tId)) B
              |  (and
              |    (= (type-of x!0) (type-of x!1) $thId)
              |    ${(for (q <- fieldInfos) yield st"(${if (q.fieldAdtType.render == "ADT") st"|ADT.==|" else typeOpId(q.fieldType, "==")} (${q.fieldLookupId} x!0) (${q.fieldLookupId} x!1))", "\n")}))"""
        )
        addTypeDecl(st"""(define-fun $neId ((x $tId) (y $tId)) B (not ($eqId x y)))""")
      }
    }

    def addSig(t: AST.Typed.Name, ti: TypeInfo.Sig): Unit = {
      for (arg <- t.args) {
        addType(arg, reporter)
      }
      posetUp(poset.addNode(t))
      addTypeDecl(st"(define-sort ${typeId(t)} () ADT)")
      val tId = typeHierarchyId(t)
      addTypeHiearchyId(tId)
      addTypeDecl(st"(declare-const $tId Type)")
      addSub(T, t, ti.ast.typeParams, tId, ti.parents)
    }

    def addSubZ(t: AST.Typed.Name, ti: TypeInfo.SubZ): Unit = {
      val tId = typeId(t)
      val tNegId = typeOpId(t, "unary_-")
      val tCompId = typeOpId(t, "unary_~")
      val tLeId = typeOpId(t, "<=")
      val tLtId = typeOpId(t, "<")
      val tGeId = typeOpId(t, ">=")
      val tGtId = typeOpId(t, ">")
      val tEqId = typeOpId(t, "==")
      val tNeId = typeOpId(t, "!=")
      val tAddId = typeOpId(t, "+")
      val tSubId = typeOpId(t, "-")
      val tMulId = typeOpId(t, "*")
      val tDivId = typeOpId(t, "/")
      val tRemId = typeOpId(t, "%")
      val tShlId = typeOpId(t, "<<")
      val tShrId = typeOpId(t, ">>")
      val tUshrId = typeOpId(t, ">>>")
      (ti.ast.isSigned, ti.ast.isBitVector) match {
        case (T, T) =>
          addTypeDecl(
            st"""(define-sort $tId () (_ BitVec ${ti.ast.bitWidth}))
                 |(define-fun $tNegId ((x $tId)) $tId (bvneg x))
                 |(define-fun $tCompId ((x $tId)) $tId (bvnot x))
                 |(define-fun $tLeId ((x $tId) (y $tId)) B (bvsle x y))
                 |(define-fun $tLtId ((x $tId) (y $tId)) B (bvslt x y))
                 |(define-fun $tGtId ((x $tId) (y $tId)) B (bvsgt x y))
                 |(define-fun $tGeId ((x $tId) (y $tId)) B (bvsge x y))
                 |(define-fun $tEqId ((x $tId) (y $tId)) B (= x y))
                 |(define-fun $tNeId ((x $tId) (y $tId)) B (not (= x y)))
                 |(define-fun $tAddId ((x $tId) (y $tId)) $tId (bvadd x y))
                 |(define-fun $tSubId ((x $tId) (y $tId)) $tId (bvsub x y))
                 |(define-fun $tMulId ((x $tId) (y $tId)) $tId (bvmul x y))
                 |(define-fun $tDivId ((x $tId) (y $tId)) $tId (bvsdiv x y))
                 |(define-fun $tRemId ((x $tId) (y $tId)) $tId (bvsrem x y))
                 |(define-fun $tShlId ((x $tId) (y $tId)) $tId (bvshl x y))
                 |(define-fun $tShrId ((x $tId) (y $tId)) $tId (bvashr x y))
                 |(define-fun $tUshrId ((x $tId) (y $tId)) $tId (bvlshr x y))""")
        case (F, T) =>
          addTypeDecl(
            st"""(define-sort $tId () (_ BitVec ${ti.ast.bitWidth}))
                |(define-fun $tNegId ((x $tId)) $tId (bvneg x))
                |(define-fun $tCompId ((x $tId)) $tId (bvnot x))
                |(define-fun $tLeId ((x $tId) (y $tId)) B (bvule x y))
                |(define-fun $tLtId ((x $tId) (y $tId)) B (bvult x y))
                |(define-fun $tGtId ((x $tId) (y $tId)) B (bvugt x y))
                |(define-fun $tGeId ((x $tId) (y $tId)) B (bvuge x y))
                |(define-fun $tEqId ((x $tId) (y $tId)) B (= x y))
                |(define-fun $tNeId ((x $tId) (y $tId)) B (not (= x y)))
                |(define-fun $tAddId ((x $tId) (y $tId)) $tId (bvadd x y))
                |(define-fun $tSubId ((x $tId) (y $tId)) $tId (bvsub x y))
                |(define-fun $tMulId ((x $tId) (y $tId)) $tId (bvmul x y))
                |(define-fun $tDivId ((x $tId) (y $tId)) $tId (bvudiv x y))
                |(define-fun $tRemId ((x $tId) (y $tId)) $tId (bvurem x y))
                |(define-fun $tShlId ((x $tId) (y $tId)) $tId (bvshl x y))
                |(define-fun $tShrId ((x $tId) (y $tId)) $tId (bvlshr x y))
                |(define-fun $tUshrId ((x $tId) (y $tId)) $tId (bvlshr x y))""")
        case (_, _) =>
          addTypeDecl(
            st"""(define-sort $tId () Int)
                |(define-fun $tNegId ((x $tId)) $tId (- x))
                |(define-fun $tLeId ((x $tId) (y $tId)) B (<= x y))
                |(define-fun $tLtId ((x $tId) (y $tId)) B (< x y))
                |(define-fun $tGtId ((x $tId) (y $tId)) B (> x y))
                |(define-fun $tGeId ((x $tId) (y $tId)) B (>= x y))
                |(define-fun $tEqId ((x $tId) (y $tId)) B (= x y))
                |(define-fun $tNeId ((x $tId) (y $tId)) B (not (= x y)))
                |(define-fun $tAddId ((x $tId) (y $tId)) Z (+ x y))
                |(define-fun $tSubId ((x $tId) (y $tId)) Z (- x y))
                |(define-fun $tMulId ((x $tId) (y $tId)) Z (* x y))
                |(define-fun $tDivId ((x $tId) (y $tId)) Z (div x y))
                |(define-fun $tRemId ((x $tId) (y $tId)) Z (mod x y))""")
      }
    }

    def addEnum(t: AST.Typed.Name, ti: TypeInfo.Enum): Unit = {
      val tid = typeId(t)
      val owner = ops.ISZOps(ti.name).dropRight(1)
      val eqOp = typeOpId(t, "==")
      val neOp = typeOpId(t, "!=")
      val ordinalOp = typeOpId(t, "ordinal")
      addTypeDecl(
        st"""(declare-datatypes (($tid 0)) ((
            |  ${(for (element <- ti.elements.keys) yield st"(${typeHierarchyId(AST.Typed.Name(t.ids :+ element, ISZ()))})", " ")})))
            |(declare-fun $ordinalOp ($tid) Int)
            |(define-fun $eqOp ((x $tid) (y $tid)) B (= x y))
            |(define-fun $neOp ((x $tid) (y $tid)) B (not (= x y)))""")
      val elements: ISZ[ST] = for (element <- ti.elements.keys) yield enumId(owner, element)
      var ordinal = 0
      for (element <- elements) {
        addTypeDecl(st"(declare-const $element $tid)")
        addTypeDecl(st"(assert (= ($ordinalOp $element) $ordinal))")
        ordinal = ordinal + 1
      }
      if (elements.size > 1) {
        addTypeDecl(st"(assert (distinct ${(elements, " ")}))")
      }
    }

    def addTypeVar(t: AST.Typed.TypeVar): Unit = {
      val tid = typeId(t)
      addTypeDecl(st"(declare-sort $tid 0)")
      val eqId = typeOpId(t, "==")
      val neId = typeOpId(t, "!=")
      addTypeDecl(
        st"""(define-fun $eqId ((x $tid) (y $tid)) B (= x y))
            |(define-fun $neId ((x $tid) (y $tid)) B (not (= x y)))"""
      )
    }

    def addTuple(t: AST.Typed.Tuple): Unit = {
      for (arg <- t.args) {
        addType(arg, reporter)
      }
      val tId = typeId(t)
      val eqOp = typeOpId(t, "==")
      val neOp = typeOpId(t, "!=")
      addTypeDecl(
        st"""(declare-datatypes (($tId 0)) (((${typeOpId(t, "new")} ${(for (i <- 1 to t.args.size) yield st"(${typeOpId(t, s"_$i")} ${adtId(t.args(i - 1))})", " ")}))))
            |(define-fun $eqOp ((x $tId) (y $tId)) B
            |  (and
            |    ${(for (i <- 1 to t.args.size) yield st"(${adtTypeOpId(t.args(i - 1), "==")} (${typeOpId(t, s"_$i")} x) (${typeOpId(t, s"_$i")} y))", "\n")}
            |  )
            |)
            |(define-fun $neOp ((x $tId) (y $tId)) B (not ($eqOp x y)))""")
    }

    if (types.contains(tipe)) {
      return
    }
    typesUp(types + tipe)
    tipe match {
      case t: AST.Typed.Name =>
        if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
          addS(t)
        } else {
          typeHierarchy.typeMap.get(t.ids).get match {
            case ti: TypeInfo.Adt => addAdt(t, ti)
            case ti: TypeInfo.Sig => addSig(t, ti)
            case ti: TypeInfo.SubZ => addSubZ(t, ti)
            case ti: TypeInfo.Enum => addEnum(t, ti)
            case _ => halt(s"Infeasible: $t")
          }
        }
      case t: AST.Typed.TypeVar => addTypeVar(t)
      case t: AST.Typed.Tuple => addTuple(t)
      case _ => halt(s"TODO: $tipe") // TODO
    }
  }

  @memoize def seqLit2SmtDeclString(seqLit: Smt2.SeqLit): String = {
    val t = seqLit.t
    val size = seqLit.size
    val it = t.args(0).asInstanceOf[AST.Typed.Name]
    val et = t.args(1)
    val tId = typeId(t)
    val itId = typeId(it)
    val etId = adtId(et)
    val seqLitId = typeOpId(t, s"new.$size")
    val atId = typeOpId(t, "at")
    val sizeId = typeOpId(t, "size")
    val itEqId = typeOpId(it, "==")
    val lastIndexOpt: Option[ST] =
      if (size != 0) Some(st"($itEqId (${typeOpId(t, "lastIndex")} x) ${toVal(it, size - 1)})") else None()
    val r =
      st"""(define-fun $seqLitId (${(for (i <- 0 until size) yield st"(i$i $itId) (v$i $etId)", " ")} (x $tId)) B
          |  (and
          |    (= ($sizeId x) $size)
          |    $lastIndexOpt
          |    ${(for (i <- 0 until size) yield st"(= ($atId x i$i) v$i)", "\n")}))"""
    return r.render
  }

  def satQuery(headers: ISZ[ST], claims: ISZ[State.Claim], negClaimOpt: Option[State.Claim], reporter: Reporter): ST = {
    for (c <- claims; t <- c.types) {
      addType(t, reporter)
    }
    var decls: HashSMap[String, ST] = HashSMap.empty[String, ST] ++
      (for (c <- claims; p <- c2DeclST(c)) yield p)
    val lets = StateUtil.collectLetClaims(simplifiedQuery, claims)
    val sv2ST = StateUtil.value2ST(this, lets)
    var claimSmts = ISZ[String]()
    for (c <- claims) {
      c2ST(c, sv2ST, lets) match {
        case Some(st) => claimSmts = claimSmts :+ st.render
        case _ =>
      }
    }
    negClaimOpt match {
      case Some(negClaim) =>
        claimSmts = claimSmts :+ st"(not ${c2ST(negClaim, sv2ST, lets)})".render
        decls = decls ++ c2DeclST(negClaim)
      case _ =>
    }
    val seqLitDecls: ISZ[String] = for (seqLit <- seqLits.elements) yield seqLit2SmtDeclString(seqLit)
    return query(headers, seqLitDecls ++ (for (d <- decls.values) yield d.render), claimSmts)
  }

  def valid(log: B, logDirOpt: Option[String], title: String, pos: message.Position, premises: ISZ[State.Claim],
            conclusion: State.Claim, reporter: Reporter): Smt2Query.Result = {
    val defs = ClaimDefs.empty
    val ps = State.Claim.claimsSTs(premises, defs)
    val headers = (st"Validity Check for $title:" +: ps :+ st"⊢") ++ State.Claim.claimsSTs(ISZ(conclusion), defs)
    val (r, res) = checkUnsat(satQuery(headers, premises, Some(conclusion), reporter).render, None())
    reporter.query(pos, res)
    if (log) {
      reporter.info(None(), Logika.kind,
        st"""Verification Condition: ${if (r) s"Discharged (${res.kind})" else "Undischarged"}
            |  ${res.query}""".render)
    }
    logDirOpt match {
      case Some(logDir) =>
        val filename: String =
          if (ops.StringOps(title).contains("[")) s"vc-$title"
          else s"vc-$title-at-${pos.beginLine}-${pos.beginColumn}"
        writeFile(logDir, filename, res.query)
      case _ =>
    }
    return res
  }

  def isAdtType(t: AST.Typed): B = {
    return adtId(t).render == "ADT"
  }

  def query(headers: ISZ[ST], decls: ISZ[String], claims: ISZ[String]): ST = {
    val distinctOpt: Option[ST] =
      if (typeHierarchyIds.size <= 1) None()
      else Some(
        st"""(assert (distinct
            |  ${(typeHierarchyIds, "\n")}))""")

    var adtEqs = ISZ[ST]()
    for (t <- poset.nodes.keys) {
      typeHierarchy.typeMap.get(t.ids) match {
        case Some(info: TypeInfo.Adt) if !info.ast.isRoot =>
          adtEqs = adtEqs :+ st"(=> (= t ${typeHierarchyId(t)}) (${typeOpId(t, "==")} x y))"
        case _ =>
      }
    }
    val zST: ST =
      if (intBitWidth == 0)
        st"""(define-sort Z () Int)
            |(define-fun |Z.unary_-| ((x Z)) Z (- x))
            |(define-fun |Z.<=| ((x Z) (y Z)) B (<= x y))
            |(define-fun |Z.<| ((x Z) (y Z)) B (< x y))
            |(define-fun |Z.>| ((x Z) (y Z)) B (> x y))
            |(define-fun |Z.>=| ((x Z) (y Z)) B (>= x y))
            |(define-fun |Z.==| ((x Z) (y Z)) B (= x y))
            |(define-fun |Z.!=| ((x Z) (y Z)) B (not (= x y)))
            |(define-fun |Z.+| ((x Z) (y Z)) Z (+ x y))
            |(define-fun |Z.-| ((x Z) (y Z)) Z (- x y))
            |(define-fun |Z.*| ((x Z) (y Z)) Z (* x y))
            |(define-fun |Z./| ((x Z) (y Z)) Z (div x y))
            |(define-fun |Z.%| ((x Z) (y Z)) Z (mod x y))"""
      else
        st"""(define-sort Z () (_ BitVec $intBitWidth))
            |(define-fun |Z.unary_-| ((x Z)) Z (bvneg x))
            |(define-fun |Z.<=| ((x Z) (y Z)) B (bvsle x y))
            |(define-fun |Z.<| ((x Z) (y Z)) B (bvslt x y))
            |(define-fun |Z.>| ((x Z) (y Z)) B (bvsgt x y))
            |(define-fun |Z.>=| ((x Z) (y Z)) B (bvsge x y))
            |(define-fun |Z.==| ((x Z) (y Z)) B (= x y))
            |(define-fun |Z.!=| ((x Z) (y Z)) B (not (= x y)))
            |(define-fun |Z.+| ((x Z) (y Z)) Z (bvadd x y))
            |(define-fun |Z.-| ((x Z) (y Z)) Z (bvsub x y))
            |(define-fun |Z.*| ((x Z) (y Z)) Z (bvmul x y))
            |(define-fun |Z./| ((x Z) (y Z)) Z (bvsdiv x y))
            |(define-fun |Z.%| ((x Z) (y Z)) Z (bvsrem x y))"""
    val r =
      st"""${(for (header <- headers; line <- ops.StringOps(header.render).split(c => c == '\n')) yield st"; $line", "\n")}
          |(set-logic ALL)
          |
          |(define-sort B () Bool)
          |(define-fun |B.unary_!| ((x B)) B (not x))
          |(define-fun |B.unary_~| ((x B)) B (not x))
          |(define-fun |B.==| ((x B) (y B)) B (= x y))
          |(define-fun |B.!=| ((x B) (y B)) B (not (= x y)))
          |(define-fun |B.&| ((x B) (y B)) B (and x y))
          |(define-fun |B.│| ((x B) (y B)) B (or x y))
          |(define-fun |B.│^| ((x B) (y B)) B (xor x y))
          |(define-fun |B.imply_:| ((x B) (y B)) B (=> x y))
          |
          |(define-sort C () (_ BitVec ${charBitWidth}))
          |(define-fun |C.unary_-| ((x C)) C (bvneg x))
          |(define-fun |C.unary_~| ((x C)) C (bvnot x))
          |(define-fun |C.<=| ((x C) (y C)) B (bvule x y))
          |(define-fun |C.<| ((x C) (y C)) B (bvult x y))
          |(define-fun |C.>| ((x C) (y C)) B (bvugt x y))
          |(define-fun |C.>=| ((x C) (y C)) B (bvuge x y))
          |(define-fun |C.==| ((x C) (y C)) B (= x y))
          |(define-fun |C.!=| ((x C) (y C)) B (not (= x y)))
          |(define-fun |C.+| ((x C) (y C)) C (bvadd x y))
          |(define-fun |C.-| ((x C) (y C)) C (bvsub x y))
          |(define-fun |C.*| ((x C) (y C)) C (bvmul x y))
          |(define-fun |C./| ((x C) (y C)) C (bvudiv x y))
          |(define-fun |C.%| ((x C) (y C)) C (bvurem x y))
          |(define-fun |C.<<| ((x C) (y C)) C (bvshl x y))
          |(define-fun |C.>>| ((x C) (y C)) C (bvlshr x y))
          |(define-fun |C.>>>| ((x C) (y C)) C (bvlshr x y))
          |
          |$zST
          |
          |(define-sort F32 () Float32)
          |(define-const |F32.PInf| F32 (_ +oo 8 24))
          |(define-const |F32.NInf| F32 (_ -oo 8 24))
          |(define-const |F32.NaN| F32 (_ NaN 8 24))
          |(define-fun |F32.unary_-| ((x F32)) F32 (fp.neg x))
          |(define-fun |F32.<=| ((x F32) (y F32)) B (fp.leq x y))
          |(define-fun |F32.<| ((x F32) (y F32)) B (fp.lt x y))
          |(define-fun |F32.>| ((x F32) (y F32)) B (fp.gt x y))
          |(define-fun |F32.>=| ((x F32) (y F32)) B (fp.geq x y))
          |(define-fun |F32.==| ((x F32) (y F32)) B (fp.eq x y))
          |(define-fun |F32.!=| ((x F32) (y F32)) B (not (fp.eq x y)))
          |(define-fun |F32.+| ((x F32) (y F32)) F32 (fp.add RNE x y))
          |(define-fun |F32.-| ((x F32) (y F32)) F32 (fp.sub RNE x y))
          |(define-fun |F32.*| ((x F32) (y F32)) F32 (fp.mul RNE x y))
          |(define-fun |F32./| ((x F32) (y F32)) F32 (fp.div RNE x y))
          |(define-fun |F32.%| ((x F32) (y F32)) F32 (fp.rem x y))
          |
          |(define-sort F64 () Float64)
          |(define-const |F64.PInf| F64 (_ +oo 11 53))
          |(define-const |F64.NInf| F64 (_ -oo 11 53))
          |(define-const |F64.NaN| F64 (_ NaN 11 53))
          |(define-fun |F64.unary_-| ((x F64)) F64 (fp.neg x))
          |(define-fun |F64.<=| ((x F64) (y F64)) B (fp.leq x y))
          |(define-fun |F64.<| ((x F64) (y F64)) B (fp.lt x y))
          |(define-fun |F64.>| ((x F64) (y F64)) B (fp.gt x y))
          |(define-fun |F64.>=| ((x F64) (y F64)) B (fp.geq x y))
          |(define-fun |F64.==| ((x F64) (y F64)) B (fp.eq x y))
          |(define-fun |F64.!=| ((x F64) (y F64)) B (not (fp.eq x y)))
          |(define-fun |F64.+| ((x F64) (y F64)) F64 (fp.add RNE x y))
          |(define-fun |F64.-| ((x F64) (y F64)) F64 (fp.sub RNE x y))
          |(define-fun |F64.*| ((x F64) (y F64)) F64 (fp.mul RNE x y))
          |(define-fun |F64./| ((x F64) (y F64)) F64 (fp.div RNE x y))
          |(define-fun |F64.%| ((x F64) (y F64)) F64 (fp.rem x y))
          |
          |(define-sort R () Real)
          |(define-fun |R.<=| ((x R) (y R)) B (<= x y))
          |(define-fun |R.<| ((x R) (y R)) B (< x y))
          |(define-fun |R.>| ((x R) (y R)) B (> x y))
          |(define-fun |R.>=| ((x R) (y R)) B (>= x y))
          |(define-fun |R.==| ((x R) (y R)) B (= x y))
          |(define-fun |R.!=| ((x R) (y R)) B (not (= x y)))
          |(define-fun |R.+| ((x R) (y R)) R (+ x y))
          |(define-fun |R.-| ((x R) (y R)) R (- x y))
          |(define-fun |R.*| ((x R) (y R)) R (* x y))
          |(define-fun |R./| ((x R) (y R)) R (/ x y))
          |
          |${(sorts, "\n\n")}
          |
          |(declare-sort ADT 0)
          |(declare-sort Type 0)
          |(declare-fun type-of (ADT) Type)
          |(declare-fun sub-type (Type Type) Bool)
          |(assert (forall ((x Type)) (sub-type x x)))
          |(assert (forall ((x Type) (y Type) (z Type)) (=> (and (sub-type x y) (sub-type y z)) (sub-type x z))))
          |(assert (forall ((x Type) (y Type)) (=> (and (sub-type x y) (sub-type y x)) (= x y))))
          |(declare-fun |ADT.==| (ADT ADT) B)
          |
          |${(adtDecls, "\n")}
          |
          |${(sTypeDecls, "\n")}
          |
          |${(typeDecls, "\n")}
          |
          |(assert (forall ((x ADT) (y ADT))
          |  (=> (|ADT.==| x y)
          |      (let ((t (type-of x)))
          |        (and
          |          (= t (type-of y))
          |          ${(adtEqs, "\n")})))))
          |
          |$distinctOpt
          |
          |${(for (p <- strictPureMethods.values) yield p._1, "\n")}
          |
          |${(for (p <- strictPureMethods.values) yield p._2, "\n")}
          |
          |${(decls, "\n")}
          |
          |${(for (a <- claims) yield st"(assert $a)", "\n")}
          |
          |(check-sat)
          |(exit)"""
    return r
  }

  @pure def v2ST(v: State.Value): ST = {
    v match {
      case v: State.Value.B => return if (v.value) Smt2.stTrue else Smt2.stFalse
      case v: State.Value.Z => return if (v.value < 0) st"(- ${v.value * -1})" else st"${v.value}"
      case v: State.Value.Sym => return st"cx!${v.num}"
      case v: State.Value.Range => return if (v.value < 0) st"(- ${v.value * -1})" else st"${v.value}"
      case v: State.Value.Enum => return enumId(v.owner, v.id)
      case v: State.Value.S8 => return toVal(v.tipe, conversions.S8.toZ(v.value))
      case v: State.Value.S16 => return toVal(v.tipe, conversions.S16.toZ(v.value))
      case v: State.Value.S32 => return toVal(v.tipe, conversions.S32.toZ(v.value))
      case v: State.Value.S64 => return toVal(v.tipe, conversions.S64.toZ(v.value))
      case v: State.Value.U8 => return toVal(v.tipe, conversions.U8.toZ(v.value))
      case v: State.Value.U16 => return toVal(v.tipe, conversions.U16.toZ(v.value))
      case v: State.Value.U32 => return toVal(v.tipe, conversions.U32.toZ(v.value))
      case v: State.Value.U64 => return toVal(v.tipe, conversions.U64.toZ(v.value))
      case v: State.Value.F32 => return formatF32(v.value)
      case v: State.Value.F64 => return formatF64(v.value)
      case v: State.Value.C =>
        val t: AST.Typed.Name = charBitWidth match {
          case 8 => AST.Typed.u8
          case 16 => AST.Typed.u16
          case 32 => AST.Typed.u32
          case _ => halt("Infeasible")
        }
        return toVal(t, conversions.U32.toZ(conversions.C.toU32(v.value)))
      case v: State.Value.R =>
        val text = s"${v.value}"
        return if (ops.StringOps(text).contains(".")) st"$text" else st"$text.0"
      case _ =>
        halt("TODO") // TODO
    }
  }

  @memoize def ids2ST(ids: ISZ[String]): ST = {
    return st"${(ids, ".")}"
  }

  def shorten(ids: ISZ[String]): ST = {
    def rec(suffix: ISZ[String]): ST = {
      shortIds.get(suffix) match {
        case Some(other) =>
          if (other != ids) {
            if (suffix.size == ids.size) {
              shortIdsUp(shortIds + ids ~> ids)
              return ids2ST(ids)
            } else {
              return rec(ops.ISZOps(ids).takeRight(suffix.size + 1))
            }
          } else {
            return ids2ST(suffix)
          }
        case _ =>
          if (suffix == ISZ("Type") && ids.size != 1) {
            return rec(ops.ISZOps(ids).takeRight(suffix.size + 1))
          } else {
            shortIdsUp(shortIds + suffix ~> ids)
            return ids2ST(suffix)
          }
      }
    }
    return rec(ISZ(ids(ids.size - 1)))
  }

  def currentNameId(c: State.Claim.Let.CurrentName): ST = {
    return st"|g:${(shorten(c.ids), ".")}|"
  }

  def currentLocalId(c: State.Claim.Let.CurrentId): ST = {
    return currentLocalIdString(c.id)
  }

  def currentLocalIdString(id: String): ST = {
    return st"|l:$id|"
  }

  def localId(c: State.Claim.Let.Id): ST = {
    return if (c.context.isEmpty) st"|l:${c.id}@${State.Claim.possLines(c.poss)}#${c.num}|"
    else st"|l:${c.id}:${(c.context, ".")}@${State.Claim.possLines(c.poss)}#${c.num}|"
  }

  def nameId(c: State.Claim.Let.Name): ST = {
    return st"|g:${(shorten(c.ids), ".")}@${State.Claim.possLines(c.poss)}#${c.num}|"
  }

  def qvar2ST(x: State.Claim.Let.Quant.Var): ST = {
    x match {
      case x: State.Claim.Let.Quant.Var.Id => return st"(|l:${x.id}| ${typeId(x.tipe)})"
      case x: State.Claim.Let.Quant.Var.Sym => return st"(${v2ST(x.sym)} ${typeId(x.sym.tipe)})"
    }
  }

  def enumId(owner: ISZ[String], id: String): ST = {
    return st"|e:${(shorten(owner), ".")}.$id|"
  }

  def l2DeclST(c: State.Claim.Let): ST = {
    c match {
      case c: State.Claim.Let.CurrentId if c.declId => return st"(${l2RhsST(c, v2ST _, HashMap.empty)} ${v2ST(c.sym)})"
      case _ => return st"(${v2ST(c.sym)} ${l2RhsST(c, v2ST _, HashMap.empty)})"
    }
  }

  def embeddedClaims(isImply: B, claims: ISZ[State.Claim], letsOpt: Option[HashMap[Z, ISZ[State.Claim.Let]]]): ST = {
    def collectSyms(c: State.Claim, acc: ISZ[State.Value.Sym]): ISZ[State.Value.Sym] = {
      c match {
        case c: State.Claim.Def => return acc :+ c.sym
        case c: State.Claim.And =>
          var r = acc
          for (ca <- c.claims) {
            r = collectSyms(ca, r)
          }
          return r
        case c: State.Claim.Or =>
          var r = acc
          for (ca <- c.claims) {
            r = collectSyms(ca, r)
          }
          return r
        case c: State.Claim.Imply =>
          var r = acc
          for (ca <- c.claims) {
            r = collectSyms(ca, r)
          }
          return r
        case c: State.Claim.If =>
          var r = acc
          for (ca <- c.tClaims ++ c.fClaims) {
            r = collectSyms(ca, r)
          }
          return r
        case _: State.Claim.Label => return acc
        case _: State.Claim.Prop => return acc
      }
    }

    def raw: ST = {
      var lets = ISZ[State.Claim.Let]()
      var lsyms = ISZ[State.Value.Sym]()
      var syms = ISZ[State.Value.Sym]()
      var rest = ISZ[State.Claim]()
      for (i <- 0 until claims.size) {
        claims(i) match {
          case claim: State.Claim.Let if i != claims.size - 1 => lsyms = lsyms :+ claim.sym; lets = lets :+ claim
          case claim: State.Claim.Def => syms = syms :+ claim.sym; rest = rest :+ claim
          case claim: State.Claim.If => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.And => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.Or => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.Imply => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.Label => rest = rest :+ claim
          case claim: State.Claim.Prop => rest = rest :+ claim
        }
      }
      var body: ST =
        if (isImply) implyST(rest, v2ST _, HashMap.empty)
        else andST(rest, v2ST _, HashMap.empty)
      if (lets.nonEmpty) {
        body =
          st"""(let (${l2DeclST(lets(lets.size - 1))})
              |  $body)"""
        for (i <- (lets.size - 2) to 0 by -1) {
          val let = lets(i)
          body =
            st"""(let (${l2DeclST(let)})
                |$body)"""
        }
      }
      val s = HashSSet.empty[State.Value.Sym] ++ syms -- lsyms
      if (s.nonEmpty) {
        body =
          st"""(exists (${(for (sym <- s.elements) yield st"(${v2ST(sym)} ${typeId(sym.tipe)})", " ")})
              |  $body)"""
      }
      return body
    }

    def simplified: ST = {
      var lets = StateUtil.collectLetClaims(simplifiedQuery, claims)
      letsOpt match {
        case Some(ls) =>
          for (p <- ls.entries) {
            val (k, s) = p
            lets = lets + k ~> (HashSet.empty[State.Claim.Let] ++ lets.get(k).getOrElse(ISZ()) ++ s).elements
          }
        case _ =>
      }
      val sv2ST = StateUtil.value2ST(this, lets)
      var simplifiedClaimSTs = ISZ[ST]()
      for (i <- 0 until (if (isImply) claims.size - 1 else claims.size)) {
        c2ST(claims(i), sv2ST, lets) match {
          case Some(st) => simplifiedClaimSTs = simplifiedClaimSTs :+ st
          case _ =>
        }
      }
      var r: ST =
        if (isImply) implySTH(simplifiedClaimSTs, c2ST(claims(claims.size - 1), sv2ST, lets))
        else andSTH(simplifiedClaimSTs)
      val uscdid = UsedSymsCurrentDeclIdCollector(HashSet.empty, ISZ())
      for (c <- claims) {
        uscdid.transformStateClaim(c)
      }
      val usedSyms = uscdid.syms
      val syms: ISZ[State.Value.Sym] = for (ds <- lets.values if ds.size > 1 && usedSyms.contains(ds(0).sym)) yield ds(0).sym
      var decls: ISZ[ST] = for (sym <- syms) yield st"(${v2ST(sym)} ${typeId(sym.tipe)})"
      for (cid <- uscdid.currentDeclIds) {
        decls = decls :+ st"(|l:${cid.id}| ${typeId(cid.sym.tipe)})"
      }
      if (decls.nonEmpty) {
        r =
          st"""(exists (${(decls, " ")})
              |  $r)"""
      }
      return r
    }

    return if (simplifiedQuery) simplified else raw
  }

  def l2RhsST(c: State.Claim.Let, v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]]): ST = {
    c match {
      case c: State.Claim.Let.CurrentName =>
        return currentNameId(c)
      case c: State.Claim.Let.Name =>
        return nameId(c)
      case c: State.Claim.Let.CurrentId =>
        return currentLocalId(c)
      case c: State.Claim.Let.Id =>
        return localId(c)
      case c: State.Claim.Let.Eq =>
        return v2st(c.value)
      case c: State.Claim.Let.TypeTest =>
        return st"(${if (c.isEq) "=" else "sub-type"} (type-of ${v2st(c.value)}) ${typeHierarchyId(c.tipe)})"
      case c: State.Claim.Let.Quant =>
        val body = embeddedClaims(c.isAll, c.claims, Some(lets))
        return if (c.isAll)
          st"""(forall (${(for (x <- c.vars) yield qvar2ST(x), " ")})
              |  $body
              |)"""
        else
          st"""(exists (${(for (x <- c.vars) yield qvar2ST(x), " ")})
              |  $body
              |)"""
      case c: State.Claim.Let.Binary => return st"(${typeOpId(c.tipe, c.op)} ${v2st(c.left)} ${v2st(c.right)})"
      case c: State.Claim.Let.Unary =>
        return st"(${typeOpId(c.sym.tipe, s"unary_${c.op}")} ${v2st(c.value)})"
      case c: State.Claim.Let.SeqLookup =>
        return st"(${typeOpId(c.seq.tipe, "at")} ${v2st(c.seq)} ${v2st(c.index)})"
      case c: State.Claim.Let.FieldLookup =>
        return st"(${typeOpId(c.adt.tipe, c.id)} ${v2st(c.adt)})"
      case c: State.Claim.Let.SeqInBound =>
        return st"(${typeOpId(c.seq.tipe, "isInBound")} ${v2st(c.seq)} ${v2st(c.index)})"
      case c: State.Claim.Let.TupleLit =>
        return st"(${typeOpId(c.sym.tipe, "new")} ${(for (arg <- c.args) yield v2st(arg), " ")})"
      case c: State.Claim.Let.And =>
        return if (c.args.size == 0) Smt2.stFalse
        else if (c.args.size == 1) v2st(c.args(0))
        else st"(and ${(c.args.map(v2st), " ")})"
      case c: State.Claim.Let.Or =>
        return if (c.args.size == 0) Smt2.stTrue
        else if (c.args.size == 1) v2st(c.args(0))
        else st"(or ${(c.args.map(v2st), " ")})"
      case c: State.Claim.Let.Imply =>
        return st"(=> ${(c.args.map(v2st), " ")})"
      case c: State.Claim.Let.Ite =>
        return st"(ite ${v2st(c.cond)} ${v2st(c.left)} ${v2st(c.right)})"
      case c: State.Claim.Let.ProofFunApply =>
        return st"(${proofFunId(c.pf)} ${(for (arg <- c.args) yield v2st(arg), " ")})"
      case c: State.Claim.Let.Apply =>
        halt("TODO") // TODO
      case c: State.Claim.Let.IApply =>
        halt("TODO") // TODO
    }
  }

  def c2ST(c: State.Claim, v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]]): Option[ST] = {
    c match {
      case c: State.Claim.Let =>
        c match {
          case c: State.Claim.Let.CurrentId if c.declId =>
          case _ =>
            lets.get(c.sym.num) match {
              case Some(ls) if ls.size == 1 => return None()
              case _ =>
            }
        }
        c match {
          case c: State.Claim.Let.Binary if Smt2.imsOps.contains(c.op) =>
            c.tipe match {
              case t: AST.Typed.Name if t.ids == AST.Typed.isName || t.ids == AST.Typed.msName =>
                return Some(st"(${typeOpId(t, c.op)} ${v2st(c.left)} ${v2st(c.right)} ${v2st(c.sym)})")
              case _ =>
            }
          case _ =>
        }
        val rhs: ST = c match {
          case c: State.Claim.Let.CurrentName =>
            return Some(st"(= ${currentNameId(c)} ${v2st(c.sym)})")
          case c: State.Claim.Let.Name =>
            return Some(st"(= ${nameId(c)} ${v2st(c.sym)})")
          case c: State.Claim.Let.CurrentId =>
            return Some(st"(= ${currentLocalId(c)} ${v2st(c.sym)})")
          case c: State.Claim.Let.Id =>
            return Some(st"(= ${localId(c)} ${v2st(c.sym)})")
          case _ => l2RhsST(c, v2st, lets)
        }
        return Some(st"(= ${v2st(c.sym)} $rhs)")
      case c: State.Claim.Def.SeqLit =>
        return Some(st"(${typeOpId(c.sym.tipe, s"new.${c.args.size}")} ${(for (arg <- c.args) yield st"${v2st(arg.index)} ${v2st(arg.value)}", " ")} ${v2st(c.sym)})")
      case c: State.Claim.Def.SeqStore =>
        return Some(st"(${typeOpId(c.seq.tipe, "up")} ${v2st(c.seq)} ${v2st(c.index)} ${v2st(c.element)} ${v2st(c.sym)})")
      case c: State.Claim.Def.FieldStore =>
        return Some(st"(${typeOpId(c.adt.tipe, s"${c.id}_=")} ${v2st(c.adt)} ${v2st(c.value)} ${v2st(c.sym)})")
      case c: State.Claim.Def.AdtLit =>
        return Some(st"(${typeOpId(c.sym.tipe, "new")} ${(for (arg <- c.args) yield v2st(arg), " ")} ${v2st(c.sym)})")
      case c: State.Claim.Prop =>
        return Some(if (c.isPos) v2st(c.value) else st"(not ${v2st(c.value)})")
      case _: State.Claim.Label =>
        return None()
      case _: State.Claim.Def.Random =>
        return None()
      case c: State.Claim.If =>
        return Some(
          st"""(ite ${v2st(c.cond)}
              |  ${andST(c.tClaims, v2st, lets)}
              |  ${andST(c.fClaims, v2st, lets)}
              |)"""
        )
      case c: State.Claim.And => return Some(andST(c.claims, v2st, lets))
      case c: State.Claim.Or => return Some(orST(c.claims, v2st, lets))
      case c: State.Claim.Imply => return Some(implyST(c.claims, v2st, lets))
    }
  }

  def andSTH(sts: ISZ[ST]): ST = {
    if (sts.size == 0) {
      return Smt2.stTrue
    } else if (sts.size == 1) {
      return sts(0)
    } else {
      val r =
        st"""(and
            |  ${(sts, "\n")})"""
      return r
    }
  }

  def andST(cs: ISZ[State.Claim], v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]]): ST = {
    var sts = ISZ[ST]()
    for (c <- cs) {
      c2ST(c, v2st, lets) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    return andSTH(sts)
  }

  def orSTH(sts: ISZ[ST]): ST = {
    if (sts.size == 0) {
      return Smt2.stTrue
    } else if (sts.size == 1) {
      return sts(0)
    } else {
      val r =
        st"""(or
            |  ${(sts, "\n")})"""
      return r
    }
  }

  def orST(cs: ISZ[State.Claim], v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]]): ST = {
    var sts = ISZ[ST]()
    for (c <- cs) {
      c2ST(c, v2st, lets) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    return orSTH(sts)
  }

  def implySTH(sts: ISZ[ST], lastOpt: Option[ST]): ST = {
    if (sts.size == 0) {
      return lastOpt.getOrElse(Smt2.stTrue)
    } else {
      val sts2: ISZ[ST] = lastOpt match {
        case Some(st) => sts :+ st
        case _ => sts
      }
      val r =
        st"""(=>
            |  ${(sts2, "\n")})"""
      return r
    }
  }

  def implyST(cs: ISZ[State.Claim], v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]]): ST = {
    var sts = ISZ[ST]()
    for (i <- 0 until cs.size - 1) {
      c2ST(cs(i), v2st, lets) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    val lastOpt = c2ST(cs(cs.size - 1), v2st, lets)
    return implySTH(sts, lastOpt)
  }

  def c2DeclST(c: State.Claim): ISZ[(String, ST)] = {
    @pure def declareConst(n: ST, tipe: AST.Typed): ST = {
      val r: ST = if (isAdtType(tipe)) {
        st"""(declare-const $n ${typeId(tipe)})
            |(assert (sub-type (type-of $n) ${typeHierarchyId(tipe)}))"""
      } else {
        st"(declare-const $n ${typeId(tipe)})"
      }
      return r
    }
    def def2DeclST(cDef: State.Claim.Def): ISZ[(String, ST)] = {
      val symST = v2ST(cDef.sym)
      return ISZ[(String, ST)](symST.render ~> st"(declare-const $symST ${typeId(cDef.sym.tipe)})")
    }
    c match {
      case _: State.Claim.Label => return ISZ()
      case c: State.Claim.Prop =>
        val vST = v2ST(c.value)
        return ISZ[(String, ST)](vST.render ~> st"(declare-const $vST B)")
      case c: State.Claim.If =>
        val condST = v2ST(c.cond)
        var r = ISZ[(String, ST)](condST.render ~> st"(declare-const $condST B)")
        for (tClaim <- c.tClaims) {
          r = r ++ c2DeclST(tClaim)
        }
        for (fClaim <- c.fClaims) {
          r = r ++ c2DeclST(fClaim)
        }
        return r
      case c: State.Claim.And => return for (claim <- c.claims; p <- c2DeclST(claim)) yield p
      case c: State.Claim.Or => return for (claim <- c.claims; p <- c2DeclST(claim)) yield p
      case c: State.Claim.Imply => return for (claim <- c.claims; p <- c2DeclST(claim)) yield p
      case c: State.Claim.Let.CurrentName =>
        var r = def2DeclST(c)
        val n = currentNameId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Let.Name =>
        var r = def2DeclST(c)
        val n = nameId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Let.CurrentId =>
        var r = def2DeclST(c)
        val n = currentLocalId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Let.Id =>
        var r = def2DeclST(c)
        val n = localId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Def => return def2DeclST(c)
    }
  }

  def typeIdRaw(t: AST.Typed): ST = {
    t match {
      case t: AST.Typed.Name =>
        if (t.args.isEmpty) {
          return st"${(shorten(t.ids), ".")}"
        } else {
          return st"${(shorten(t.ids), ".")}[${(for (arg <- t.args) yield typeIdRaw(arg), ", ")}]"
        }
      case t: AST.Typed.TypeVar => return st"$$${t.id}"
      case t: AST.Typed.Enum => return st"${(shorten(t.name), ".")}"
      case t: AST.Typed.Tuple => return st"(${(for (arg <- t.args) yield typeIdRaw(arg), ", ")})"
      case _ => halt("TODO") // TODO
    }
  }

  @pure def id(t: AST.Typed, prefix: String): ST = {
    t match {
      case t: AST.Typed.Name =>
        if (t.ids.size == 3 && t.args.isEmpty && t.ids(0) == "org" && t.ids(1) == "sireum") {
          return st"${t.ids(2)}"
        } else {
          if (t.args.nonEmpty) {
            return if (prefix == "") st"|${(shorten(t.ids), ".")}[${(for (arg <- t.args) yield typeIdRaw(arg), ", ")}]|"
            else st"|$prefix:${(shorten(t.ids), ".")}[${(for (arg <- t.args) yield typeIdRaw(arg), ", ")}]|"
          } else {
            return if (prefix == "") st"|${(t.ids, ".")}|" else st"|$prefix:${(t.ids, ".")}|"
          }
        }
      case t: AST.Typed.TypeVar => return st"$$${t.id}"
      case _ => return if (prefix == "") st"|${typeIdRaw(t)}|" else st"|$prefix:${typeIdRaw(t)}|"
    }
  }

  @pure def typeId(t: AST.Typed): ST = {
    return id(t, "")
  }

  @pure def typeHierarchyId(t: AST.Typed): ST = {
    return id(t, "T")
  }
}
