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
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.message.Reporter

@msig trait Smt2 {

  def types: HashSet[AST.Typed]

  def typesUp(newTypes: HashSet[AST.Typed]): Unit

  def poset: Poset[AST.Typed.Name]

  def posetUp(newPoset: Poset[AST.Typed.Name]): Unit

  def sorts: ISZ[ST]

  def sortsUp(newSorts: ISZ[ST]): Unit

  def addSort(sort: ST): Unit = {
    sortsUp(sorts :+ sort)
  }

  def typeDecls: ISZ[ST]

  def typeDeclsUp(newTypeDecls: ISZ[ST]): Unit

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

  def typeConstructors: ISZ[ST]

  def typeConstructorsUp(newConstructors: ISZ[ST]): Unit

  def addTypeConstructor(constructor: ST): Unit = {
    typeConstructorsUp(typeConstructors :+ constructor)
  }

  def typeHierarchy: TypeHierarchy

  def timeoutInSeconds: Z

  def checkSat(query: String): B

  def checkUnsat(query: String): B

  @memoize def basicTypes: HashSet[AST.Typed] = {
    return HashSet.empty[AST.Typed] ++ ISZ[AST.Typed](
      AST.Typed.b, AST.Typed.c, AST.Typed.f32, AST.Typed.f64, AST.Typed.r, AST.Typed.string, AST.Typed.z
    )
  }

  @memoize def typeHierarchyId(t: AST.Typed): ST = {
    return State.smtTypeHierarchyId(t)
  }

  @memoize def typeId(t: AST.Typed): ST = {
    return State.smtTypeId(t)
  }

  @memoize def adtId(tipe: AST.Typed): ST = {
    @pure def smtId(t: AST.Typed): ST = {
      t match {
        case t: AST.Typed.Name =>
          shorten(t) match {
            case Some(r) => return r
            case _ =>
              if (t.args.nonEmpty) {
                return st"|${(t.ids, ".")}[${(for (arg <- t.args) yield smtIdRaw(arg), ", ")}]|"
              } else {
                return st"|${(t.ids, ".")}|"
              }
          }
        case _ => return st"|${smtIdRaw(t)}|"
      }
    }

    @pure def smtIdRaw(t: AST.Typed): ST = {
      t match {
        case t: AST.Typed.Name =>
          shorten(t) match {
            case Some(r) => return r
            case _ =>
              if (t.args.nonEmpty) {
                return st"${(t.ids, ".")}[${(for (arg <- t.args) yield smtIdRaw(arg), ", ")}]"
              } else {
                return st"${(t.ids, ".")}"
              }
          }
        case t: AST.Typed.TypeVar => return st"'${t.id}"
        case _ => halt("TODO") // TODO
      }
    }

    @pure def shorten(t: AST.Typed.Name): Option[ST] = {
      @pure def isAdt: B = {
        typeHierarchy.typeMap.get(t.ids).get match {
          case _: TypeInfo.Adt => return T
          case _: TypeInfo.Sig => return T
          case _ => return F
        }
      }
      if (t.ids.size == 3 && t.ids(0) == "org" && t.ids(1) == "sireum") {
        val tid = t.ids(2)
        if (tid == "IS" || tid == "MS") {
          val it = t.args(0).asInstanceOf[AST.Typed.Name]
          var zIndex: B = it == AST.Typed.z
          if (!zIndex) {
            typeHierarchy.typeMap.get(it.ids).get match {
              case ti: TypeInfo.SubZ if ti.ast.isBitVector =>
              case _ => zIndex = T
            }
          }
          return if (zIndex) Some(st"(${tid}Z ${smtIdRaw(t.args(1))})")
          else Some(st"($tid ${smtIdRaw(it)} ${smtIdRaw(t.args(1))})")
        } else if (t.args.isEmpty) {
          return if (!basicTypes.contains(t) && isAdt) Some(st"ADT") else Some(st"${t.ids(2)}")
        }
      }
      return if (isAdt) Some(st"ADT") else None()
    }

    return smtId(tipe)
  }

  @memoize def typeOpId(tipe: AST.Typed.Name, op: String): ST = {
    return st"|${typeIdRaw(tipe)}.$op|"
  }

  @memoize def typeIdRaw(t: AST.Typed): ST = {
    return State.smtIdRaw(t)
  }

  @pure def typeConstructorId(t: AST.Typed.Name): ST = {
    return State.smtTypeConstructorId(t)
  }

  @memoize def globalId(owner: ISZ[String], id: String): ST = {
    return st"|g:${(owner, ".")}.$id|"
  }

  @memoize def fieldId(receiver: AST.Typed, id: String): ST = {
    return st"|f:${typeIdRaw(receiver)}.$id|"
  }

  def sat(title: String, claims: ISZ[State.Claim]): B = {
    val headers = st"Satisfiability Check for $title:" +: (for (c <- claims) yield c.toST)
    checkSat(satQuery(headers, claims).render)
  }

  def addType(tipe: AST.Typed): Unit = {
    def addS(t: AST.Typed.Name): Unit = {
      val it = t.args(0).asInstanceOf[AST.Typed.Name]
      addType(it)
      val et = t.args(1)
      addType(et)
      val tId = typeId(t)
      val aId = adtId(t)
      val itId = typeId(it)
      val etId = typeId(et)
      val atId = typeOpId(t, "at")
      val sizeId = typeOpId(t, "size")
      val appendId = typeOpId(t, ":+")
      val appendsId = typeOpId(t, "++")
      val prependId = typeOpId(t, "+:")
      addTypeDecl(st"(define-sort $tId () $aId)")
      val aIdOps = ops.StringOps(aId.render)
      if (aIdOps.startsWith("(ISZ") || aIdOps.startsWith("(MSZ")) {
        addTypeDecl(st"(define-fun $sizeId ((x $tId)) Z (seq.len x))")
        addTypeDecl(st"(declare-fun $atId ($tId $itId) $etId)")
        addTypeDecl(
          st"""(assert (forall ((x $tId) (y $itId) (z $etId))
                       |  (= (= ($atId x y) z)
                       |     (= (seq.at x y) (seq.unit z)))))""")
        addTypeDecl(st"(define-fun $appendId ((x $tId) (y $etId)) $tId (seq.++ x (seq.unit y)))")
        addTypeDecl(st"(define-fun $appendsId ((x $tId) (y $tId)) $tId (seq.++ x y))")
        addTypeDecl(st"(define-fun $prependId ((x $etId) (y $tId)) $tId (seq.++ (seq.unit x) y))")
      } else {
        addTypeDecl(st"(declare-fun $sizeId ($tId) Z)")
        addTypeDecl(st"(define-fun $atId ((x $tId) (y $itId)) $etId (select x y))")
        addTypeDecl(st"(assert (forall ((x $tId)) (>= ($sizeId x) 0)))")
        addTypeDecl(st"(declare-fun $appendId ($tId $etId) $tId)")
        addTypeDecl(
          st"""(assert (forall ((x $tId) (y $etId) (z $tId))
                       |  (= (= ($appendId x y) z)
                       |     (and
                       |        (= ($sizeId z) (+ ($sizeId x) 1))
                       |        (forall ((i Z)) (implies (and (<= 0 i) (< i ($sizeId x)))
                       |                                 (= ($atId z i) ($atId x i)))
                       |        (= ($atId z ($sizeId x)) y)))))""")
        addTypeDecl(st"(declare-fun $appendsId ($tId $tId) $tId)")
        addTypeDecl(
          st"""(assert (forall ((x $tId) (y $tId) (z $tId))
                       |  (= (= ($appendsId x y) z)
                       |     (and
                       |        (= ($sizeId z) (+ ($sizeId x) ($sizeId y)))
                       |        (forall ((i Z)) (implies (and (<= 0 i) (< i ($sizeId x)))
                       |                                 (= ($atId z i) ($atId x i)))
                       |        (forall ((i Z)) (implies (and (<= 0 i) (< i ($sizeId y)))
                       |                                 (= ($atId z (+ ($sizeId x) i)) ($atId y i)))))))""")
        addTypeDecl(st"(declare-fun $prependId ($etId $tId) $tId)")
        addTypeDecl(
          st"""(assert (forall ((x $etId) (y $tId) (z $tId))
                       |  (= (= ($prependId x y) z)
                       |     (and
                       |        (= ($sizeId z) (+ ($sizeId y) 1))
                       |        (forall ((i Z)) (implies (and (<= 0 i) (< i ($sizeId y)))
                       |                                 (= ($atId z (+ i 1)) ($atId y i)))
                       |        (= ($atId z 0) x)))))""")
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

      val reporter = Reporter.create
      val tsm = TypeChecker.buildTypeSubstMap(t.ids, None(), tTypeParams, t.args, reporter).get
      assert(!reporter.hasMessage)
      for (parent <- parents) {
        addType(parent.subst(tsm))
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
            addType(childT)
          }
        }
        posetUp(poset.addChildren(t, children))
        addTypeDecls(for (child <- children) yield st"(assert (sub-type ${typeHierarchyId(child)} $tId))")
      }
      return tsm
    }
    def addAdt(t: AST.Typed.Name, ti: TypeInfo.Adt): Unit = {
      for (arg <- t.args) {
        addType(arg)
      }
      posetUp(poset.addNode(t))
      addTypeDecl(st"(define-sort ${typeId(t)} () ADT)")
      val tId = typeHierarchyId(t)
      addTypeHiearchyId(tId)
      addTypeDecl(st"(declare-const $tId Type)")
      val sm = addSub(ti.ast.isRoot, t, ti.ast.typeParams, tId, ti.parents)

      @pure def fieldIdType(f: Info.Var): (ST, ST, AST.Typed) = {
        val ft = f.typedOpt.get.subst(sm)
        return (fieldId(t, f.ast.id.value), adtId(ft), ft)
      }
      if (!ti.ast.isRoot) {
        val tcId = typeConstructorId(t)
        val fieldIdTypes: ISZ[(ST, ST, AST.Typed)] = for (f <- ti.vars.values) yield fieldIdType(f)
        addTypeConstructor(
          st"""($tcId
                         |  ${(for (t <- fieldIdTypes) yield st"(${t._1} ${t._2})", "\n")})""")
        addTypeDecl(st"(assert (leaf-type $tId))")
        for (t <- fieldIdTypes if t._2.render == "ADT") {
          addTypeDecl(
            st"""(assert (forall ((o ADT) (v ADT))
                         |  (implies (= (${t._1} o) v)
                         |           (sub-type (type-of v) ${typeHierarchyId(t._3)}))))""")
        }
      }
    }
    def addSig(t: AST.Typed.Name, ti: TypeInfo.Sig): Unit = {
      for (arg <- t.args) {
        addType(arg)
      }
      posetUp(poset.addNode(t))
      addTypeDecl(st"(define-sort ${typeId(t)} () ADT)")
      val tId = typeHierarchyId(t)
      addTypeHiearchyId(tId)
      addTypeDecl(st"(declare-const $tId Type)")
      addSub(T, t, ti.ast.typeParams, tId, ti.parents)
    }
    def addSubZ(t: AST.Typed.Name, ti: TypeInfo.SubZ): Unit = {
      halt("TODO") // TODO
    }
    def addEnum(name: ISZ[String], ti: Info.Enum): Unit = {
      halt("TODO") // TODO
    }
    def addTypeVar(t: AST.Typed.TypeVar): Unit = {
      addTypeDecl(st"(declare-sort ${typeId(t)})")
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
            case _ => halt(s"Infeasible: $t")
          }
        }
      case t: AST.Typed.TypeVar => addTypeVar(t)
      case t: AST.Typed.Enum => addEnum(t.name, typeHierarchy.nameMap.get(t.name).get.asInstanceOf[Info.Enum])
      case _ => halt(s"TODO: $tipe") // TODO
    }
  }

  def satQuery(headers: ISZ[ST], claims: ISZ[State.Claim]): ST = {
    for (c <- claims; t <- c.types) {
      addType(t)
    }
    val decls: ISZ[String] = (HashSMap.empty[String, String] ++
      (for (c <- claims; p <- c.toSmtDeclString) yield p)).values
    return query(headers, decls, for (c <- claims) yield c.toSmtString)
  }

  def valid(title: String, premises: ISZ[State.Claim], conclusion: State.Claim): B = {
    val headers = st"Validity Check for $title:" +: (for (c <- premises) yield c.toST) :+ st"  ⊢" :+ conclusion.toST
    checkUnsat(satQuery(headers, premises :+ State.Claim.Neg(conclusion)).render)
  }

  @pure def query(headers: ISZ[ST], decls: ISZ[String], claims: ISZ[String]): ST = {
    val distinctOpt: Option[ST] =
      if (typeHierarchyIds.isEmpty) None()
      else Some(st"""(assert (distinct
                    |  ${(typeHierarchyIds, "\n")}))""")
    return st"""${(for (header <- headers; line <- ops.StringOps(header.render).split(c => c == '\n')) yield st"; $line", "\n")}
               |
               |(define-sort   B            ()           Bool)
               |(define-sort   C            ()           String)
               |(define-sort   Z            ()           Int)
               |(define-sort   R            ()           Real)
               |(define-sort   F32          ()           Float32)
               |(define-sort   F64          ()           Float64)
               |(define-const  F32_PInf     (F32)        (_ +oo 8 24))
               |(define-const  F32_NInf     (F32)        (_ -oo 8 24))
               |(define-const  F32_NaN      (F32)        (_ NaN 8 24))
               |(define-const  F64_PInf     (F64)        (_ +oo 11 53))
               |(define-const  F64_NInf     (F64)        (_ -oo 11 53))
               |(define-const  F64_NaN      (F64)        (_ NaN 11 53))
               |
               |(define-sort   IS           (I T)        (Array I T))
               |(define-sort   MS           (I T)        (Array I T))
               |(define-sort   ISZ          (T)          (Seq T))
               |(define-sort   MSZ          (T)          (Seq T))
               |
               |${(sorts, "\n\n")}
               |
               |(declare-sort SigData)
               |(declare-sort MSigData)
               |
               |(declare-datatypes ((ADT 0))
               |  (((Sig (Sig.data SigData))
               |    (MSig (MSig.data MSigData))
               |    ${(typeConstructors, "\n")})))
               |
               |(declare-sort  Type)
               |(declare-fun   type-of      (ADT)        Type)
               |(declare-fun   sub-type     (Type Type)  Bool)
               |(define-fun    leaf-type    ((x Type))   Bool
               |                  (forall ((y Type)) (=> (sub-type y x) (= y x))))
               |(assert        (forall ((x Type))
               |                  (sub-type x x)))
               |(assert        (forall ((x Type) (y Type) (z Type))
               |                  (=> (and (sub-type x y) (sub-type y z)) (sub-type x z))))
               |(assert        (forall ((x Type) (y Type))
               |                  (=> (and (sub-type x y) (sub-type y x)) (= x y))))
               |
               |${(typeDecls, "\n")}
               |
               |$distinctOpt
               |
               |${(decls, "\n")}
               |
               |${(for (a <- claims) yield st"(assert $a)", "\n")}
               |
               |(check-sat)
               |(exit)"""
  }
}
