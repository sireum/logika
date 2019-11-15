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

object Smt2 {

  @datatype class SeqLit(t: AST.Typed.Name, size: Z)

  val binop2Smt2Map: HashMap[AST.Typed.Name, HashMap[String, String]] =
    HashMap.empty[AST.Typed.Name, HashMap[String, String]] ++
      ISZ[(AST.Typed.Name, HashMap[String, String])](
        AST.Typed.b ~> (HashMap.empty[String, String] ++ ISZ(
          AST.Exp.BinaryOp.And ~> "and",
          AST.Exp.BinaryOp.Or ~> "or",
          AST.Exp.BinaryOp.Imply ~> "=>"
        )),
        AST.Typed.z ~> (HashMap.empty[String, String] ++ ISZ(
          AST.Exp.BinaryOp.Add ~> "+",
          AST.Exp.BinaryOp.Sub ~> "-",
          AST.Exp.BinaryOp.Mul ~> "*",
          AST.Exp.BinaryOp.Div ~> "div",
          AST.Exp.BinaryOp.Rem ~> "rem",
          AST.Exp.BinaryOp.Eq ~> "=",
          AST.Exp.BinaryOp.Lt ~> "<",
          AST.Exp.BinaryOp.Le ~> "<=",
          AST.Exp.BinaryOp.Gt ~> ">",
          AST.Exp.BinaryOp.Ge ~> ">="
        )),
      )

  val unop2Smt2Map: HashMap[AST.Typed, HashMap[AST.Exp.UnaryOp.Type, String]] =
    HashMap.empty[AST.Typed, HashMap[AST.Exp.UnaryOp.Type, String]] ++
      ISZ[(AST.Typed, HashMap[AST.Exp.UnaryOp.Type, String])](
        AST.Typed.b ~> (HashMap.empty[AST.Exp.UnaryOp.Type, String] ++ ISZ(
          AST.Exp.UnaryOp.Not ~> "not",
          AST.Exp.UnaryOp.Complement ~> "not",
        )),
        AST.Typed.z ~> (HashMap.empty[AST.Exp.UnaryOp.Type, String] ++ ISZ(
          AST.Exp.UnaryOp.Minus ~> "-"
        ))
      )

  @pure def typeId(t: AST.Typed): ST = {
    return id(t, "")
  }

  @pure def typeHierarchyId(t: AST.Typed): ST = {
    return id(t, "T")
  }

  @pure def id(t: AST.Typed, prefix: String): ST = {
    t match {
      case t: AST.Typed.Name =>
        shorten(t) match {
          case Some((r, raw)) => return if (raw) r else st"|$r|"
          case _ =>
            if (t.args.nonEmpty) {
              return if (prefix == "") st"|${(t.ids, ".")}[${(for (arg <- t.args) yield idRaw(arg), ", ")}]|"
              else st"|$prefix:${(t.ids, ".")}[${(for (arg <- t.args) yield idRaw(arg), ", ")}]|"
            } else {
              return if (prefix == "") st"|${(t.ids, ".")}|" else st"|$prefix:${(t.ids, ".")}|"
            }
        }
      case _ => return if (prefix == "") st"|${idRaw(t)}|" else st"|$prefix:${idRaw(t)}|"
    }
  }

  @pure def idRaw(t: AST.Typed): ST = {
    t match {
      case t: AST.Typed.Name =>
        shorten(t) match {
          case Some((r, _)) => return r
          case _ =>
            if (t.args.nonEmpty) {
              return st"${(t.ids, ".")}[${(for (arg <- t.args) yield idRaw(arg), ", ")}]"
            } else {
              return st"${(t.ids, ".")}"
            }
        }
      case t: AST.Typed.TypeVar => return st"'${quotedEscape(t.id)}"
      case _ => halt("TODO") // TODO
    }
  }

  @pure def shorten(t: AST.Typed.Name): Option[(ST, B)] = {
    if (t.ids.size == 3 && t.ids(0) == "org" && t.ids(1) == "sireum") {
      val tid = t.ids(2)
      if (tid == "IS" || tid == "MS") {
        val it = t.args(0).asInstanceOf[AST.Typed.Name]
        return Some((st"$tid[${idRaw(it)}, ${idRaw(t.args(1))}]", F))
      } else if (t.args.isEmpty) {
        return Some((st"${t.ids(2)}", T))
      }
    }
    return None()
  }

  @strictpure def quotedEscape(s: String): String = ops.StringOps(s).replaceAllChars('|', '│')
}

@msig trait Smt2 {

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

  def shortIds: HashMap[ISZ[String], ISZ[String]]

  def shortIdsUp(newShortIds: HashMap[ISZ[String], ISZ[String]]): Unit

  def addShortIds(ids: ISZ[String], shortenedIds: ISZ[String]): Unit = {
    shortIdsUp(shortIds + ids ~> shortenedIds)
  }

  def addSeqLit(t: AST.Typed.Name, n: Z): Unit = {
    seqLitsUp(seqLits + Smt2.SeqLit(t, n))
  }

  def typeHierarchy: TypeHierarchy

  def checkSat(query: String, timeoutInMs: Z): B

  def checkUnsat(query: String, timeoutInMs: Z): B

  @memoize def basicTypes: HashSet[AST.Typed] = {
    return HashSet.empty[AST.Typed] ++ ISZ[AST.Typed](
      AST.Typed.b, AST.Typed.c, AST.Typed.f32, AST.Typed.f64, AST.Typed.r, AST.Typed.string, AST.Typed.z
    )
  }

  @memoize def typeHierarchyId(t: AST.Typed): ST = {
    return Smt2.typeHierarchyId(t)
  }

  @memoize def typeId(t: AST.Typed): ST = {
    return Smt2.typeId(t)
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

  @memoize def typeOpId(tipe: AST.Typed, op: String): ST = {
    return st"|${typeIdRaw(tipe)}.${Smt2.quotedEscape(op)}|"
  }

  @memoize def typeIdRaw(t: AST.Typed): ST = {
    return Smt2.idRaw(t)
  }

  @memoize def globalId(owner: ISZ[String], id: String): ST = {
    return st"|g:${(owner, ".")}.$id|"
  }

  def sat(title: String, claims: ISZ[State.Claim]): B = {
    val headers = st"Satisfiability Check for $title:" +: (for (c <- claims) yield c.toST)
    checkSat(satQuery(headers, claims, None()).render, 500)
  }

  def addType(tipe: AST.Typed): Unit = {
    def addS(t: AST.Typed.Name): Unit = {
      val it = t.args(0).asInstanceOf[AST.Typed.Name]
      addType(it)
      val et = t.args(1)
      addType(et)
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
      val firstIndexId = typeOpId(t, "firstIndex")
      val lastIndexId = typeOpId(t, "lastIndex")
      addTypeDecl(st"(define-sort $tId () (Array $itId $etId))")
      addTypeDecl(st"(declare-fun $sizeId ($tId) Z)")
      //addTypeDecl(st"(define-fun $firstIndexId ($tId) $itId )")
      addTypeDecl(st"(assert (forall ((x $tId)) (>= ($sizeId x) 0)))")
      addTypeDecl(st"(define-fun $atId ((x $tId) (y $itId)) $etId (select x y))")
      addTypeDecl(
        st"""(define-fun $appendId ((x $tId) (y $etId) (z $tId)) B
            |  (and
            |    (= ($sizeId z) (+ ($sizeId x) 1))
            |    (forall ((i $itId)) (=> (and (<= 0 i) (< i ($sizeId x)))
            |                            (= ($atId z i) ($atId x i))))
            |    (= ($atId z ($sizeId x)) y)))""")
      addTypeDecl(
        st"""(define-fun $appendsId ((x $tId) (y $tId) (z $tId)) B
            |  (and
            |    (= ($sizeId z) (+ ($sizeId x) ($sizeId y)))
            |      (forall ((i $itId)) (=> (and (<= 0 i) (< i ($sizeId x)))
            |                              (= ($atId z i) ($atId x i))))
            |      (forall ((i $itId)) (=> (and (<= 0 i) (< i ($sizeId y)))
            |                              (= ($atId z (+ ($sizeId x) i)) ($atId y i))))))""")
      addTypeDecl(
        st"""(define-fun $prependId ((x $etId) (y $tId) (z $tId)) B
            |  (and
            |    (= ($sizeId z) (+ ($sizeId y) 1))
            |    (forall ((i $itId)) (=> (and (<= 0 i) (< i ($sizeId y)))
            |                            (= ($atId z (+ i 1)) ($atId y i))))
            |    (= ($atId z 0) x)))""")
      addTypeDecl(
        st"""(define-fun $upId ((x $tId) (y $itId) (z $etId) (x2 $tId)) B
            |  (and
            |    (= ($sizeId x2) ($sizeId x))
            |    (= x2 (store x y z))))""")
      addTypeDecl(
        st"""(define-fun $eqId ((x $tId) (y $tId)) B
            |  (and
            |    (= ($sizeId x) ($sizeId y))
            |    (forall ((i $itId)) (= (select x i) (select y i)))))""")
      if (isAdtType(et)) {
        addTypeDecl(
          st"""(assert (forall ((x $tId) (i $itId) (v ADT))
              |  (=> (= ($atId x i) v)
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
      val tId = typeId(t)
      addTypeDecl(st"(define-sort $tId () ADT)")
      val thId = typeHierarchyId(t)
      addTypeHiearchyId(thId)
      addTypeDecl(st"(declare-const $thId Type)")
      val sm = addSub(ti.ast.isRoot, t, ti.ast.typeParams, thId, ti.parents)

      @pure def fieldIdType(f: Info.Var): (ST, ST, AST.Typed, String) = {
        val ft = f.typedOpt.get.subst(sm)
        val id = f.ast.id.value
        return (typeOpId(t, f.ast.id.value), adtId(ft), ft, id)
      }

      if (!ti.ast.isRoot) {
        val newId = typeOpId(t, "new")
        val fieldIdTypes: ISZ[(ST, ST, AST.Typed, String)] = for (f <- ti.vars.values) yield fieldIdType(f)
        for (q <- fieldIdTypes) {
          addTypeDecl(st"(declare-fun ${q._1} ($tId) ${q._2})")
        }
        addTypeDecl(
          st"""(define-fun $newId (${(for (q <- fieldIdTypes) yield st"(${q._4} ${q._2})", " ")} (x $tId)) B
              |  (and
              |    (sub-type (type-of x) $thId)
              |    ${(for (q <- fieldIdTypes) yield st"(= (${q._1} x) ${q._4})", "\n")}))""")
        addTypeDecl(st"(assert (leaf-type $thId))")
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
    val r =
      st"""(define-fun $seqLitId (${(for (i <- 0 until size) yield st"(i$i $itId) (v$i $etId)", " ")} (x $tId)) B
          |  (and
          |    (= ($sizeId x) $size)
          |    ${(for (i <- 0 until size) yield st"(= ($atId x i$i) v$i)", "\n")}))"""
    return r.render
  }

  def satQuery(headers: ISZ[ST], claims: ISZ[State.Claim], negClaimOpt: Option[State.Claim]): ST = {
    for (c <- claims; t <- c.types) {
      addType(t)
    }
    var decls: HashSMap[String, ST] = HashSMap.empty[String, ST] ++
      (for (c <- claims; p <- c2DeclST(c)) yield p)
    var claimSmts: ISZ[String] = for (c <- claims) yield c2ST(c).render
    negClaimOpt match {
      case Some(negClaim) =>
        claimSmts = claimSmts :+ st"(not ${c2ST(negClaim)})".render
        decls = decls ++ c2DeclST(negClaim)
      case _ =>
    }
    val seqLitDecls: ISZ[String] = for (seqLit <- seqLits.elements) yield seqLit2SmtDeclString(seqLit)
    return query(headers, seqLitDecls ++ (for (d <- decls.values) yield d.render), claimSmts)
  }

  def valid(title: String, premises: ISZ[State.Claim], conclusion: State.Claim, timeoutInMs: Z): B = {
    val headers = st"Validity Check for $title:" +: (for (c <- premises) yield c.toST) :+ st"  ⊢" :+ conclusion.toST
    checkUnsat(satQuery(headers, premises, Some(conclusion)).render, timeoutInMs)
  }

  def isAdtType(t: AST.Typed): B = {
    return adtId(t).render == "ADT"
  }

  @pure def query(headers: ISZ[ST], decls: ISZ[String], claims: ISZ[String]): ST = {
    val distinctOpt: Option[ST] =
      if (typeHierarchyIds.isEmpty) None()
      else Some(
        st"""(assert (distinct
            |  ${(typeHierarchyIds, "\n")}))""")
    val r =
      st"""${(for (header <- headers; line <- ops.StringOps(header.render).split(c => c == '\n')) yield st"; $line", "\n")}
          |(set-logic ALL)
          |
          |(define-sort B () Bool)
          |(define-fun |B.!| ((x B)) B (not x))
          |(define-fun |B.&| ((x B) (y B)) B (and x y))
          |(define-fun |B.│| ((x B) (y B)) B (or x y))
          |(define-fun |B.│^| ((x B) (y B)) B (xor x y))
          |(define-fun |B.imply_:| ((x B) (y B)) B (=> x y))
          |
          |(define-sort Z () Int)
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
          |(define-fun |Z.%| ((x Z) (y Z)) Z (mod x y))
          |
          |${(sorts, "\n\n")}
          |
          |(declare-sort ADT 0)
          |(declare-sort Type 0)
          |(declare-fun type-of (ADT) Type)
          |(declare-fun sub-type (Type Type) Bool)
          |(define-fun leaf-type ((x Type)) Bool (forall ((y Type)) (=> (sub-type y x) (= y x))))
          |(assert (forall ((x Type)) (sub-type x x)))
          |(assert (forall ((x Type) (y Type) (z Type)) (=> (and (sub-type x y) (sub-type y z)) (sub-type x z))))
          |(assert (forall ((x Type) (y Type)) (=> (and (sub-type x y) (sub-type y x)) (= x y))))
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
    return r
  }

  @pure def v2ST(v: State.Value): ST = {
    v match {
      case v: State.Value.B => return if (v.value) st"true" else st"false"
      case v: State.Value.Z => return st"${v.value}"
      case v: State.Value.Sym => return st"cx!${v.num}"
      case v: State.Value.Range => return st"${v.value}"
      case _ =>
        halt("TODO") // TODO
    }
  }

  def rawShorten(ids: ISZ[String]): ST = {
    def rec(suffix: ISZ[String]): ST = {
      shortIds.get(suffix) match {
        case Some(_) =>
          if (suffix.size == ids.size) {
            shortIdsUp(shortIds + ids ~> ids)
            return st"${(ids, ".")}"
          } else {
            return rec(ops.ISZOps(ids).takeRight(suffix.size + 1))
          }
        case _ =>
          shortIdsUp(shortIds + suffix ~> ids)
          return st"${(suffix, ".")}"
      }
    }
    return rec(ISZ(ids(ids.size - 1)))
  }

  def currentNameId(c: State.Claim.Let.CurrentName): ST = {
    return st"|g:${(rawShorten(c.ids), ".")}|"
  }

  def currentLocalId(c: State.Claim.Let.CurrentId): ST = {
    return st"|l:${c.id}|"
  }

  def localId(c: State.Claim.Let.Id): ST = {
    return if (c.context.isEmpty) st"|l:${c.id}@${State.Claim.possLines(c.poss)}#${c.num}|"
    else st"|l:${c.id}:${(c.context, ".")}@${State.Claim.possLines(c.poss)}#${c.num}|"
  }

  def nameId(c: State.Claim.Let.Name): ST = {
    return st"|g:${(rawShorten(c.ids), ".")}@${State.Claim.possLines(c.poss)}#${c.num}|"
  }

  def qvar2ST(x: State.Claim.Let.Quant.Var): ST = {
    return st"(|l:${x.id}| ${Smt2.typeId(x.tipe)})"
  }

  def l2DeclST(c: State.Claim.Let): ST = {
    return st"(${v2ST(c.sym)} ${l2RhsST(c)})"
  }

  def l2RhsST(c: State.Claim.Let): ST = {
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
        return v2ST(c.value)
      case c: State.Claim.Let.Quant =>
        var lets = ISZ[State.Claim.Let]()
        var defs = ISZ[State.Claim.Def]()
        var rest = ISZ[State.Claim]()
        for (claim <- c.claims) {
          claim match {
            case claim: State.Claim.Let => lets = lets :+ claim
            case claim: State.Claim.Def => defs = defs :+ claim; rest = rest :+ claim
            case _ => rest = rest :+ claim
          }
        }
        var body: ST = if (c.isAll) implyST(rest) else andST(rest)
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
        if (defs.nonEmpty) {
          body =
            st"""(forall (${(for (d <- defs) yield st"(${v2ST(d.sym)} ${Smt2.typeId(d.sym.tipe)})", " ")})
                |  $body)"""
        }
        return if (c.isAll)
          st"""(forall (${(for (x <- c.vars) yield qvar2ST(x), " ")})
              |  $body
              |)"""
        else
          st"""(exists (${(for (x <- c.vars) yield qvar2ST(x), " ")})
              |  $body
              |)"""
      case c: State.Claim.Let.Binary =>
        var neg: B = F
        val binop: String = if (c.op == "!=") {
          neg = T
          "=="
        } else {
          c.op
        }
        val r: ST = Smt2.binop2Smt2Map.get(c.tipe) match {
          case Some(m) =>
            if (neg) st"(not (${m.get(binop).get} ${v2ST(c.left)} ${v2ST(c.right)}))"
            else st"(${m.get(binop).get} ${v2ST(c.left)} ${v2ST(c.right)})"
          case _ =>
            halt("TODO") // TODO
        }
        return r
      case c: State.Claim.Let.Unary =>
        Smt2.unop2Smt2Map.get(c.sym.tipe) match {
          case Some(m) => return st"(${m.get(c.op).get} ${v2ST(c.sym)})"
          case _ =>
            halt("TODO") // TODO
        }
      case c: State.Claim.Let.SeqLookup =>
        return st"(${c.atId} ${v2ST(c.seq)} ${v2ST(c.index)})"
      case c: State.Claim.Let.FieldStore =>
        halt("TODO") // TODO
      case c: State.Claim.Let.FieldLookup =>
        return st"(${c.id} ${v2ST(c.adt)})"
      case c: State.Claim.Let.Apply =>
        halt("TODO") // TODO
      case c: State.Claim.Let.IApply =>
        halt("TODO") // TODO
    }
  }

  def c2ST(c: State.Claim): ST = {
    c match {
      case c: State.Claim.Let =>
        val rhs: ST = c match {
          case c: State.Claim.Let.CurrentName =>
            return st"(= ${currentNameId(c)} ${v2ST(c.sym)})"
          case c: State.Claim.Let.Name =>
            return st"(= ${nameId(c)} ${v2ST(c.sym)})"
          case c: State.Claim.Let.CurrentId =>
            return st"(= ${currentLocalId(c)} ${v2ST(c.sym)})"
          case c: State.Claim.Let.Id =>
            return st"(= ${localId(c)} ${v2ST(c.sym)})"
          case _ => l2RhsST(c)
        }
        return st"(= ${v2ST(c.sym)} $rhs)"
      case c: State.Claim.Def.SeqLit =>
        return st"(${c.seqLitId} ${(for (arg <- c.args) yield st"${v2ST(arg._1)} ${v2ST(arg._2)}", " ")} ${v2ST(c.sym)})"
      case c: State.Claim.Def.SeqStore =>
        return st"(${c.upId} ${v2ST(c.seq)} ${v2ST(c.index)} ${v2ST(c.element)} ${v2ST(c.sym)})"
      case c: State.Claim.Def.AdtLit =>
        return st"(${c.newId} ${(for (arg <- c.args) yield v2ST(arg), " ")} ${v2ST(c.sym)})"
      case c: State.Claim.Prop =>
        return if (c.isPos) v2ST(c.value) else st"(not ${v2ST(c.value)})"
      case c: State.Claim.If =>
        val r =
          st"""(ite ${v2ST(c.cond)}
              |  ${andST(c.tClaims)}
              |  ${andST(c.fClaims)}
              |)"""
        return r
    }
  }

  def andST(cs: ISZ[State.Claim]): ST = {
    val r: ST =
      if (cs.size == 0) st"true"
      else if (cs.size == 1) c2ST(cs(0))
      else
        st"""(and
            |  ${(for (c <- cs) yield c2ST(c), "\n")})"""
    return r
  }

  def orST(cs: ISZ[State.Claim]): ST = {
    val r: ST =
      if (cs.size == 0) st"false"
      else if (cs.size == 1) c2ST(cs(0))
      else
        st"""(or
            |  ${(for (c <- cs) yield c2ST(c), "\n")})"""
    return r
  }

  def implyST(cs: ISZ[State.Claim]): ST = {
    val r: ST =
      if (cs.size == 1) c2ST(cs(0))
      else
        st"""(=>
            |  ${(for (c <- cs) yield c2ST(c), "\n")})"""
    return r
  }

  def c2DeclST(c: State.Claim): ISZ[(String, ST)] = {
    def def2DeclST(c: State.Claim.Def): ISZ[(String, ST)] = {
      val symST = v2ST(c.sym)
      return ISZ[(String, ST)](symST.render ~> st"(declare-const $symST ${Smt2.typeId(c.sym.tipe)})")
    }
    c match {
      case c: State.Claim.Prop =>
        val vST = v2ST(c.value)
        return ISZ[(String, ST)](vST.render ~> st"(declare-const $vST ${Smt2.typeId(c.value.tipe)})")
      case c: State.Claim.If =>
        val condST = v2ST(c.cond)
        var r = ISZ[(String, ST)](condST.render ~> st"(declare-const $condST ${Smt2.typeId(c.cond.tipe)})")
        for (tClaim <- c.tClaims) {
          r = r ++ c2DeclST(tClaim)
        }
        for (fClaim <- c.fClaims) {
          r = r ++ c2DeclST(fClaim)
        }
        return r
      case c: State.Claim.Let.CurrentName =>
        var r = def2DeclST(c)
        val n = currentNameId(c)
        val ns = n.render
        r = r :+ ns ~> st"(declare-const $n ${Smt2.typeId(c.sym.tipe)})"
        return r
      case c: State.Claim.Let.Name =>
        var r = def2DeclST(c)
        val n = nameId(c)
        val ns = n.render
        r = r :+ ns ~> st"(declare-const $n ${Smt2.typeId(c.sym.tipe)})"
        return r
      case c: State.Claim.Let.CurrentId =>
        var r = def2DeclST(c)
        val n = currentLocalId(c)
        val ns = n.render
        r = r :+ ns ~> st"(declare-const $n ${Smt2.typeId(c.sym.tipe)})"
        return r
      case c: State.Claim.Let.Id =>
        var r = def2DeclST(c)
        val n = localId(c)
        val ns = n.render
        r = r :+ ns ~> st"(declare-const $n ${Smt2.typeId(c.sym.tipe)})"
        return r
      case c: State.Claim.Def => return def2DeclST(c)
    }
  }
}
