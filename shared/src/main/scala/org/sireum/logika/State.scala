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
import org.sireum.message.Position

@datatype class State(status: B,
                      claims: ISZ[State.Claim],
                      nextFresh: org.sireum.Z) {

  @pure def toST: ST = {
    val r =  st"""State {
                 |  status = $status,
                 |  claims = {
                 |    ${(for (c <- claims) yield c.toST, ",\n")}
                 |  },
                 |  nextFresh = $nextFresh
                 |}"""
    return r
  }

  @pure def addClaim(claim: State.Claim): State = {
    return this(claims = this.claims :+ claim)
  }

  @pure def addClaims(claims: ISZ[State.Claim]): State = {
    return this(claims = this.claims ++ claims)
  }

  @pure def fresh: (State, org.sireum.Z) = {
    return (this(nextFresh = nextFresh + 1), nextFresh)
  }

  @pure def freshSym(tipe: AST.Typed, pos: Position): (State, State.Value.Sym) = {
    val (newState, n) = fresh
    return (newState, State.Value.Sym(n, tipe, pos))
  }

}

object State {
  type Scope = ISZ[String]
  type Address = org.sireum.Z

  val symPrefix: String = "α"
  val errorValue: Value.Sym = Value.Sym(0, AST.Typed.nothing, Position.none)

  @memoize def create: State = {
    return State(T, ISZ(), 1)
  }

  @pure def smtTypeId(t: AST.Typed): ST = {
    return smtId(t, "")
  }

  @pure def smtTypeHierarchyId(t: AST.Typed): ST = {
    return smtId(t, "T")
  }

  @pure def smtTypeConstructorId(t: AST.Typed): ST = {
    return smtId(t, "C")
  }

  @pure def smtId(t: AST.Typed, prefix: String): ST = {
    t match {
      case t: AST.Typed.Name =>
        shorten(t) match {
          case Some((r, raw)) => return if (raw) r else st"|$r|"
          case _ =>
            if (t.args.nonEmpty) {
              return if (prefix == "") st"|${(t.ids, ".")}[${(for (arg <- t.args) yield smtIdRaw(arg), ", ")}]|"
              else st"|$prefix:${(t.ids, ".")}[${(for (arg <- t.args) yield smtIdRaw(arg), ", ")}]|"
            } else {
              return if (prefix == "") st"|${(t.ids, ".")}|" else st"|$prefix:${(t.ids, ".")}|"
            }
        }
      case _ => return if (prefix == "") st"|${smtIdRaw(t)}|" else st"|$prefix:${smtIdRaw(t)}|"
    }
  }

  @pure def smtIdRaw(t: AST.Typed): ST = {
    t match {
      case t: AST.Typed.Name =>
        shorten(t) match {
          case Some((r, _)) => return r
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

  @pure def shorten(t: AST.Typed.Name): Option[(ST, B)] = {
    if (t.ids.size == 3 && t.ids(0) == "org" && t.ids(1) == "sireum") {
      val tid = t.ids(2)
      if (tid == "IS" || tid == "MS") {
        val it = t.args(0).asInstanceOf[AST.Typed.Name]
        return Some((st"$tid[${smtIdRaw(it)}, ${smtIdRaw(t.args(1))}]", F))
      } else if (t.args.isEmpty) {
        return Some((st"${t.ids(2)}", T))
      }
    }
    return None()
  }

  @datatype trait Value {

    @pure def tipe: AST.Typed

    @pure def toST: ST

    @pure def pos: Position

    @pure def toSmt: ST
  }


  @datatype trait Fun

  @datatype class IFun(tipe: AST.Typed.Name, id: String) extends Fun

  @datatype class OFun(name: ISZ[String]) extends Fun


  object Value {

    @datatype class B(value: org.sireum.B, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.b
      }

      @pure override def toST: ST = {
        return if (value) st"T" else st"F"
      }

      @pure override def toSmt: ST = {
        return if (value) st"true" else st"false"
      }
    }

    @datatype class Z(value: org.sireum.Z, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.z
      }

      @pure override def toST: ST = {
        return st"$value"
      }

      @pure override def toSmt: ST = {
        return toST
      }
    }

    @datatype class C(value: org.sireum.C, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.c
      }

      @pure override def toST: ST = {
        return st"char${Json.Printer.printC(value)}"
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class F32(value: org.sireum.F32, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f32
      }

      @pure override def toST: ST = {
        return st"${value}f"
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class F64(value: org.sireum.F64, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f64
      }

      @pure override def toST: ST = {
        return st"${value}d"
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class R(value: org.sireum.R, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.r
      }

      @pure override def toST: ST = {
        return st"$value"
      }

      @pure override def toSmt: ST = {
        return toST
      }
    }

    @datatype class String(value: org.sireum.String, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.string
      }

      @pure override def toST: ST = {
        return Json.Printer.printString(value)
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype trait SubZ extends Value {
      @pure override def tipe: AST.Typed.Name

      @pure override def toST: ST = {
        val id = tipe.ids(tipe.ids.size - 1)
        return st"""${ops.StringOps(id).firstToLower}"$valueString""""
      }

      @pure def valueString: org.sireum.String
    }

    @datatype class Range(value: org.sireum.Z, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        return st"$value"
      }
    }

    @datatype class S8(value: org.sireum.S8, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class S16(value: org.sireum.S16, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class S32(value: org.sireum.S32, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class S64(value: org.sireum.S64, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class U8(value: org.sireum.U8, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class U16(value: org.sireum.U16, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class U32(value: org.sireum.U32, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class U64(value: org.sireum.U64, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }

      @pure override def toSmt: ST = {
        halt("TODO") // TODO
      }
    }

    @datatype class Sym(num: org.sireum.Z, @hidden val tipe: AST.Typed, @hidden val pos: Position) extends Value {

      @pure override def toST: ST = {
        return st"$symPrefix$num@[${pos.beginLine}:${pos.beginColumn}]"
      }

      @pure override def toSmt: ST = {
        return st"cx!$num"
      }
    }

  }

  @datatype trait Claim {

    @pure def toST: ST

    @pure def toSmt: ST

    @pure def toSmtDecl: HashSMap[String, ST]

    @pure def funs: ISZ[Fun] = {
      return ISZ()
    }

    @pure def types: ISZ[AST.Typed]

    @memoize def toSmtString: String = {
      return toSmt.render
    }

    @memoize def toSmtDeclString: ISZ[(String, String)] = {
      return (HashSMap.empty[String, String] ++ (for(p <- toSmtDecl.entries) yield (p._1, p._2.render))).entries
    }

    @memoize def funsMem: ISZ[State.Fun] = {
      return (HashSSet.empty[State.Fun] ++ funs).elements
    }

    @memoize def typeNames: ISZ[AST.Typed.Name] = {
      var r = HashSSet.empty[AST.Typed.Name]
      for (t <- types) {
        t match {
          case t: AST.Typed.Name => r = r + t
          case _ =>
        }
      }
      return r.elements
    }

  }

  object Claim {

    @datatype class And(claims: ISZ[Claim]) extends Claim {
      @pure override def toST: ST = {
        val r: ST =
          if (claims.size == 0) st"T"
          else if (claims.size == 1) claims(0).toST
          else
            st"""∧(
                |  ${(for (c <- claims) yield c.toST, ",\n")}
                |)"""
        return r
      }

      @pure override def toSmt: ST = {
        val r: ST =
          if (claims.size == 0) st"true"
          else if (claims.size == 1) claims(0).toSmt
          else
            st"""(and
                |  ${(for (c <- claims) yield c.toSmt, "\n")}
                |)"""
        return r
      }

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        var r = HashSMap.empty[String, ST]
        for (c <- claims) {
          r = r ++ c.toSmtDecl.entries
        }
        return r
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }
    }

    @datatype class Or(claims: ISZ[Claim]) extends Claim {
      @pure override def toST: ST = {
        val r: ST =
          if (claims.size == 0) st"F"
          else if (claims.size == 1) claims(0).toST
          else
            st"""∨(
                |  ${(for (c <- claims) yield c.toST, ",\n")}
                |)"""
        return r
      }

      @pure override def toSmt: ST = {
        val r: ST =
          if (claims.size == 0) st"false"
          else if (claims.size == 1) claims(0).toSmt
          else
            st"""(or
                |  ${(for (c <- claims) yield c.toSmt, "\n")}
                |)"""
        return r
      }

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        var r = HashSMap.empty[String, ST]
        for (c <- claims) {
          r = r ++ c.toSmtDecl.entries
        }
        return r
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }
    }

    @datatype class Imply(claims: ISZ[Claim]) extends Claim {
      @pure override def toST: ST = {
        val r =  st"""→(
                     |  ${(for (c <- claims) yield c.toST, ",\n")}
                     |)"""
        return r
      }

      @pure override def toSmt: ST = {
        val r = st"""(=>
                    |  ${(for (c <- claims) yield c.toSmt, "\n")}
                    |)"""
        return r
      }

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        var r = HashSMap.empty[String, ST]
        for (c <- claims) {
          r = r ++ c.toSmtDecl.entries
        }
        return r
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }
    }

    @datatype class Quant(isAll: B, ids: ISZ[Def.CurrentId], tipe: AST.Typed, claims: ISZ[Claim], sym: State.Value.Sym)
      extends Claim {
      @pure override def toST: ST = {
        val r =
          st"""${if (isAll) "∀" else "∃"} ${(for (id <- ids) yield id.toST, ", ")} : ${tipe.string}
              |  ${(for (claim <- claims) yield claim.toST, "\n")}
              |  ${sym.toST}"""
        return r
      }

      @pure override def toSmt: ST = {
        val t = State.smtTypeId(sym.tipe)
        val r =
          st"""(${if (isAll) "forall" else "exists"} (${(for (id <- ids) yield st"(${id.toSmt} $t)", " ")})
              |  (and
              |    ${(for (claim <- claims) yield claim.toSmt, "\n")}
              |    ${sym.toSmt}
              |  )
              |)"""
        return r
      }

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        var r = HashSMap.empty[String, ST]
        for (c <- claims) {
          r = r ++ c.toSmtDecl.entries
        }
        return r --
          (for (id <- ids) yield id.smt2name.render) --
          (for (id <- ids) yield id.sym.toSmt.render)
      }

      @pure def types: ISZ[AST.Typed] = {
        return tipe +: (for (claim <- claims; t <- claim.types) yield t) :+ sym.tipe
      }
    }

    @datatype class Neg(claim: Claim) extends Claim {
      @pure override def toST: ST = {
        return st"¬(${claim.toST})"
      }

      @pure override def toSmt: ST = {
        return st"(not ${claim.toSmt})"
      }

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        return claim.toSmtDecl
      }

      @pure def types: ISZ[AST.Typed] = {
        return claim.types
      }
    }

    @datatype class Prop(value: Value.Sym) extends Claim {
      @pure override def toST: ST = {
        return value.toST
      }

      @pure override def toSmt: ST = {
        return value.toSmt
      }

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        return HashSMap.empty[String, ST] + value.toSmt.render ~>
          st"(declare-const ${value.toSmt} ${State.smtTypeId(value.tipe)})"
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(value.tipe)
      }
    }

    @datatype class If(sym: Value.Sym,
                       tClaims: ISZ[Claim],
                       fClaims: ISZ[Claim]) extends Claim {

      @pure override def toST: ST = {
        val r =
          st"""${sym.toST} ?
              |  ${And(tClaims).toST}
              |  ${And(fClaims).toST}"""
        return r
      }

      @pure override def toSmt: ST = {
        val r =
          st"""(ite ${sym.toSmt}
              |  ${And(tClaims).toSmt}
              |  ${And(fClaims).toSmt}
              |)"""
        return r
      }

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        var r = HashSMap.empty[String, ST] +
          sym.toSmt.render ~> st"(declare-const ${sym.toSmt} ${State.smtTypeId(sym.tipe)})"
        for (tClaim <- tClaims) {
          r = r ++ tClaim.toSmtDecl.entries
        }
        for (fClaim <- fClaims) {
          r = r ++ fClaim.toSmtDecl.entries
        }
        return r
      }

      @pure def types: ISZ[AST.Typed] = {
        return sym.tipe +: ((for (tClaim <- tClaims; t <- tClaim.types) yield t) ++
          (for (fClaim <- fClaims; t <- fClaim.types) yield t))
      }
    }

    @datatype trait Def extends Claim {
      def sym: Value.Sym

      @pure override def toSmtDecl: HashSMap[String, ST] = {
        return HashSMap.empty[String, ST] + sym.toSmt.render ~>
          st"(declare-const ${sym.toSmt} ${State.smtTypeId(sym.tipe)})"
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(sym.tipe)
      }
    }

    object Def {

      val binop2Smt2Map: HashMap[AST.Typed.Name, HashMap[String, String]] =
        HashMap.empty[AST.Typed.Name, HashMap[String, String]] ++
          ISZ[(AST.Typed.Name, HashMap[String, String])](
            AST.Typed.b ~> (HashMap.empty[String, String] ++ ISZ(
              AST.Exp.BinaryOp.And ~> "and",
              AST.Exp.BinaryOp.Or ~> "or",
              AST.Exp.BinaryOp.Imply ~> "implies"
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

      @datatype class CurrentName(val sym: Value.Sym, ids: ISZ[String],
                                  @hidden defPosOpt: Option[Position]) extends Def {
        @pure override def toST: ST = {
          return st"${(ids, ".")} == ${sym.toST}"
        }

        @pure override def toSmt: ST = {
          return st"(= $smt2name ${sym.toSmt})"
        }

        @pure override def toSmtDecl: HashSMap[String, ST] = {
          var r = super.toSmtDecl
          val n = smt2name
          val ns = n.render
          if (!r.contains(ns)) {
            r = r + ns ~> st"(declare-const $n ${State.smtTypeId(sym.tipe)})"
          }
          return r
        }

        @memoize def smt2name: ST = {
          return st"|g:${(ids, ".")}|"
        }
      }

      @datatype class Name(val sym: Value.Sym, ids: ISZ[String], num: Z, poss: ISZ[Position]) extends Def {
        @pure override def toST: ST = {
          return st"${(ids, ".")}@$possLines:$num == ${sym.toST}"
        }

        @pure override def toSmt: ST = {
          return st"(= $smt2name ${sym.toSmt})"
        }

        @pure override def toSmtDecl: HashSMap[String, ST] = {
          var r = super.toSmtDecl
          val n = smt2name
          val ns = n.render
          if (!r.contains(ns)) {
            r = r + ns ~> st"(declare-const $n ${State.smtTypeId(sym.tipe)})"
          }
          return r
        }

        @memoize def smt2name: ST = {
          return st"|g:${(ids, ".")}@$possLines:$num|"
        }

        @pure def possLines: ST = {
          return if (poss.size > 1) st"{${(for (pos <- poss) yield pos.beginLine, ", ")}}"
          else st"${poss(0).beginLine}"
        }
      }

      @datatype class CurrentId(val sym: Value.Sym, context: ISZ[String], id: String,
                                @hidden defPosOpt: Option[Position]) extends Def {
        @pure override def toST: ST = {
          return st"$id == ${sym.toST}"
        }

        @pure override def toSmt: ST = {
          return st"(= |l:$id| ${sym.toSmt})"
        }

        @pure override def toSmtDecl: HashSMap[String, ST] = {
          var r = super.toSmtDecl
          val n = smt2name
          val ns = n.render
          if (!r.contains(ns)) {
            r = r + ns ~> st"(declare-const $n ${State.smtTypeId(sym.tipe)})"
          }
          return r
        }

        @memoize def smt2name: ST = {
          return st"|l:$id|"
        }
      }

      @datatype class Id(val sym: Value.Sym, context: ISZ[String], id: String, num: Z, poss: ISZ[Position]) extends Def {

        @pure override def toST: ST = {
          return if (context.isEmpty) st"$id@$possLines:$num == ${sym.toST}"
          else st"$id:${(context, ".")}@$possLines:$num == ${sym.toST}"
        }

        @pure override def toSmt: ST = {
          return st"(= $smt2name ${sym.toSmt})"
        }

        @pure override def toSmtDecl: HashSMap[String, ST] = {
          var r = super.toSmtDecl
          val n = smt2name
          val ns = n.render
          if (!r.contains(ns)) {
            r = r + ns ~> st"(declare-const $n ${State.smtTypeId(sym.tipe)})"
          }
          return r
        }

        @memoize def smt2name: ST = {
          return if (context.isEmpty) st"|l:$id@$possLines:$num|" else st"|l:$id:${(context, ".")}@$possLines:$num|"
        }

        @pure def possLines: ST = {
          return if (poss.size > 1) st"{${(for (pos <- poss) yield pos.beginLine, ", ")}}"
          else st"${poss(0).beginLine}"
        }
      }

      @datatype class Eq(val sym: Value.Sym, value: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${value.toST}"
        }

        @pure override def toSmt: ST = {
          return st"(= ${sym.toSmt} ${value.toSmt})"
        }
      }

      @datatype class Binary(val sym: Value.Sym, left: Value, op: String, right: Value, tipe: AST.Typed.Name) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${left.toST} $op ${right.toST}"
        }

        @pure override def toSmt: ST = {
          var neg: B = F
          val binop: String = if (op == "!=") {
            neg = T
            "=="
          } else {
            op
          }
          val r: ST = binop2Smt2Map.get(tipe) match {
            case Some(m) => st"(= ${sym.toSmt} (${m.get(binop).get} ${left.toSmt} ${right.toSmt}))"
            case _ =>
              halt("TODO") // TODO
          }
          return if (neg) st"(not $r)" else r
        }
      }

      @datatype class Unary(val sym: Value.Sym, op: AST.Exp.UnaryOp.Type, value: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ $op ${value.toST}"
        }

        @pure override def toSmt: ST = {
          unop2Smt2Map.get(sym.tipe) match {
            case Some(m) => return st"(= ${sym.toSmt} (${m.get(op).get} ${sym.toSmt}))"
            case _ =>
              halt("TODO") // TODO
          }
        }
      }

      @datatype class SeqStore(val sym: Value.Sym, seq: Value, index: Value, element: Value, @hidden upId: ST) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @${seq.toST}(${index.toST} ~> ${element.toST})"
        }

        @pure override def toSmt: ST = {
          return st"($upId ${seq.toSmt} ${index.toSmt} ${element.toSmt} ${sym.toSmt})"
        }
      }

      @datatype class SeqLookup(val sym: Value.Sym, seq: Value, index: Value, @hidden atId: ST) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @${seq.toST}(${index.toST})"
        }

        @pure override def toSmt: ST = {
          return st"($atId ${seq.toSmt} ${index.toSmt} ${sym.toSmt})"
        }
      }

      @datatype class FieldStore(val sym: Value.Sym, adt: Value, id: ST, value: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @$adt($id = ${value.toST})"
        }

        @pure override def toSmt: ST = {
          halt("TODO") // TODO
        }
      }

      @datatype class FieldLookup(val sym: Value.Sym, adt: Value, id: ST) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @$adt.$id"
        }

        @pure override def toSmt: ST = {
          return st"(= ${sym.toSmt} ($id ${adt.toSmt}))"
        }
      }

      @datatype class Apply(val sym: Value.Sym, name: ISZ[String], args: ISZ[Value]) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${(name, ".")}(${(for (arg <- args) yield arg.toST, ", ")})"
        }

        @pure override def toSmt: ST = {
          halt("TODO") // TODO
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ(OFun(name))
        }
      }

      @datatype class IApply(val sym: Value.Sym, o: Value, oTipe: AST.Typed.Name, id: String, args: ISZ[Value]) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${o.toST}.$id(${(for (arg <- args) yield arg.toST, ", ")})"
        }

        @pure override def toSmt: ST = {
          halt("TODO") // TODO
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ(IFun(oTipe, id))
        }
      }

      @datatype class AdtLit(val sym: Value.Sym, @hidden params: ISZ[ST], args: ISZ[Value]) extends Def {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg.toST, ", ")})"
        }

        @pure override def toSmt: ST = {
          val symST = sym.toSmt
          val r =  st"""(and
                       |  (= (type-of $symST) ${State.smtTypeHierarchyId(sym.tipe)})
                       |  ${(for (p <- ops.ISZOps(params).zip(args)) yield st"(= (${p._1} $symST) ${p._2.toSmt})", "\n")})"""
          return r
        }
      }

      @datatype class SeqLit(val sym: Value.Sym, args: ISZ[(Value, Value)], @hidden sizeId: ST, @hidden atId: ST) extends Def {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg._2.toST, ", ")})"
        }

        @pure override def toSmt: ST = {
          val symST = sym.toSmt
          val r =  st"""(and
                       |  (= ($sizeId $symST) ${args.size})
                       |  ${(for (arg <- args) yield st"($atId $symST ${arg._1.toSmt} ${arg._2.toSmt})", "\n")})"""
          return r
        }
      }

    }
  }
}
