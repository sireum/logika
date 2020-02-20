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
import org.sireum.lang.ast.Typed
import org.sireum.lang.{ast => AST}
import org.sireum.message.Position

@datatype class State(status: B,
                      claims: ISZ[State.Claim],
                      nextFresh: org.sireum.Z) {

  @pure def toST: ST = {
    val r =
      st"""State {
          |  status = $status,
          |  claims = {
          |    ${(for (c <- claims) yield c.toRawST, ",\n")}
          |  },
          |  nextFresh = $nextFresh
          |}"""
    return r
  }

  @pure def addClaim(claim: State.Claim): State = {
    return this (claims = this.claims :+ claim)
  }

  @pure def addClaims(claims: ISZ[State.Claim]): State = {
    return this (claims = this.claims ++ claims)
  }

  @pure def fresh: (State, org.sireum.Z) = {
    return (this (nextFresh = nextFresh + 1), nextFresh)
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

  @datatype trait Value {

    @pure def tipe: AST.Typed

    @pure def toRawST: ST

    @pure def pos: Position

    @pure def toST(defs: HashMap[Z, Claim.Def]): ST = {
      return toRawST
    }
  }


  @datatype trait Fun

  @datatype class IFun(tipe: AST.Typed.Name, id: String) extends Fun

  @datatype class OFun(name: ISZ[String]) extends Fun


  object Value {

    @datatype class Unit(@hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.unit
      }

      @pure override def toRawST: ST = {
        return st"()"
      }
    }

    @datatype class B(value: org.sireum.B, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.b
      }

      @pure override def toRawST: ST = {
        return if (value) st"T" else st"F"
      }
    }

    @datatype class Z(value: org.sireum.Z, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.z
      }

      @pure override def toRawST: ST = {
        return st"$value"
      }
    }

    @datatype class C(value: org.sireum.C, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.c
      }

      @pure override def toRawST: ST = {
        return st"char${Json.Printer.printC(value)}"
      }
    }

    @datatype class F32(value: org.sireum.F32, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f32
      }

      @pure override def toRawST: ST = {
        return st"${value}f"
      }
    }

    @datatype class F64(value: org.sireum.F64, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f64
      }

      @pure override def toRawST: ST = {
        return st"${value}d"
      }
    }

    @datatype class R(value: org.sireum.R, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.r
      }

      @pure override def toRawST: ST = {
        return st"$value"
      }
    }

    @datatype class String(value: org.sireum.String, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.string
      }

      @pure override def toRawST: ST = {
        return Json.Printer.printString(value)
      }
    }

    @datatype trait SubZ extends Value {
      @pure override def tipe: AST.Typed.Name

      @pure override def toRawST: ST = {
        val id = tipe.ids(tipe.ids.size - 1)
        return st"""${ops.StringOps(id).firstToLower}"$valueString""""
      }

      @pure def valueString: org.sireum.String
    }

    @datatype class Range(value: org.sireum.Z, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S8(value: org.sireum.S8, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S16(value: org.sireum.S16, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S32(value: org.sireum.S32, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S64(value: org.sireum.S64, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U8(value: org.sireum.U8, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U16(value: org.sireum.U16, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U32(value: org.sireum.U32, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U64(value: org.sireum.U64, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class Enum(val tipe: AST.Typed.Name, owner: ISZ[org.sireum.String], id: org.sireum.String,
                         ordinal: org.sireum.Z, @hidden val pos: Position) extends Value {
      @strictpure override def toRawST: ST = st"${(owner, ".")}.$id"
    }

    @datatype class Sym(num: org.sireum.Z, @hidden val tipe: AST.Typed, @hidden val pos: Position) extends Value {

      @pure override def toRawST: ST = {
        return st"$symPrefix$num@[${pos.beginLine},${pos.beginColumn}]"
      }

      @pure override def toST(defs: HashMap[org.sireum.Z, Claim.Def]): ST = {
        defs.get(num) match {
          case Some(d) => return d.toST(defs)
          case _ => halt("Infeasible")
        }
      }
    }

  }

  @record class ClaimSTs(var value: ISZ[ST]) {
    def add(st: ST): Unit = {
      value = value :+ st
    }
  }

  @datatype trait Claim {

    @pure def toRawST: ST

    def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit

    @pure def funs: ISZ[Fun] = {
      return ISZ()
    }

    @pure def types: ISZ[AST.Typed]

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

    def collectDefs(defs: Claim.Defs): Unit = {
      def rec(c: Claim): Unit = {
        c match {
          case c: Claim.Let.CurrentId =>
            if (!defs.hasDef(c)) {
              defs.addDef(c)
            }
          case c: Claim.Let.CurrentName =>
            if (!defs.hasDef(c)) {
              defs.addDef(c)
            }
          case c: Claim.Let.Id =>
            if (!defs.hasDef(c)) {
              defs.addDef(c)
            }
          case c: Claim.Let.Name =>
            if (!defs.hasDef(c)) {
              defs.addDef(c)
            }
          case c: Claim.Def => defs.addDef(c)
          case _ =>
        }
        c match {
          case c: Claim.Composite =>
            for (cc <- c.claims) {
              rec(cc)
            }
          case _ =>
        }
      }
      rec(this)
    }

  }

  object Claim {

    @datatype trait Composite extends Claim {
      @pure def claims: ISZ[Claim]
    }

    @datatype class Prop(isPos: B, value: Value.Sym) extends Claim {
      @pure override def toRawST: ST = {
        return if (isPos) value.toRawST else st"¬(${value.toRawST})"
      }

      override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
        if (isPos) {
          claimSTs.add(value.toST(defs))
        } else {
          claimSTs.add(st"¬(${value.toST(defs)})")
        }
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(value.tipe)
      }
    }


    @datatype class And(val claims: ISZ[Claim]) extends Composite {
      @pure def toRawST: ST = {
        val r: ST =
          if (claims.size == 0) st"T"
          else if (claims.size == 1) claims(0).toRawST
          else
            st"""∧(
                |  ${(for (c <- claims) yield c.toRawST, ",\n")}
                |)"""
        return r
      }

      @pure def toST(defs: HashMap[Z, Claim.Def]): ST = {
        val claimSTs = ClaimSTs(ISZ())
        for (c <- claims) {
          c.toSTs(claimSTs, defs)
        }
        val r: ST =
          if (claimSTs.value.size == 0) st"T"
          else if (claimSTs.value.size == 1) claimSTs.value(0)
          else
            st"""∧(
                |  ${(claimSTs.value, ",\n")}
                |)"""
        return r
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }

      override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
        claimSTs.add(toST(defs))
      }
    }

    @datatype class Or(val claims: ISZ[Claim]) extends Composite {
      @pure def toRawST: ST = {
        val r: ST =
          if (claims.size == 0) st"F"
          else if (claims.size == 1) claims(0).toRawST
          else
            st"""∨(
                |  ${(for (c <- claims) yield c.toRawST, ",\n")})"""
        return r
      }

      @pure def toST(defs: HashMap[Z, Claim.Def]): ST = {
        val claimSTs = ClaimSTs(ISZ())
        for (c <- claims) {
          c.toSTs(claimSTs, defs)
        }
        val r: ST =
          if (claimSTs.value.size == 0) st"F"
          else if (claimSTs.value.size == 1) claimSTs.value(0)
          else
            st"""∨(
                |  ${(claimSTs.value, ",\n")}
                |)"""
        return r
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }

      override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
        claimSTs.add(toST(defs))
      }
    }

    @datatype class Imply(val claims: ISZ[Claim]) extends Composite {
      @pure def toRawST: ST = {
        val r: ST =
          if (claims.size == 2)
            st"""${claims(0).toRawST} →
                |  ${claims(1).toRawST}"""
          else
            st"""→(
                |  ${(for (c <- claims) yield c.toRawST, ",\n")})"""
        return r
      }

      @pure def toST(defs: HashMap[Z, Claim.Def]): ST = {
        val claimSTs = ClaimSTs(ISZ())
        for (c <- claims) {
          c.toSTs(claimSTs, defs)
        }
        val r: ST =
          if (claimSTs.value.size == 1 && claims.size == 2) st"T"
          else if (claimSTs.value.size == 2)
            st"""${claimSTs.value(0)} →
                |  ${claimSTs.value(1)}"""
          else
            st"""→(
                |  ${(claimSTs.value, ",\n")}
                |)"""
        return r
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }

      override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
        claimSTs.add(toST(defs))
      }
    }

    @datatype class If(cond: Value.Sym,
                       tClaims: ISZ[Claim],
                       fClaims: ISZ[Claim]) extends Composite {

      @strictpure override def claims: ISZ[Claim] = tClaims ++ fClaims

      @pure override def toRawST: ST = {
        val r =
          st"""${cond.toRawST} ?
              |  ${And(tClaims).toRawST}
              |: ${And(fClaims).toRawST}"""
        return r
      }

      override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
        claimSTs.add(
          st"""${cond.toST(defs)} ?
              |  ${And(tClaims).toST(defs)}
              |: ${And(fClaims).toST(defs)}""")
      }

      @pure def types: ISZ[AST.Typed] = {
        return cond.tipe +: ((for (tClaim <- tClaims; t <- tClaim.types) yield t) ++
          (for (fClaim <- fClaims; t <- fClaim.types) yield t))
      }
    }

    @datatype trait Def extends Claim {
      @pure def sym: Value.Sym

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(sym.tipe)
      }

      @pure def toST(defs: HashMap[Z, Claim.Def]): ST

      override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {}
    }

    @record class Defs(var value: HashMap[Z, Def]) {
      def addDef(d: Claim.Def): Unit = {
        value = value + d.sym.num ~> d
      }
      def hasDef(d: Claim.Def): B = {
        return value.contains(d.sym.num)
      }
    }

    object Defs {
      @strictpure def empty: Defs = Defs(HashMap.empty)
    }

    object Def {

      @datatype class SeqLit(val sym: Value.Sym, args: ISZ[(Value, Value)]) extends Def {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg._2.toRawST, ", ")})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${sym.tipe.string}(${(for (arg <- args) yield arg._2.toST(defs), ", ")})"
        }
      }

      @datatype class SeqStore(val sym: Value.Sym, seq: Value, index: Value, element: Value) extends Def {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${seq.toRawST}(${index.toRawST} ~> ${element.toRawST})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${seq.toST(defs)}(${index.toST(defs)} ~> ${element.toST(defs)})"
        }
      }

      @datatype class FieldStore(val sym: Value.Sym, adt: Value, id: String, value: Value) extends Def {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${adt.toRawST}($id = ${value.toRawST})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${adt.toST(defs)}($id = ${value.toST(defs)})"
        }
      }

      @datatype class AdtLit(val sym: Value.Sym, args: ISZ[Value]) extends Def {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${sym.tipe.string}(${(for (arg <- args) yield arg.toST(defs), ", ")})"
        }
      }

    }

    @datatype trait Let extends Def

    object Let {

      @datatype class CurrentName(val sym: Value.Sym, ids: ISZ[String],
                                  @hidden defPosOpt: Option[Position]) extends Let {
        @pure override def toRawST: ST = {
          return st"${(ids, ".")} == ${sym.toRawST}"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${(ids, ".")}"
        }

        override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
          if (defs.get(sym.num).get != this) {
            claimSTs.add(st"${toST(defs)} == ${sym.toST(defs)}")
          }
        }
      }

      @datatype class Name(val sym: Value.Sym, ids: ISZ[String], num: Z, poss: ISZ[Position]) extends Let {
        @pure override def toRawST: ST = {
          return st"${(ids, ".")}@${possLines(poss)}#$num == ${sym.toRawST}"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${(ids, ".")}@${possLines(poss)}#$num"
        }

        override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
          if (defs.get(sym.num).get != this) {
            claimSTs.add(st"${toST(defs)} == ${sym.toST(defs)}")
          }
        }
      }

      @datatype class CurrentId(val sym: Value.Sym, context: ISZ[String], id: String,
                                @hidden defPosOpt: Option[Position]) extends Let {
        @pure override def toRawST: ST = {
          return st"$id == ${sym.toRawST}"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"$id"
        }

        override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
          if (defs.get(sym.num).get != this) {
            claimSTs.add(st"${toST(defs)} == ${sym.toST(defs)}")
          }
        }
     }

      @datatype class Id(val sym: Value.Sym, context: ISZ[String], id: String, num: Z, poss: ISZ[Position]) extends Let {

        @pure override def toRawST: ST = {
          return if (context.isEmpty) st"$id@${possLines(poss)}#$num == ${sym.toRawST}"
          else st"$id:${(context, ".")}@${possLines(poss)}#$num == ${sym.toRawST}"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return if (context.isEmpty) st"$id@${possLines(poss)}#$num"
          else st"$id:${(context, ".")}@${possLines(poss)}#$num"
        }

        override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
          if (defs.get(sym.num).get != this) {
            claimSTs.add(st"${toST(defs)} == ${sym.toST(defs)}")
          }
        }
      }

      @datatype class Eq(val sym: Value.Sym, value: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${value.toRawST}"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${value.toST(defs)}"
        }

        override def toSTs(claimSTs: ClaimSTs, defs: HashMap[Z, Claim.Def]): Unit = {
          claimSTs.add(st"${sym.toST(defs)} == ${value.toST(defs)}")
        }
      }

      object Quant {
        @datatype class Var(id: String, tipe: AST.Typed) {
          @pure def toST: ST = {
            return st"$id: ${tipe.string}"
          }
        }
      }

      @datatype class Quant(val sym: Value.Sym,
                            isAll: B, vars: ISZ[Quant.Var],
                            val claims: ISZ[Claim]) extends Let with Composite {
        @pure override def toRawST: ST = {
          val r =
            st"""${sym.toRawST} ≜ ${if (isAll) "∀" else "∃"} ${(for (x <- vars) yield x.toST, ", ")}
                |  ${if (isAll) Claim.Imply(claims).toRawST else Claim.And(claims).toRawST}"""
          return r
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          val r =
            st"""${if (isAll) "∀" else "∃"} ${(for (x <- vars) yield x.toST, ", ")}
                |  ${if (isAll) Claim.Imply(claims).toST(defs) else Claim.And(claims).toST(defs)}"""
          return r
        }

        @pure override def types: ISZ[Typed] = {
          return sym.tipe +: (for (claim <- claims; t <- claim.types) yield t)
        }
      }

      @datatype class Binary(val sym: Value.Sym, left: Value, op: String, right: Value, tipe: AST.Typed) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${left.toRawST} $op ${right.toRawST}"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${left.toST(defs)} $op ${right.toST(defs)}"
        }
      }

      @datatype class Unary(val sym: Value.Sym, op: AST.Exp.UnaryOp.Type, value: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ $opString${value.toRawST}"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"$opString${value.toST(defs)}"
        }

        @strictpure def opString: String = op match {
          case AST.Exp.UnaryOp.Complement => "~"
          case AST.Exp.UnaryOp.Minus => "-"
          case AST.Exp.UnaryOp.Not => "!"
          case AST.Exp.UnaryOp.Plus => "+"
        }
      }

      @datatype class SeqLookup(val sym: Value.Sym, seq: Value, index: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${seq.toRawST}(${index.toRawST})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${seq.toST(defs)}(${index.toST(defs)})"
        }
      }

      @datatype class SeqInBound(val sym: Value.Sym, seq: Value, index: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ inBound(${seq.toRawST}, ${index.toRawST})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"inBound(${seq.toST(defs)}, ${index.toST(defs)})"
        }
      }

      @datatype class FieldLookup(val sym: Value.Sym, adt: Value, id: String) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${adt.toRawST}.$id"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${adt.toST(defs)}.$id"
        }
      }

      @datatype class Apply(val sym: Value.Sym, name: ISZ[String], args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${(name, ".")}(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${(name, ".")}(${(for (arg <- args) yield arg.toST(defs), ", ")})"
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ(OFun(name))
        }
      }

      @datatype class IApply(val sym: Value.Sym, o: Value, oTipe: AST.Typed.Name, id: String, args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${o.toRawST}.$id(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return st"${o.toST(defs)}.$id(${(for (arg <- args) yield arg.toST(defs), ", ")})"
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ(IFun(oTipe, id))
        }
      }

      @datatype class And(val sym: Value.Sym, args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (args.size == 0) st"F"
          else if (args.size == 1) st"${sym.toRawST} ≜ ${args(0).toRawST}"
          else if (args.size == 2) st"${sym.toRawST} ≜ ${args(0).toRawST} ∧ ${args(1).toRawST}"
          else st"${sym.toRawST} ≜ ∧(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return if (args.size == 0) st"F"
          else if (args.size == 1) st"${args(0).toST(defs)}"
          else if (args.size == 2) st"${args(0).toST(defs)} ∧ ${args(1).toST(defs)}"
          else st"∧(${(for (arg <- args) yield arg.toST(defs), ", ")})"
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ()
        }
      }

      @datatype class Or(val sym: Value.Sym, args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (args.size == 0) st"T"
          else if (args.size == 1) st"${sym.toRawST} ≜ ${args(0).toRawST}"
          else if (args.size == 2) st"${sym.toRawST} ≜ ${args(0).toRawST} ∨ ${args(1).toRawST}"
          else st"${sym.toRawST} ≜ ∨(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return if (args.size == 0) st"T"
          else if (args.size == 1) st"${args(0).toST(defs)}"
          else if (args.size == 2) st"${args(0).toST(defs)} ∨ ${args(1).toST(defs)}"
          else st"∨(${(for (arg <- args) yield arg.toST(defs), ", ")})"
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ()
        }
      }

      @datatype class Imply(val sym: Value.Sym, args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (args.size == 2) st"${sym.toRawST} ≜ ${args(0).toRawST} → ${args(1).toRawST}"
          else st"${sym.toRawST} ≜ →(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        @pure override def toST(defs: HashMap[Z, Claim.Def]): ST = {
          return if (args.size == 2) st"${args(0).toST(defs)} → ${args(1).toST(defs)}"
          else st"→(${(for (arg <- args) yield arg.toST(defs), ", ")})"
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ()
        }
      }
    }

    @pure def claimsSTs(claims: ISZ[Claim], defs: Claim.Defs): ISZ[ST] = {
      for (c <- claims) {
        c.collectDefs(defs)
      }
      val claimSTs = ClaimSTs(ISZ())
      val m = defs.value
      for (c <- claims) {
        c.toSTs(claimSTs, m)
      }
      return claimSTs.value
    }

    @pure def claimsRawSTs(claims: ISZ[Claim]): ISZ[ST] = {
      return for (c <- claims) yield c.toRawST
    }

    @pure def possLines(poss: ISZ[Position]): ST = {
      return if (poss.size > 1) st"{${(for (pos <- poss) yield pos.beginLine, ", ")}}"
      else st"${poss(0).beginLine}"
    }

  }


}
