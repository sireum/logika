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
import org.sireum.lang.ast.Typed
import org.sireum.lang.{ast => AST}
import org.sireum.message.Position

@datatype class State(val status: State.Status.Type,
                      val claims: ISZ[State.Claim],
                      val nextFresh: org.sireum.Z) {

  @strictpure def ok: B = status == State.Status.Normal

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

  @strictpure override def string: String = toST.render

  @pure def addClaim(claim: State.Claim): State = {
    val thisL = this
    return thisL(claims = this.claims :+ claim)
  }

  @pure def addClaims(claims: ISZ[State.Claim]): State = {
    if (claims.isEmpty) {
      return this
    }
    val thisL = this
    return thisL(claims = this.claims ++ claims)
  }

  @pure def fresh: (State, org.sireum.Z) = {
    val thisL = this
    return (thisL(nextFresh = nextFresh + 1), nextFresh)
  }

  @pure def freshSym(tipe: AST.Typed, pos: Position): (State, State.Value.Sym) = {
    val (newState, n) = fresh
    return (newState, State.Value.sym(n, tipe, pos))
  }

  @pure def unconstrainedClaims: (State, ISZ[(Z, Z)]) = {
    var r = ISZ[State.Claim]()
    var r2 = ISZ[(Z, Z)]()
    for (i <- 0 until claims.size) {
      val c = claims(i)
      val add: B = c match {
        case _: State.Claim.Let.Id => T
        case _: State.Claim.Let.Name => T
        case _: State.Claim.Let.CurrentId => T
        case _: State.Claim.Let.CurrentName => T
        case _: State.Claim.Old => T
        case _ => F
      }
      if (add) {
        r = r :+ c
        r2 = r2 :+ (i, r.size - 1)
      }
    }
    val thisL = this
    return (thisL(claims = r), r2)
  }

}

object State {
  type Scope = ISZ[String]

  @enum object Status {
    "Normal"
    "End"
    "Error"
  }

  @strictpure def statusOf(ok: B): Status.Type = if (ok) Status.Normal else Status.Error

  @datatype trait Value {

    @pure def tipe: AST.Typed

    @pure def toRawST: ST

    @pure def pos: Position

    def toSTOpt(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
      return Some(toRawST)
    }

    def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): ST = {
      return toRawST
    }
  }


  @datatype trait Fun

  @datatype class IFun(val tipe: AST.Typed.Name, val id: String) extends Fun

  @datatype class OFun(val name: ISZ[String]) extends Fun


  object Value {

    @datatype class Unit(@hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.unit
      }

      @pure override def toRawST: ST = {
        return st"()"
      }
    }

    @datatype class B(val value: org.sireum.B, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.b
      }

      @pure override def toRawST: ST = {
        return if (value) State.stTrue else State.stFalse
      }

      override def toSTOpt(numMap: Util.NumMap, defs: HashMap[org.sireum.Z, ISZ[Claim.Let]]): Option[ST] = {
        return if (value) None() else Some(State.stFalse)
      }
    }

    @datatype class Z(val value: org.sireum.Z, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.z
      }

      @pure override def toRawST: ST = {
        return st"$value"
      }
    }

    @datatype class C(val value: org.sireum.C, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.c
      }

      @pure override def toRawST: ST = {
        return st"char${Json.Printer.printC(value)}"
      }
    }

    @datatype class F32(val value: org.sireum.F32, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f32
      }

      @pure override def toRawST: ST = {
        return st"${value}f"
      }
    }

    @datatype class F64(val value: org.sireum.F64, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f64
      }

      @pure override def toRawST: ST = {
        return st"${value}d"
      }
    }

    @datatype class R(val value: org.sireum.R, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.r
      }

      @pure override def toRawST: ST = {
        return st"$value"
      }
    }

    @datatype class String(val value: org.sireum.String, @hidden val pos: Position) extends Value {
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

    @datatype class Range(val value: org.sireum.Z, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S8(val value: org.sireum.S8, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S16(val value: org.sireum.S16, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S32(val value: org.sireum.S32, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S64(val value: org.sireum.S64, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U8(val value: org.sireum.U8, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U16(val value: org.sireum.U16, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U32(val value: org.sireum.U32, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U64(val value: org.sireum.U64, val tipe: AST.Typed.Name, @hidden val pos: Position) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class Enum(val tipe: AST.Typed.Name, val owner: ISZ[org.sireum.String], val id: org.sireum.String,
                         val ordinal: org.sireum.Z, @hidden val pos: Position) extends Value {
      @strictpure override def toRawST: ST = st"${(owner, ".")}.$id"
    }

    @datatype class Sym(val num: org.sireum.Z, val tipe: AST.Typed, @hidden val pos: Position) extends Value {

      @pure override def toRawST: ST = {
        return st"$symPrefix$num@[${pos.beginLine},${pos.beginColumn}]"
      }

      override def toST(numMap: Util.NumMap, defs: HashMap[org.sireum.Z, ISZ[Claim.Let]]): ST = {
        return toSTOpt(numMap, defs).getOrElse(stTrue)
      }

      override def toSTOpt(numMap: Util.NumMap, defs: HashMap[org.sireum.Z, ISZ[Claim.Let]]): Option[ST] = {
        defs.get(num) match {
          case Some(d) =>
            return if (d.size == 1) d(0).toST(numMap, defs)
            else Some(toRawST)
          case _ => return Some(toRawST)
        }
      }
    }

    @pure def sym(num: org.sireum.Z, tipe: AST.Typed, pos: Position): Sym = {
      return Sym(num, tipe, pos)
    }
  }

  @datatype trait Claim {

    @pure def toRawST: ST

    def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit

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

    @pure override def string: String = {
      return toRawST.render
    }
  }

  object Claim {

    @datatype trait Composite extends Claim {
      @pure def claims: ISZ[Claim]
    }

    @datatype class Label(val label: String, val pos: Position) extends Claim {
      @pure override def toRawST: ST = {
        pos.uriOpt match {
          case Some(uri) =>
            val sops = ops.StringOps(uri)
            val i = sops.lastIndexOf('/')
            val filename: String = if (i < 0) uri else sops.substring(i + 1, uri.size)
            return st"$filename@[${pos.beginLine},${pos.beginColumn}]: $label"
          case _ =>
            return st"[${pos.beginLine},${pos.beginColumn}]: $label"
        }
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        claimSTs.add(toRawST)
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ()
      }
    }

    @datatype class Old(val isLocal: B, isSpec: B, val owner: ISZ[String], val id: String, val value: Value,
                        val pos: Position) extends Claim {
      @pure override def toRawST: ST = {
        return value.toRawST
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(value.tipe)
      }
    }

    @datatype class Input(val isLocal: B, isSpec: B, val owner: ISZ[String], val id: String, val value: Value,
                          val pos: Position) extends Claim {
      @pure override def toRawST: ST = {
        return value.toRawST
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(value.tipe)
      }
    }

    @datatype class Prop(val isPos: B, val value: Value.Sym) extends Claim {
      @pure override def toRawST: ST = {
        return if (isPos) value.toRawST else st"¬(${value.toRawST})"
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        value.toSTOpt(numMap, defs) match {
          case Some(r) =>
            if (isPos) {
              claimSTs.add(st"$r")
            } else {
              claimSTs.add(st"¬($r)")
            }
          case _ =>
            if (!isPos) {
              claimSTs.add(State.stFalse)
            }
        }
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(value.tipe)
      }
    }

    @datatype class Eq(val v1: Value.Sym, val v2: Value) extends Claim {
      @pure override def toRawST: ST = {
        return st"${v1.toRawST} === ${v2.toRawST}"
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        claimSTs.add(st"${v1.toST(numMap, defs)} === ${v2.toST(numMap, defs)}")
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(v1.tipe, v2.tipe)
      }
    }

    @datatype class And(val claims: ISZ[Claim]) extends Composite {
      @pure def toRawST: ST = {
        val r: ST =
          if (claims.size == 1) claims(0).toRawST
          else
            st"""∧(
                |  ${(for (c <- claims) yield c.toRawST, ",\n")}
                |)"""
        return r
      }

      def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
        val claimSTs = Util.ClaimSTs(ISZ())
        for (c <- claims) {
          c.toSTs(claimSTs, numMap, defs)
        }
        if (claimSTs.value.size == 0) {
          return None()
        } else if (claimSTs.value.size == 1) {
          return Some(claimSTs.value(0))
        } else {
          return Some(
            st"""∧(
                |  ${(claimSTs.value, ",\n")}
                |)"""
          )
        }
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        toST(numMap, defs) match {
          case Some(r) => claimSTs.add(r)
          case _ =>
        }
      }
    }

    @datatype class Or(val claims: ISZ[Claim]) extends Composite {
      @pure def toRawST: ST = {
        val r: ST =
          if (claims.size == 1) claims(0).toRawST
          else
            st"""∨(
                |  ${(for (c <- claims) yield c.toRawST, ",\n")}
                |)"""
        return r
      }

      def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
        val claimSTs = Util.ClaimSTs(ISZ())
        for (c <- claims) {
          c.toSTs(claimSTs, numMap, defs)
        }
        if (claimSTs.value.size == 0) {
          if (claims.nonEmpty) {
            return None()
          } else {
            return Some(State.stFalse)
          }
        }
        else if (claimSTs.value.size == 1) {
          return Some(claimSTs.value(0))
        }
        else {
          return Some(
            st"""∨(
                |  ${(claimSTs.value, ",\n")}
                |)"""
          )
        }
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        toST(numMap, defs) match {
          case Some(r) => claimSTs.add(r)
          case _ =>
        }
      }
    }

    @datatype class Imply(val isCond: B, val claims: ISZ[Claim]) extends Composite {
      @pure def toRawST: ST = {
        val r: ST =
          if (claims.size == 2)
            st"""${claims(0).toRawST} → ${claims(1).toRawST}"""
          else
            st"""→(
                |  ${(for (c <- claims) yield c.toRawST, ",\n")}
                |)"""
        return r
      }

      @pure def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
        var claimSTs = Util.ClaimSTs(ISZ())
        claims(claims.size - 1).toSTs(claimSTs, numMap, defs)
        if (claimSTs.value.isEmpty) {
          return None()
        }
        val conclusion = claimSTs.value(0)
        claimSTs = Util.ClaimSTs(ISZ())
        for (i <- 0 until claims.size - 1) {
          claims(i).toSTs(claimSTs, numMap, defs)
        }
        if (claimSTs.value.size == 0) {
          return Some(conclusion)
        } else if (claimSTs.value.size == 1) {
          return Some(st"""${claimSTs.value(0)} → $conclusion""")
        } else {
          return Some(
            st"""→(
                |  ${(claimSTs.value, ",\n")},
                |  $conclusion
                |)"""
          )
        }
      }

      @pure def types: ISZ[AST.Typed] = {
        return for (c <- claims; t <- c.types) yield t
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        toST(numMap, defs) match {
          case Some(r) => claimSTs.add(r)
          case _ =>
        }

      }
    }

    @datatype class If(val cond: Value.Sym,
                       val tClaims: ISZ[Claim],
                       val fClaims: ISZ[Claim]) extends Composite {

      @strictpure override def claims: ISZ[Claim] = tClaims ++ fClaims

      @pure override def toRawST: ST = {
        val r =
          st"""${cond.toRawST} ?
              |    ${And(tClaims).toRawST}
              |  : ${And(fClaims).toRawST}"""
        return r
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        val condST = cond.toST(numMap, defs)
        val tSTOpt = And(tClaims).toST(numMap, defs)
        val fSTOpt = And(fClaims).toST(numMap, defs)
        (tSTOpt, fSTOpt) match {
          case (Some(tST), Some(fST)) =>
            claimSTs.add(
              st"""$condST ?
                  |    $tST
                  |  : $fST""")
          case (Some(tST), _) => claimSTs.add(st"""$condST → $tST""")
          case (_, Some(fST)) => claimSTs.add(st"""¬($condST) → $fST""")
          case (_, _) =>
        }
      }

      @pure def types: ISZ[AST.Typed] = {
        return cond.tipe +: ((for (tClaim <- tClaims; t <- tClaim.types) yield t) ++
          (for (fClaim <- fClaims; t <- fClaim.types) yield t))
      }
    }

    @datatype trait Let extends Claim {
      @pure def sym: Value.Sym

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(sym.tipe)
      }

      @pure def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST]

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {}
    }

    object Let {

      @datatype class AdtLit(val sym: Value.Sym, val args: ISZ[Value]) extends Let {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${sym.tipe.string}(${(for (arg <- args) yield arg.toST(numMap, defs), ", ")})")
        }
      }

      @datatype class SeqLit(val sym: Value.Sym, val args: ISZ[SeqLit.Arg]) extends Let {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg.value.toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${sym.tipe.string}(${(for (arg <- args) yield arg.value.toST(numMap, defs), ", ")})")
        }
      }

      object SeqLit {
        @datatype class Arg(val index: Value, val value: Value)
      }

      @datatype class CurrentName(val sym: Value.Sym, val ids: ISZ[String],
                                  val defPosOpt: Option[Position]) extends Let {
        @pure override def toRawST: ST = {
          return st"${(shorten(ids), ".")} == ${sym.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${(shorten(ids), ".")}")
        }

        override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
          if (defs.get(sym.num).get != ISZ[Claim.Let](this)) {
            claimSTs.add(st"${toST(numMap, defs)} == ${sym.toST(numMap, defs)}")
          }
        }
      }

      @datatype class SeqStore(val sym: Value.Sym, val seq: Value, val index: Value, val element: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${seq.toRawST}(${index.toRawST} ~> ${element.toRawST})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${seq.toST(numMap, defs)}(${index.toST(numMap, defs)} ~> ${element.toST(numMap, defs)})")
        }
      }

      @datatype class FieldStore(val sym: Value.Sym, val adt: Value, val id: String, val value: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${adt.toRawST}($id = ${value.toRawST})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${adt.toST(numMap, defs)}($id = ${value.toST(numMap, defs)})")
        }
      }

      @datatype class Random(val sym: Value.Sym, val hidden: B, val pos: Position) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${sym.tipe}.random@[${pos.beginLine},${pos.beginColumn}]#${sym.num}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(numMap.toST(st"${sym.tipe}.random@[${pos.beginLine},${pos.beginColumn}]", sym.num))
        }
      }

      @datatype class Name(val sym: Value.Sym, val ids: ISZ[String], val num: Z, val poss: ISZ[Position]) extends Let {
        @pure override def toRawST: ST = {
          return st"${(shorten(ids), ".")}@${possLines(poss)}#$num == ${sym.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(numMap.toST(st"${(shorten(ids), ".")}@${possLines(poss)}", num))
        }

        override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
          if (defs.get(sym.num).get != ISZ[Claim.Let](this)) {
            claimSTs.add(st"${toST(numMap, defs)} == ${sym.toST(numMap, defs)}")
          }
        }
      }

      @datatype class CurrentId(val declId: B, val sym: Value.Sym, val context: ISZ[String], val id: String,
                                val defPosOpt: Option[Position]) extends Let {
        @pure override def toRawST: ST = {
          return st"$id == ${sym.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"$id")
        }

        override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
          if (defs.get(sym.num).get != ISZ[Claim.Let](this)) {
            claimSTs.add(st"${toST(numMap, defs)} == ${sym.toST(numMap, defs)}")
          }
        }
     }

      @datatype class Id(val sym: Value.Sym, val inScope: B, val context: ISZ[String], val id: String, val num: Z,
                         val poss: ISZ[Position]) extends Let {

        @pure override def toRawST: ST = {
          return if (context.isEmpty) st"$id@${possLines(poss)}#$num == ${sym.toRawST}"
          else st"$id:${(shorten(context), ".")}@${possLines(poss)}#$num == ${sym.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(numMap.toST(
            if (context.isEmpty) st"$id@${possLines(poss)}" else st"$id:${(shorten(context), ".")}@${possLines(poss)}",
            num
          ))
        }

        override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
          if (defs.get(sym.num).get != ISZ[Claim.Let](this)) {
            claimSTs.add(st"${toST(numMap, defs)} == ${sym.toST(numMap, defs)}")
          }
        }
      }

      @datatype class Def(val sym: Value.Sym, val value: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${value.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${value.toST(numMap, defs)}")
        }

        override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
          if (defs.get(sym.num).get.size > 1) {
            claimSTs.add(st"${sym.toRawST} === ${value.toST(numMap, defs)}")
          }
        }
      }

      @datatype class TypeTest(val sym: Value.Sym, val isEq: B, val value: Value, val tipe: AST.Typed) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ typeOf(${value.toRawST}) $testRel $tipe"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"typeOf(${value.toST(numMap, defs)}) $testRel $tipe")
        }

        @strictpure def testRel: String = if (isEq) "=:=" else "<:<"
      }

      object Quant {
        @datatype class Var(val context: ISZ[String], val id: String, val tipe: AST.Typed) {
          @pure def toRawST: ST = {
            return st"$id: $tipe"
          }

          @pure def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
            return Some(toRawST)
          }

        }
      }

      @datatype class Quant(val sym: Value.Sym,
                            val isAll: B, val vars: ISZ[Quant.Var],
                            val claims: ISZ[Claim]) extends Let with Composite {
        @pure override def toRawST: ST = {
          val r =
            st"""${sym.toRawST} ≜ ${if (isAll) "∀" else "∃"} ${(for (x <- vars) yield x.toRawST, ", ")}
                |  ${if (isAll) Claim.Imply(F, claims).toRawST else Claim.And(claims).toRawST}"""
          return r
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(
            st"""${if (isAll) "∀" else "∃"} ${(for (x <- vars) yield x.toST(numMap, defs), ", ")}  ${if (isAll) Claim.Imply(F, claims).toST(numMap, defs).getOrElse(State.stTrue) else Claim.And(claims).toST(numMap, defs).getOrElse(State.stTrue)}"""
          )
        }

        @pure override def types: ISZ[Typed] = {
          return sym.tipe +: (for (claim <- claims; t <- claim.types) yield t)
        }
      }

      @datatype class Ite(val sym: Value.Sym, val cond: Value, val left: Value, val right: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${cond.toRawST} ? ${left.toRawST} : ${right.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          left match {
            case left: State.Value.B if left.value =>
              return Some(st"(${cond.toST(numMap, defs)}) || (${right.toST(numMap, defs)})")
            case _ =>
          }
          right match {
            case right: State.Value.B =>
              if (right.value) {
                return Some(st"(${cond.toST(numMap, defs)}) -->: (${left.toST(numMap, defs)})")
              } else {
                return Some(st"(${cond.toST(numMap, defs)}) && (${left.toST(numMap, defs)})")
              }
            case _ =>
              return Some(
                st"""(if (${cond.toST(numMap, defs)})
                    |   ${left.toST(numMap, defs)}
                    | else ${right.toST(numMap, defs)})""")
          }
        }
      }

      @datatype class Binary(val sym: Value.Sym, val left: Value, val op: String, val right: Value, val tipe: AST.Typed) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${left.toRawST} $op ${right.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          val l = AST.Exp.BinaryOp.precendenceLevel(op)
          @pure def checkLevel(ds: ISZ[Claim.Let]): B = {
            for (d <- ds) {
              d match {
                case d: Binary if AST.Exp.BinaryOp.precendenceLevel(d.op) >= l => return T
                case _ =>
              }
            }
            return F
          }
          var leftParen = F
          left match {
            case left: Value.Sym => defs.get(left.num) match {
              case Some(defs) if checkLevel(defs) => leftParen = T
              case _ =>
            }
            case _ =>
          }
          var rightParen = F
          right match {
            case right: Value.Sym => defs.get(right.num) match {
              case Some(defs) if checkLevel(defs) => rightParen = T
              case _ =>
            }
            case _ =>
          }
          val leftST: ST = if (leftParen) st"(${left.toST(numMap, defs)})" else st"${left.toST(numMap, defs)}"
          val rightST: ST = if (rightParen) st"(${right.toST(numMap, defs)})" else st"${right.toST(numMap, defs)}"
          return Some(st"$leftST $op $rightST")
        }
      }

      @datatype class Unary(val sym: Value.Sym, val op: String, val value: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ $op${value.toRawST}"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"$op${value.toST(numMap, defs)}")
        }
      }

      @datatype class SeqLookup(val sym: Value.Sym, val seq: Value, val index: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${seq.toRawST}(${index.toRawST})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${seq.toST(numMap, defs)}(${index.toST(numMap, defs)})")
        }
      }

      @datatype class SeqInBound(val sym: Value.Sym, val seq: Value, val index: Value) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ inBound(${seq.toRawST}, ${index.toRawST})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"inBound(${seq.toST(numMap, defs)}, ${index.toST(numMap, defs)})")
        }
      }

      @datatype class FieldLookup(val sym: Value.Sym, val adt: Value, val id: String) extends Let {
        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${adt.toRawST}.$id"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${adt.toST(numMap, defs)}.$id")
        }
      }

      @datatype class ProofFunApply(val sym: Value.Sym, val pf: ProofFun, val args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (pf.receiverTypeOpt.isEmpty)
            if (pf.context.isEmpty) st"${sym.toRawST} ≜ ${pf.id}(${(for (arg <- args) yield arg.toRawST, ", ")})"
            else st"${sym.toRawST} ≜ ${(shorten(pf.context) :+ pf.id, ".")}(${(for (arg <- args) yield arg.toRawST, ", ")})"
          else st"${sym.toRawST} ≜ ${args(0).toRawST}.${pf.id}(${(for (i <- 1 until args.size) yield args(i).toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(
            if (pf.receiverTypeOpt.isEmpty)
              st"${(shorten(pf.context) :+ pf.id, ".")}(${(for (arg <- args) yield arg.toST(numMap, defs), ", ")})"
            else st"${args(0).toST(numMap, defs)}.${pf.id}(${(for (i <- 1 until args.size) yield args(i).toST(numMap, defs), ", ")})"
          )
        }

      }

      @datatype class Apply(val sym: Value.Sym, val isLocal: B, val context: ISZ[String], val id: String, val args: ISZ[Value], val tipe: AST.Typed.Fun) extends Let {
        @strictpure def name: ISZ[String] = context :+ id

        @pure override def toRawST: ST = {
          return st"${sym.toRawST} ≜ ${(shorten(name), ".")}(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(st"${(shorten(name), ".")}(${(for (arg <- args) yield arg.toST(numMap, defs), ", ")})")
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ(OFun(name))
        }
      }

      @datatype class TupleLit(val sym: Value.Sym, val args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (args.size == 1) st"${sym.toRawST} ≜ ${args(0).toRawST}"
          else st"${sym.toRawST} ≜ (${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          return Some(
            if (args.size == 1) st"${args(0).toST(numMap, defs)}"
            else st"(${(for (arg <- args) yield arg.toST(numMap, defs), ", ")})"
          )
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ()
        }
      }

      @datatype class And(val sym: Value.Sym, val args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (args.size == 1) st"${sym.toRawST} ≜ ${args(0).toRawST}"
          else if (args.size == 2) st"${sym.toRawST} ≜ ${args(0).toRawST} ∧ ${args(1).toRawST}"
          else st"${sym.toRawST} ≜ ∧(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          var claims = ISZ[ST]()
          for (arg <- args) {
            arg.toSTOpt(numMap, defs) match {
              case Some(claim) => claims = claims :+ claim
              case _ =>
            }
          }
          return if (claims.size == 0 && args.nonEmpty) None()
          else if (claims.size == 1) Some(claims(0))
          else if (claims.size == 2) Some(st"(${claims(0)}) ∧ (${claims(1)})")
          else Some(st"∧(${(claims, ", ")})")
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ()
        }
      }

      @datatype class Or(val sym: Value.Sym, val args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (args.size == 1) st"${sym.toRawST} ≜ ${args(0).toRawST}"
          else if (args.size == 2) st"${sym.toRawST} ≜ ${args(0).toRawST} ∨ ${args(1).toRawST}"
          else st"${sym.toRawST} ≜ ∨(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          var claims = ISZ[ST]()
          for (arg <- args) {
            arg.toSTOpt(numMap, defs) match {
              case Some(claim) => claims = claims :+ claim
              case _ =>
            }
          }
          return if (claims.size == 0 && args.nonEmpty) None()
          else if (claims.size == 1) Some(claims(0))
          else if (claims.size == 2) Some(st"(${claims(0)}) ∨ (${claims(1)})")
          else Some(st"∨(${(claims, ", ")})")
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ()
        }
      }

      @datatype class Imply(val sym: Value.Sym, val args: ISZ[Value]) extends Let {
        @pure override def toRawST: ST = {
          return if (args.size == 2) st"${sym.toRawST} ≜ ${args(0).toRawST} → ${args(1).toRawST}"
          else st"${sym.toRawST} ≜ →(${(for (arg <- args) yield arg.toRawST, ", ")})"
        }

        override def toST(numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Option[ST] = {
          args(args.size - 1).toSTOpt(numMap, defs) match {
            case Some(conclusion) =>
              var premises = ISZ[ST]()
              for (i <- 0 until args.size - 1) {
                args(i).toSTOpt(numMap, defs) match {
                  case Some(premise) => premises = premises :+ premise
                  case _ =>
                }
              }
              return if (premises.size == 0) Some(conclusion)
              else if (premises.size == 1) Some(st"(${premises(0)}) → $conclusion")
              else Some(st"→(${(premises, ", ")}, $conclusion)")
            case _ => return None()
          }
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ()
        }
      }
    }

    @pure def claimsSTs(claims: ISZ[Claim], defs: Util.ClaimDefs): ISZ[ST] = {
      for (c <- claims) {
        Util.ClaimDefs.collectDefs(c, defs)
      }
      val claimSTs = Util.ClaimSTs(ISZ())
      val m = defs.value
      val numMap = Util.NumMap(HashMap.empty)
      for (c <- claims) {
        c.toSTs(claimSTs, numMap, m)
      }
      return claimSTs.value
    }

    @pure def claimsRawSTs(claims: ISZ[Claim]): ISZ[ST] = {
      return for (c <- claims) yield c.toRawST
    }

    @pure def possLines(poss: ISZ[Position]): ST = {
      return if (poss.size != 1) st"{${(for (pos <- poss) yield pos.beginLine, ", ")}}"
      else st"${poss(0).beginLine}"
    }

    @datatype class Custom(data: Data) extends Claim {
      @pure override def toRawST: ST = {
        return data.toRawST
      }

      override def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit = {
        data.toSTs(claimSTs, numMap, defs)
      }

      @strictpure override def types: ISZ[AST.Typed] = data.types
    }

    @sig trait Data {
      @pure def toRawST: ST
      def toSTs(claimSTs: Util.ClaimSTs, numMap: Util.NumMap, defs: HashMap[Z, ISZ[Claim.Let]]): Unit
      @strictpure def types: ISZ[AST.Typed]
    }

  }

  @datatype class ProofFun(val receiverTypeOpt: Option[AST.Typed],
                           val context: ISZ[String],
                           val id: String,
                           val isByName: B,
                           val paramIds: ISZ[String],
                           val paramTypes: ISZ[AST.Typed],
                           val returnType: AST.Typed)

  val symPrefix: String = "α"
  val errorValue: Value.Sym = Value.sym(0, AST.Typed.nothing, Position.none)
  val stTrue: ST = st"T"
  val stFalse: ST = st"F"

  @memoize def create: State = {
    return State(State.Status.Normal, ISZ(), 1)
  }

  @pure def shorten(ids: ISZ[String]): ISZ[String] = {
    return if (ids.size > 2 && ids(0) == "org" && ids(1) == "sireum") ops.ISZOps(ids).slice(2, ids.size) else ids
  }

}
