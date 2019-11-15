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
          |    ${(for (c <- claims) yield c.toST, ",\n")}
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

    @pure def toST: ST

    @pure def pos: Position
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
    }

    @datatype class Z(value: org.sireum.Z, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.z
      }

      @pure override def toST: ST = {
        return st"$value"
      }
    }

    @datatype class C(value: org.sireum.C, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.c
      }

      @pure override def toST: ST = {
        return st"char${Json.Printer.printC(value)}"
      }
    }

    @datatype class F32(value: org.sireum.F32, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f32
      }

      @pure override def toST: ST = {
        return st"${value}f"
      }
    }

    @datatype class F64(value: org.sireum.F64, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.f64
      }

      @pure override def toST: ST = {
        return st"${value}d"
      }
    }

    @datatype class R(value: org.sireum.R, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.r
      }

      @pure override def toST: ST = {
        return st"$value"
      }
    }

    @datatype class String(value: org.sireum.String, @hidden val pos: Position) extends Value {
      @pure override def tipe: AST.Typed.Name = {
        return AST.Typed.string
      }

      @pure override def toST: ST = {
        return Json.Printer.printString(value)
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

    @datatype class Sym(num: org.sireum.Z, @hidden val tipe: AST.Typed, @hidden val pos: Position) extends Value {

      @pure override def toST: ST = {
        return st"$symPrefix$num@[${pos.beginLine}:${pos.beginColumn}]"
      }
    }

  }

  @datatype trait Claim {

    @pure def toST: ST

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

  }

  @datatype class And(claims: ISZ[Claim]) {
    @pure def toST: ST = {
      val r: ST =
        if (claims.size == 0) st"T"
        else if (claims.size == 1) claims(0).toST
        else
          st"""∧(
              |  ${(for (c <- claims) yield c.toST, ",\n")}
              |)"""
      return r
    }

    @pure def types: ISZ[AST.Typed] = {
      return for (c <- claims; t <- c.types) yield t
    }
  }

  @datatype class Or(claims: ISZ[Claim]) {
    @pure def toST: ST = {
      val r: ST =
        if (claims.size == 0) st"F"
        else if (claims.size == 1) claims(0).toST
        else
          st"""∨(
              |  ${(for (c <- claims) yield c.toST, ",\n")})"""
      return r
    }

    @pure def types: ISZ[AST.Typed] = {
      return for (c <- claims; t <- c.types) yield t
    }
  }

  @datatype class Imply(claims: ISZ[Claim]) {
    @pure def toST: ST = {
      val r: ST =
        if (claims.size == 1) claims(0).toST
        else
          st"""→(
              |  ${(for (c <- claims) yield c.toST, ",\n")})"""
      return r
    }

    @pure def types: ISZ[AST.Typed] = {
      return for (c <- claims; t <- c.types) yield t
    }
  }

  object Claim {

    @datatype class Prop(isPos: B, value: Value.Sym) extends Claim {
      @pure override def toST: ST = {
        return if (isPos) value.toST else st"¬(${value.toST})"
      }

      @pure def types: ISZ[AST.Typed] = {
        return ISZ(value.tipe)
      }
    }

    @datatype class If(cond: Value.Sym,
                       tClaims: ISZ[Claim],
                       fClaims: ISZ[Claim]) extends Claim {

      @pure override def toST: ST = {
        val r =
          st"""${cond.toST} ?
              |  ${And(tClaims).toST}
              |  ${And(fClaims).toST}"""
        return r
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
    }

    object Def {

      @datatype class SeqLit(val sym: Value.Sym, args: ISZ[(Value, Value)], @hidden seqLitId: ST, @hidden sizeId: ST, @hidden atId: ST) extends Def {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg._2.toST, ", ")})"
        }
      }

      @datatype class SeqStore(val sym: Value.Sym, seq: Value, index: Value, element: Value, @hidden upId: ST) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @${seq.toST}(${index.toST} ~> ${element.toST})"
        }
      }

      @datatype class AdtLit(val sym: Value.Sym, args: ISZ[Value], @hidden newId: ST) extends Def {
        @pure def tipe: AST.Typed.Name = {
          return sym.tipe.asInstanceOf[AST.Typed.Name]
        }

        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${sym.tipe.string}(${(for (arg <- args) yield arg.toST, ", ")})"
        }
      }

    }

    @datatype trait Let extends Def

    object Let {

      @datatype class CurrentName(val sym: Value.Sym, ids: ISZ[String],
                                  @hidden defPosOpt: Option[Position]) extends Let {
        @pure override def toST: ST = {
          return st"${(ids, ".")} == ${sym.toST}"
        }
      }

      @datatype class Name(val sym: Value.Sym, ids: ISZ[String], num: Z, poss: ISZ[Position]) extends Let {
        @pure override def toST: ST = {
          return st"${(ids, ".")}@${possLines(poss)}#$num == ${sym.toST}"
        }
      }

      @datatype class CurrentId(val sym: Value.Sym, context: ISZ[String], id: String,
                                @hidden defPosOpt: Option[Position]) extends Let {
        @pure override def toST: ST = {
          return st"$id == ${sym.toST}"
        }
     }

      @datatype class Id(val sym: Value.Sym, context: ISZ[String], id: String, num: Z, poss: ISZ[Position]) extends Let {

        @pure override def toST: ST = {
          return if (context.isEmpty) st"$id@${possLines(poss)}#$num == ${sym.toST}"
          else st"$id:${(context, ".")}@${possLines(poss)}#$num == ${sym.toST}"
        }
      }

      @datatype class Eq(val sym: Value.Sym, value: Value) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${value.toST}"
        }
      }

      object Quant {
        @datatype class Var(id: String, tipe: AST.Typed) {
          @pure def toST: ST = {
            return st"$id: ${tipe.string}"
          }
        }
      }

      @datatype class Quant(val sym: Value.Sym, isAll: B, vars: ISZ[Quant.Var], claims: ISZ[Claim]) extends Let {
        @pure override def toST: ST = {
          val r =
            st"""${sym.toST} ≜ ${if (isAll) "∀" else "∃"} ${(for (x <- vars) yield x.toST, ", ")}
                |  ${if (isAll) Imply(claims).toST else And(claims).toST}"""
          return r
        }

        @pure override def types: ISZ[Typed] = {
          return sym.tipe +: (for (claim <- claims; t <- claim.types) yield t)
        }
      }

      @datatype class Binary(val sym: Value.Sym, left: Value, op: String, right: Value, tipe: AST.Typed.Name) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${left.toST} $op ${right.toST}"
        }
      }

      @datatype class Unary(val sym: Value.Sym, op: AST.Exp.UnaryOp.Type, value: Value) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ $op ${value.toST}"
        }
      }

      @datatype class SeqLookup(val sym: Value.Sym, seq: Value, index: Value, @hidden atId: ST) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @${seq.toST}(${index.toST})"
        }
      }

      @datatype class FieldStore(val sym: Value.Sym, adt: Value, id: String, value: Value) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @${adt.toST}($id = ${value.toST})"
        }
      }

      @datatype class FieldLookup(val sym: Value.Sym, adt: Value, id: String) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ @${adt.toST}.$id"
        }
      }

      @datatype class Apply(val sym: Value.Sym, name: ISZ[String], args: ISZ[Value]) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${(name, ".")}(${(for (arg <- args) yield arg.toST, ", ")})"
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ(OFun(name))
        }
      }

      @datatype class IApply(val sym: Value.Sym, o: Value, oTipe: AST.Typed.Name, id: String, args: ISZ[Value]) extends Let {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${o.toST}.$id(${(for (arg <- args) yield arg.toST, ", ")})"
        }

        @pure override def funs: ISZ[Fun] = {
          return ISZ(IFun(oTipe, id))
        }
      }

    }

    def possLines(poss: ISZ[Position]): ST = {
      return if (poss.size > 1) st"{${(for (pos <- poss) yield pos.beginLine, ", ")}}"
      else st"${poss(0).beginLine}"
    }

  }

}
