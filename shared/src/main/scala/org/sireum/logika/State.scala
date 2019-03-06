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
import org.sireum.lang.symbol._
import org.sireum.message._

@datatype class State(globalVars: HashSMap[ISZ[String], State.Value],
                      heap: State.Heap,
                      store: State.Store,
                      stack: Stack[State.Store],
                      claims: HashSSet[State.Claim],
                      nextSym: State.SymId,
                      errorOpt: Option[Message]) {
  @pure def nextAddress: State.Address = {
    return if (heap.isEmpty) 1 else heap.keys(heap.keys.size - 1) + 1
  }

  @pure def toST: ST = {
    @pure def store2ST(s: State.Store): ST = {
      return st"""{
                 |  ${(for (p <- s.entries) yield st"${p._1} = ${p._2.toST}", ",\n")}
                 |}"""
    }
    @pure def heap2ST(h: State.Heap): ST = {
      return st"""{
                 |  ${(for (p <- h.entries) yield st"@${p._1} = ${p._2.toST}", ",\n")}
                 |}"""
    }
    val stackElements = ops.ISZOps(stack.elements).reverse
    return st"""State {
               |  globals = {
               |    ${(for (p <- globalVars.entries) yield st"${(p._1, ".")} = ${p._2.toST}", ",\n")}
               |  },
               |  heap = ${heap2ST(heap)},
               |  store = ${store2ST(store)},
               |  stack = [
               |    ${(for (s <- stackElements) yield store2ST(s), ",\n")}
               |  ],
               |  claims = {
               |    ${(claims.elements.map(State.c2st), ",\n")}
               |  },
               |  nextSym = $nextSym,
               |  error = { $errorOpt }
               |}"""
  }

  @pure def hasError: B = {
    return errorOpt.nonEmpty
  }
}

object State {
  type Address = Z
  type Heap = HashSMap[State.Address, HeapValue]
  type Store = HashSMap[String, Value]
  type SymId = Z

  val symPrefix: String = "α"
  val v2st: Value => ST @pure = x => x.toST
  val c2st: Claim => ST @pure = x => x.toST
  val errorValue: Value.Sym = Value.Sym(0, AST.Typed.nothing)

  @datatype class HeapValue(count: Z, value: Value) {
    @pure def toST: ST = {
      return st"<$count> ${value.toST}"
    }
  }

  @datatype trait Value {
    @pure def typed(state: State): AST.Typed

    @pure def resolve(state: State): Value = {
      this match {
        case v: Value.Ref => return state.heap.get(v.address).get.value
        case v => return v
      }
    }

    @pure def toST: ST
  }

  object Value {

    @datatype class B(value: org.sireum.B) extends Value {
      @pure override def typed(state: State): AST.Typed.Name = {
        return AST.Typed.b
      }

      @pure override def toST: ST = {
        return if (value) st"T" else st"F"
      }
    }

    @datatype class Z(value: org.sireum.Z) extends Value {
      @pure override def typed(state: State): AST.Typed.Name = {
        return AST.Typed.z
      }

      @pure override def toST: ST = {
        return st"$value"
      }
    }

    @datatype class C(value: org.sireum.C) extends Value {
      @pure override def typed(state: State): AST.Typed.Name = {
        return AST.Typed.c
      }

      @pure override def toST: ST = {
        return st"""char${Json.Printer.printC(value)}"""
      }
    }

    @datatype class F32(value: org.sireum.F32) extends Value {
      @pure override def typed(state: State): AST.Typed.Name = {
        return AST.Typed.f32
      }

      @pure override def toST: ST = {
        return st"${value}f"
      }
    }

    @datatype class F64(value: org.sireum.F64) extends Value {
      @pure override def typed(state: State): AST.Typed.Name = {
        return AST.Typed.f64
      }

      @pure override def toST: ST = {
        return st"${value}d"
      }
    }

    @datatype class R(value: org.sireum.R) extends Value {
      @pure override def typed(state: State): AST.Typed.Name = {
        return AST.Typed.r
      }

      @pure override def toST: ST = {
        return st"$value"
      }
    }

    @datatype class String(value: org.sireum.String) extends Value {
      @pure override def typed(state: State): AST.Typed.Name = {
        return AST.Typed.string
      }

      @pure override def toST: ST = {
        return Json.Printer.printString(value)
      }
    }

    @datatype trait SubZ extends Value {
      def info: TypeInfo.SubZ

      @pure override def typed(state: State): AST.Typed.Name = {
        return info.typedOpt.get.asInstanceOf[AST.Typed.Name]
      }

      @pure override def toST: ST = {
        val id = info.name(info.name.size - 1)
        return st"""${ops.StringOps(id).firstToLower}"$valueString""""
      }

      @pure def valueString: org.sireum.String
    }

    @datatype class Range(value: org.sireum.Z, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S8(value: org.sireum.S8, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S16(value: org.sireum.S16, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S32(value: org.sireum.S32, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class S64(value: org.sireum.S64, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U8(value: org.sireum.U8, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U16(value: org.sireum.U16, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U32(value: org.sireum.U32, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class U64(value: org.sireum.U64, val info: TypeInfo.SubZ) extends SubZ {
      @pure override def valueString: org.sireum.String = {
        return value.string
      }
    }

    @datatype class Ref(address: State.Address) extends Value {
      @pure override def typed(state: State): AST.Typed = {
        return resolve(state).typed(state)
      }

      @pure override def toST: ST = {
        return st"@$address"
      }
    }

    @datatype class Adt(tipe: AST.Typed.Name, store: State.Store) extends Value {
      @pure def typed(state: State): AST.Typed.Name = {
        return tipe
      }

      @pure override def toST: ST = {
        return st"""${shorten(tipe)}(
                   |  ${(for (p <- store.entries) yield st"${p._1} = ${p._2.toST}", ",\n")}
                   |)"""
      }
    }

    @datatype class Seq(tipe: AST.Typed.Name, elements: ISZ[Value]) extends Value {
      @pure def typed(state: State): AST.Typed.Name = {
        return tipe
      }

      @pure override def toST: ST = {
        val indexType = shorten(tipe.args(0))
        val elementType = shorten(tipe.args(1))
        return st"""${tipe.ids(tipe.ids.size - 1)}[$indexType, $elementType](
                   |  ${(elements.map(v2st), ",\n")}
                   |)"""
      }
    }

    @datatype class Sym(id: State.SymId, @hidden tipe: AST.Typed) extends Value {
      @pure def typed(state: State): AST.Typed = {
        return tipe
      }

      @pure override def toST: ST = {
        return st"$symPrefix$id"
      }
    }
  }

  @datatype trait Claim {
    def toST: ST
  }

  object Claim {

    @datatype class And(claims: ISZ[Claim]) extends Claim {
      @pure override def toST: ST = {
        return st"""∧(
                   |  ${(claims.map(c2st), ",\n")}
                   |)"""
      }
    }

    @datatype class Or(claims: ISZ[Claim]) extends Claim {
      @pure override def toST: ST = {
        return st"""∨(
                   |  ${(claims.map(c2st), ",\n")}
                   |)"""
      }
    }

    @datatype class Imply(claims: ISZ[Claim]) extends Claim {
      @pure override def toST: ST = {
        return st"""→(
                   |  ${(claims.map(c2st), ",\n")}
                   |)"""
      }
    }

    @datatype class Quant(isAll: B, ids: ISZ[Def.Id], tipe: AST.Typed, defs: ISZ[Def], sym: Value.Sym) extends Claim {
      @pure override def toST: ST = {
        return st"""${if (isAll) "∀" else "∃"} ${(for (id <- ids) yield c2st(id), ", ")} : ${tipe.string} ${sym.toST}, where ∧(
                   |  ${(for (d <-defs) yield c2st(d), ",\n")}
                   |)"""
      }
    }

    @datatype trait Def extends Claim {
      def sym: Value.Sym
    }

    object Def {

      @datatype class Val(val sym: Value.Sym, value: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${value.toST}"
        }
      }

      @datatype class Id(val sym: Value.Sym, id: String) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ $id"
        }
      }

      @datatype class Binary(val sym: Value.Sym, left: Value, op: String, right: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${left.toST} $op ${right.toST}"
        }
      }

      @datatype class Unary(val sym: Value.Sym, op: String, value: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ $op ${value.toST}"
        }
      }

      @datatype class SeqStore(val sym: Value.Sym, seq: Value, index: Value, element: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${seq.toST}(${index.toST} ~> ${element.toST})"
        }
      }

      @datatype class SeqLookup(val sym: Value.Sym, seq: Value, index: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${seq.toST}(${index.toST})"
        }
      }

      @datatype class FieldStore(val sym: Value.Sym, adt: Value, id: String, value: Value) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${adt.toST}($id = ${value.toST})"
        }
      }

      @datatype class FieldLookup(val sym: Value.Sym, adt: Value, id: String) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${adt.toST}.$id"
        }
      }

      @datatype class Apply(val sym: Value.Sym, name: ISZ[String], args: ISZ[Value]) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${(name, ".")}(${(args.map(v2st), ", ")})"
        }
      }

      @datatype class IApply(val sym: Value.Sym, o: Value, id: String, args: ISZ[Value]) extends Def {
        @pure override def toST: ST = {
          return st"${sym.toST} ≜ ${o.toST}.$id(${(args.map(v2st), ", ")})"
        }
      }
    }
  }

  @pure def shorten(t: AST.Typed): ST = {
    t match {
      case t: AST.Typed.Name if t.ids.size == 3 && t.ids(0) == "org" && t.ids(1) == "sireum" =>
        return if (t.args.isEmpty) st"${t.ids(2)}" else st"${t.ids(2)}[${(t.args.map(shorten _), ", ")}]"
      case _ => return st"${t.string}"
    }
  }
}
