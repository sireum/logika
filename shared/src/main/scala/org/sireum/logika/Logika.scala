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
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}
import org.sireum.message.{Position, Reporter}

object Logika {
  val kind: String = "Logika"
}

@record class Logika(smt2: Smt2, typeHierarchy: TypeHierarchy, timeoutInSeconds: Z) {

  @memoize def basicTypes: HashSet[AST.Typed] = {
    return HashSet.empty[AST.Typed] ++ ISZ[AST.Typed](
      AST.Typed.b, AST.Typed.c, AST.Typed.f32, AST.Typed.f64, AST.Typed.r, AST.Typed.string, AST.Typed.z
    )
  }

  @memoize def zero(tipe: AST.Typed.Name, pos: Position): State.Value = {
    if (tipe == AST.Typed.z) {
      return State.Value.Z(0, pos)
    }
    halt("TODO") // TODO
  }

  def evalExp(state: State, e: AST.Exp, reporter: Reporter): (State, State.Value) = {
    if (!state.status) {
      return (state, State.errorValue)
    }

    def evalIdent(exp: AST.Exp.Ident): (State, State.Value) = {
      val s0 = state
      val pos = exp.posOpt.get

      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.LocalVar =>
          val (s1, sym) = s0.freshSym(exp.attr.typedOpt.get, pos)
          return (s1.addClaim(State.Claim.Def.CurrentId(sym, res.context, res.id)), sym)
        case AST.ResolvedInfo.Var(T, F, AST.Typed.sireumName, id) if id == "T" || id == "F" =>
          return (state, if (id == "T") State.Value.B(T, pos) else State.Value.B(F, pos))
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalBinaryExp(exp: AST.Exp.Binary): (State, State.Value) = {
      @pure def isCond(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
          case _ => return F
        }
        return T
      }

      @pure def isSeq(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryAppend =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryAppendAll =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryPrepend =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryRemoveAll =>
          case _ => return F
        }
        return T
      }

      @pure def reqNonZeroCheck(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryDiv =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryRem =>
          case _ => return F
        }
        return T
      }

      @pure def isBasic(t: AST.Typed): B = {
        if (basicTypes.contains(t)) {
          return T
        }
        t match {
          case t: AST.Typed.Name =>
            typeHierarchy.typeMap.get(t.ids) match {
              case Some(_: TypeInfo.SubZ) => return T
              case _ => return F
            }
          case _ => return F
        }
        return T
      }

      def checkNonZero(s0: State, value: State.Value, pos: Position): State = {
        val (s1, sym) = s0.freshSym(AST.Typed.b, pos)
        val tipe = value.typed.asInstanceOf[AST.Typed.Name]
        val claim = State.Claim.Def.Binary(sym, value, AST.Exp.BinaryOp.Ne, zero(tipe, pos), tipe)
        val query = smt2.valid(s0.claims :+ claim, State.Claim.Prop(sym)).render
        val unsat = smt2.checkUnsat(query, timeoutInSeconds)
        if (unsat) {
          return s1.addClaim(claim)
        } else {
          reporter.error(Some(pos), Logika.kind, s"Could not deduce non-zero second operand for ${exp.op}")
          return s1(status = F)
        }
      }

      val s0 = state

      exp.attr.resOpt.get match {
        case AST.ResolvedInfo.BuiltIn(kind) =>
          val (s1, v1) = evalExp(s0, exp.left, reporter)
          val tipe = v1.typed.asInstanceOf[AST.Typed.Name]
          if (isCond(kind)) {
            halt(s"TODO: $e") // TODO
          } else if (isSeq(kind)) {
            halt(s"TODO: $e") // TODO
          } else if (isBasic(tipe)) {
            val (s2, v2) = evalExp(s1, exp.right, reporter)
            val s3: State = if (reqNonZeroCheck(kind)) {
              checkNonZero(s2, v2, exp.right.posOpt.get)
            } else {
              s2
            }
            if (!s3.status) {
              return (s3, State.errorValue)
            }
            val rTipe = e.typedOpt.get
            val (s4, rExp) = s3.freshSym(rTipe, e.posOpt.get)
            val s5 = s4.addClaim(State.Claim.Def.Binary(rExp, v1, exp.op, v2, tipe))
            return (s5, rExp)
          } else {
            halt(s"TODO: $e") // TODO
          }
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    val s0 = state

    e match {
      case e: AST.Exp.LitB => return (s0, State.Value.B(e.value, e.posOpt.get))
      case e: AST.Exp.LitC => return (s0, State.Value.C(e.value, e.posOpt.get))
      case e: AST.Exp.LitF32 => return (s0, State.Value.F32(e.value, e.posOpt.get))
      case e: AST.Exp.LitF64 => return (s0, State.Value.F64(e.value, e.posOpt.get))
      case e: AST.Exp.LitR => return (s0, State.Value.R(e.value, e.posOpt.get))
      case e: AST.Exp.LitString => return (s0, State.Value.String(e.value, e.posOpt.get))
      case e: AST.Exp.LitZ => return (s0, State.Value.Z(e.value, e.posOpt.get))
      case e: AST.Exp.Binary => return evalBinaryExp(e)
      case e: AST.Exp.Ident => return evalIdent(e)
      case _ => halt(s"TODO: $e") // TODO
    }
  }

  def value2Sym(s0: State, v: State.Value, pos: Position): (State, State.Value.Sym) = {
    v match {
      case v: State.Value.Sym => return (s0, v)
      case _ =>
        val (s2, symV) = s0.freshSym(v.typed, pos)
        return (s2.addClaim(State.Claim.Def.Eq(symV, v)), symV)
    }
  }

  def evalStmt(state: State, stmt: AST.Stmt, reporter: Reporter): State = {
    if (!state.status) {
      return state
    }

    def evalAssume(s0: State, cond: AST.Exp): State = {
      val (s1, v) = evalExp(s0, cond, reporter)
      if (!s1.status) {
        return s1
      }
      val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
      val s3 = s2(claims = s2.claims :+ State.Claim.Prop(sym))
      val sat = smt2.checkSat(smt2.sat(s3.claims).render, timeoutInSeconds)
      return if (sat) s3 else s3(status = F)
    }

    def evalAssert(s0: State, cond: AST.Exp): State = {
      val (s1, v) = evalExp(s0, cond, reporter)
      if (!s1.status) {
        return s1
      }
      val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
      val conclusion = State.Claim.Prop(sym)
      val unsat = smt2.checkUnsat(smt2.valid(s2.claims, conclusion).render, timeoutInSeconds)
      if (unsat) {
        return s2(claims = s2.claims :+ conclusion)
      } else {
        reporter.error(cond.posOpt, Logika.kind, s"Assertion violated")
        return s2(status = F)
      }
    }

    def evalAssignExp(s0: State, ae: AST.AssignExp): (State, State.Value) = {
      ae match {
        case AST.Stmt.Expr(exp) => return evalExp(s0, exp, reporter)
        case _ => halt(s"TODO: $ae") // TODO
      }
    }

    def evalAssignLocal(decl: B, s0: State, context: ISZ[String], id: String, rhs: AST.AssignExp): State = {
      @pure def firstPos: Position = {
        for (claim <- s0.claims) {
          claim match {
            case claim: State.Claim.Def.CurrentId if claim.context == context && id == claim.id =>
              return claim.sym.pos
            case _ =>
          }
        }
        halt("Infeasible")
      }
      @pure def rewriteClaim(claim: State.Claim, pos: Position): State.Claim = {
        claim match {
          case claim: State.Claim.Def.CurrentId if claim.context == context && id == claim.id =>
            return State.Claim.Def.Id(claim.sym, context, id, s0.stack.size + 1, pos)
          case _ => return claim
        }
      }
      val (s1, init) = evalAssignExp(s0, rhs)
      val (s2, sym) = value2Sym(s1, init, rhs.asStmt.posOpt.get)
      val newClaims: ISZ[State.Claim] =
        if (decl) {
          s2.claims
        } else {
          val pos = firstPos
          for (c <- s2.claims) yield rewriteClaim(c, pos)
        }
      return s2(claims = newClaims :+ State.Claim.Def.CurrentId(sym, context, id))
    }

    stmt match {
      case AST.Stmt.Expr(e: AST.Exp.Invoke) =>
        e.attr.resOpt.get match {
          case AST.ResolvedInfo.BuiltIn(kind) =>
            kind match {
              case AST.ResolvedInfo.BuiltIn.Kind.Assert => return evalAssert(state, e.args(0))
              case AST.ResolvedInfo.BuiltIn.Kind.AssertMsg => return evalAssert(state, e.args(0))
              case AST.ResolvedInfo.BuiltIn.Kind.Assume => return evalAssume(state, e.args(0))
              case AST.ResolvedInfo.BuiltIn.Kind.AssumeMsg => return evalAssume(state, e.args(0))
              case _ =>
                halt(s"TODO: $stmt") // TODO
            }
          case _ =>
            halt(s"TODO: $stmt") // TODO
        }
      case stmt: AST.Stmt.Var if stmt.initOpt.nonEmpty =>
        stmt.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar => return evalAssignLocal(T, state, res.context, res.id, stmt.initOpt.get)
          case _ => halt(s"TODO: $stmt") // TODO
        }
      case AST.Stmt.Assign(lhs: AST.Exp.Ident, rhs) =>
        lhs.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar => return evalAssignLocal(F, state, res.context, res.id, rhs)
          case _ => halt(s"TODO: $stmt") // TODO
        }
      case _: AST.Stmt.Import => return state
      case _ =>
        halt(s"TODO: $stmt") // TODO
    }

  }

  def evalStmts(state: State, stmts: ISZ[AST.Stmt], reporter: Reporter): State = {
    var current = state

    for (stmt <- stmts) {
      if (!current.status) {
        return current
      }
      current = evalStmt(current, stmt, reporter)
    }

    return current
  }

}
