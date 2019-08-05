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
import org.sireum.lang.{ast => AST}
import org.sireum.message.{Position, Reporter}
import StateTransformer.{PrePost, PreResult}

object Logika {
  val kind: String = "Logika"

  @datatype class CurrentIdPossCollector(context: ISZ[String], id: String) extends PrePost[ISZ[Position]] {
    override def preStateClaimDefCurrentId(ctx: ISZ[Position], o: State.Claim.Def.CurrentId): PreResult[ISZ[Position], State.Claim.Def] = {
      return if (o.defPosOpt.nonEmpty && o.context == context && o.id == id) PreResult(ctx :+ o.defPosOpt.get, T, None())
      else PreResult(ctx, T, None())
    }
  }

  @datatype class CurrentIdRewriter(map: HashMap[(ISZ[String], String), (ISZ[Position], Z)]) extends PrePost[B] {
    override def preStateClaimDefCurrentId(ctx: B, o: State.Claim.Def.CurrentId): PreResult[B, State.Claim.Def] = {
      map.get((o.context, o.id)) match {
        case Some((poss, num)) => return PreResult(ctx, T, Some(State.Claim.Def.Id(o.sym, o.context, o.id, num, poss)))
        case _ => return PreResult(ctx, T, None())
      }
    }
  }

  @datatype class Config(defaultLoopBound: Z,
                         loopBounds: HashMap[ISZ[String], Z],
                         smt2TimeoutInSeconds: Z)

  def checkWorksheet(fileUriOpt: Option[String], input: String, config: Config,
                     smt2f: lang.tipe.TypeHierarchy => Smt2, reporter: Reporter): Unit = {
    lang.parser.Parser(input).parseTopUnit[AST.TopUnit.Program](allowSireum = F, isWorksheet = T, isDiet = F,
      fileUriOpt = fileUriOpt, reporter = reporter) match {
      case Some(program) if !reporter.hasIssue =>
        val (tc, rep) = lang.FrontEnd.libraryReporter
        reporter.reports(rep.messages)
        val (th, p) = lang.FrontEnd.checkWorksheet(Some(tc.typeHierarchy), program, reporter)
        if (!reporter.hasIssue) {
          lang.tipe.PostTipeAttrChecker.checkProgram(p, reporter)
        }
        if (!reporter.hasIssue) {
          val logika = Logika(config, smt2f(th))
          logika.evalStmts(State.create, p.body.stmts, reporter)
        }
      case _ =>
    }
  }
}

@record class Logika(config: Logika.Config,
                     smt2: Smt2) {

  @pure def isBasic(t: AST.Typed): B = {
    if (smt2.basicTypes.contains(t)) {
      return T
    }
    t match {
      case t: AST.Typed.Name =>
        smt2.typeHierarchy.typeMap.get(t.ids) match {
          case Some(_: TypeInfo.SubZ) => return T
          case _ => return F
        }
      case _ => return F
    }
    return T
  }

  @memoize def zero(tipe: AST.Typed.Name, pos: Position): State.Value = {
    if (tipe == AST.Typed.z) {
      return State.Value.Z(0, pos)
    }
    halt("TODO") // TODO
  }

  @memoize def adtSmtParamNames(t: AST.Typed.Name): ISZ[ST] = {
    val adt = smt2.typeHierarchy.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
    return for (p <- adt.ast.params) yield smt2.fieldId(t, p.id.value)
  }

  def evalExp(state: State, e: AST.Exp, reporter: Reporter): (State, State.Value) = {
    if (!state.status) {
      return (state, State.errorValue)
    }

    def evalIdentH(res: AST.ResolvedInfo, t: AST.Typed, pos: Position): (State, State.Value) = {
      res match {
        case res: AST.ResolvedInfo.LocalVar =>
          val (s0, sym) = state.freshSym(t, pos)
          return (s0.addClaim(State.Claim.Def.CurrentId(sym, res.context, res.id, None())), sym)
        case AST.ResolvedInfo.Var(T, F, T, AST.Typed.sireumName, id) if id == "T" || id == "F" =>
          return (state, if (id == "T") State.Value.B(T, pos) else State.Value.B(F, pos))
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalIdent(exp: AST.Exp.Ident): (State, State.Value) = {
      return evalIdentH(exp.attr.resOpt.get, exp.attr.typedOpt.get, exp.posOpt.get)
    }

    def evalUnaryExp(exp: AST.Exp.Unary): (State, State.Value) = {

      val s0 = state

      exp.attr.resOpt.get match {
        case AST.ResolvedInfo.BuiltIn(kind) if isBasic(exp.typedOpt.get) =>
          val (s1, v) = evalExp(s0, exp.exp, reporter)
          if (!s1.status) {
            return (s1, State.errorValue)
          }
          kind match {
            case AST.ResolvedInfo.BuiltIn.Kind.UnaryPlus => return (s1, v)
            case _ =>
              val (s2, sym) = s1.freshSym(v.tipe, exp.posOpt.get)
              return (s2(claims = s2.claims :+ State.Claim.Def.Unary(sym, exp.op, v)), sym)
          }
        case _ =>
          halt(s"TODO: $exp") // TODO
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

      def checkNonZero(s0: State, op: String, value: State.Value, pos: Position): State = {
        val (s1, sym) = s0.freshSym(AST.Typed.b, pos)
        val tipe = value.tipe.asInstanceOf[AST.Typed.Name]
        val claim = State.Claim.Def.Binary(sym, value, AST.Exp.BinaryOp.Ne, zero(tipe, pos), tipe)
        val valid = smt2.valid(s"non-zero second operand of '$op' at [${pos.beginLine}, ${pos.beginColumn}]",
          s0.claims :+ claim, State.Claim.Prop(sym))
        if (valid) {
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
          val tipe = v1.tipe.asInstanceOf[AST.Typed.Name]
          if (isCond(kind)) {
            halt(s"TODO: $e") // TODO
          } else if (isSeq(kind)) {
            halt(s"TODO: $e") // TODO
          } else if (isBasic(tipe)) {
            val (s2, v2) = evalExp(s1, exp.right, reporter)
            val s3: State = if (reqNonZeroCheck(kind)) {
              checkNonZero(s2, exp.op, v2, exp.right.posOpt.get)
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

    def evalSelectH(res: AST.ResolvedInfo, receiverOpt: Option[AST.Exp], id: String, tipe: AST.Typed, pos: Position): (State, State.Value) = {
      def evalField(t: AST.Typed): (State, State.Value) = {
        receiverOpt match {
          case Some(receiver) =>
            val (s0, o) = evalExp(state, receiver, reporter)
            if (!s0.status) {
              return (s0, State.errorValue)
            }
            val (s1, sym) = s0.freshSym(t, pos)
            return (s1.addClaim(State.Claim.Def.FieldLookup(sym, o, smt2.fieldId(receiver.typedOpt.get, id))), sym)
          case _ => halt(s"TODO: $e") // TODO
        }
      }
      res match {
        case res: AST.ResolvedInfo.Var =>
          if (res.isInObject) {
            halt(s"TODO: $e") // TODO
          } else {
            return evalField(tipe)
          }
        case res:AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method && res.tpeOpt.get.isByName =>
          return evalField(res.tpeOpt.get.ret)
        case res: AST.ResolvedInfo.LocalVar => return evalIdentH(res, tipe, pos)
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalSelect(exp: AST.Exp.Select): (State, State.Value) = {
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Ext && res.owner.size == 3
          && ops.ISZOps(res.owner).dropRight(1) == AST.Typed.sireumName && res.id == "random" =>
          val s0 = state
          val (s1, num) = s0.fresh
          return (s1, State.Value.Sym(num, res.tpeOpt.get.ret, exp.posOpt.get))
        case res => return evalSelectH(res, exp.receiverOpt, exp.id.value, exp.typedOpt.get, exp.posOpt.get)
      }
    }

    def evalConstructor(exp: AST.Exp.Invoke, res: AST.ResolvedInfo.Method): (State, State.Value) = {
      val t = exp.typedOpt.get.asInstanceOf[AST.Typed.Name]
      var current = state
      var args = ISZ[State.Value]()
      for (arg <- exp.args) {
        val (s0, v) = evalExp(current, arg, reporter)
        if (!s0.status) {
          return (s0, State.errorValue)
        }
        current = s0
        args = args :+ v
      }
      val (s1, sym) = current.freshSym(t, exp.posOpt.get)
      if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
        val it = t.args(0).asInstanceOf[AST.Typed.Name]
        var indices = ISZ[State.Value]()
        if (it == AST.Typed.z) {
          indices = for (i <- 0 until args.size) yield State.Value.Z(i, args(i).pos)
        } else {
          val subz = smt2.typeHierarchy.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ].ast
          @pure def z2subz(n: Z, pos: Position): State.Value = {
            if (subz.isBitVector) {
              if (subz.bitWidth == 8) {
                return if (subz.isSigned) State.Value.S8(conversions.Z.toS8(n), it, pos)
                else State.Value.U8(conversions.Z.toU8(n), it, pos)
              } else if (subz.bitWidth == 16) {
                return if (subz.isSigned) State.Value.S16(conversions.Z.toS16(n), it, pos)
                else State.Value.U16(conversions.Z.toU16(n), it, pos)
              } else if (subz.bitWidth == 32) {
                return if (subz.isSigned) State.Value.S32(conversions.Z.toS32(n), it, pos)
                else State.Value.U32(conversions.Z.toU32(n), it, pos)
              } else if (subz.bitWidth == 64) {
                return if (subz.isSigned) State.Value.S64(conversions.Z.toS64(n), it, pos)
                else State.Value.U64(conversions.Z.toU64(n), it, pos)
              } else {
                halt(s"Infeasible bit-width: ${subz.bitWidth}")
              }
            } else {
              return State.Value.Range(n, it, pos)
            }
          }
          var i = 0
          var index = subz.index
          while (i < args.size) {
            indices = indices :+ z2subz(index, args(i).pos)
            index = index + 1
            i = i + 1
          }
        }
        return (s1.addClaim(State.Claim.Def.SeqLit(sym, ops.ISZOps(indices).zip(args),
          smt2.fieldId(t, "size"), smt2.typeOpId(t, "at"))), sym)
      } else {
        return (s1.addClaim(State.Claim.Def.AdtLit(sym, adtSmtParamNames(t), args)), sym)
      }
    }

    def evalSeqSelect(exp: AST.Exp.Invoke, res: AST.ResolvedInfo.Method): (State, State.Value) = {
      val t = exp.ident.typedOpt.get.asInstanceOf[AST.Typed.Name]
      val (s0, seq) = evalSelectH(exp.ident.attr.resOpt.get, exp.receiverOpt, exp.ident.id.value, t, exp.ident.posOpt.get)
      val (s1, i) = evalExp(s0, exp.args(0), reporter)
      val (s2, v) = s1.freshSym(exp.typedOpt.get, exp.posOpt.get)
      return (s2.addClaim(State.Claim.Def.SeqLookup(v, seq, i, smt2.typeOpId(t, "at"))), v)
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
      case e: AST.Exp.Ident => return evalIdent(e)
      case e: AST.Exp.Select => return evalSelect(e)
      case e: AST.Exp.Unary => return evalUnaryExp(e)
      case e: AST.Exp.Binary => return evalBinaryExp(e)
      case e: AST.Exp.Invoke =>
        e.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method =>
            res.mode match {
              case AST.MethodMode.Constructor => return evalConstructor(e, res)
              case AST.MethodMode.Select => return evalSeqSelect(e, res)
              case _ =>
            }
          case _ =>
        }
        halt(s"TODO: $e") // TODO
      case _ => halt(s"TODO: $e") // TODO
    }
  }

  def value2Sym(s0: State, v: State.Value, pos: Position): (State, State.Value.Sym) = {
    v match {
      case v: State.Value.Sym => return (s0, v)
      case _ =>
        val (s2, symV) = s0.freshSym(v.tipe, pos)
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
      val pos = cond.posOpt.get
      val sat = smt2.sat(s"Assumption at [${pos.beginLine}, ${pos.beginColumn}]", s3.claims)
      return s3(status = sat)
    }

    def evalAssert(s0: State, cond: AST.Exp): State = {
      val (s1, v) = evalExp(s0, cond, reporter)
      if (!s1.status) {
        return s1
      }
      val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
      val conclusion = State.Claim.Prop(sym)
      val pos = cond.posOpt.get
      val valid = smt2.valid(s"Assertion at [${pos.beginLine}, ${pos.beginColumn}]", s2.claims, conclusion)
      if (!valid) {
        reporter.error(cond.posOpt, Logika.kind, s"Cannot deduce that the assertion condition holds")
      }
      return s2(status = valid, claims = s2.claims :+ conclusion)
    }

    def evalAssignExp(s0: State, ae: AST.AssignExp): (State, State.Value) = {
      ae match {
        case AST.Stmt.Expr(exp) => return evalExp(s0, exp, reporter)
        case _ => halt(s"TODO: $ae") // TODO
      }
    }

    def evalAssignLocal(decl: B, s0: State, context: ISZ[String], id: String, rhs: AST.AssignExp, idPos: Position): State = {
      val (s1, init) = evalAssignExp(s0, rhs)
      if (!s1.status) {
        return s1
      }
      val (s2, sym) = value2Sym(s1, init, rhs.asStmt.posOpt.get)
      val s4: State =
        if (decl) {
          s2
        } else {
          val poss = StateTransformer(Logika.CurrentIdPossCollector(context, id)).transformState(ISZ(), s2).ctx
          assert(poss.nonEmpty)
          val (s3, num) = s2.fresh
          val locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)] + (context, id) ~> ((poss, num))
          StateTransformer(Logika.CurrentIdRewriter(locals)).transformState(T, s3).resultOpt.get
        }
      return s4(claims = s4.claims :+ State.Claim.Def.CurrentId(sym, context, id, Some(idPos)))
    }

    def evalIf(s0: State, ifStmt: AST.Stmt.If): State = {
      val (s1, v) = evalExp(s0, ifStmt.cond, reporter)
      val pos = ifStmt.cond.posOpt.get
      val (s2, cond) = value2Sym(s1, v, pos)
      if (!s2.status) {
        return s2
      }
      val prop = State.Claim.Prop(cond)
      val thenClaims = s2.claims :+ prop
      var thenSat = smt2.sat(s"if-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", thenClaims)
      val s4: State = if (thenSat) {
        val s3 = evalBody(s2(claims = thenClaims), ifStmt.thenBody, reporter)
        thenSat = s3.status
        s3
      } else {
        s2(claims = thenClaims)
      }
      val negProp = State.Claim.Neg(prop)
      val elseClaims = s2.claims :+ negProp
      var elseSat = smt2.sat(s"if-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", elseClaims)
      val s6: State = if (elseSat) {
        val s5 = evalBody(s2(claims = elseClaims, nextFresh = s4.nextFresh), ifStmt.elseBody, reporter)
        elseSat = s5.status
        s5
      } else {
        s2(claims = elseClaims, nextFresh = s4.nextFresh)
      }
      (thenSat, elseSat) match {
        case (T, T) => return mergeStates(s2, cond, s4, s6, s6.nextFresh)
        case (T, F) => return s4(status = s4.status && !reporter.hasError, nextFresh = s6.nextFresh)
        case (F, T) => return s6(status = s6.status && !reporter.hasError)
        case _ =>
          val s7 = mergeStates(s2, cond, s4, s6, s6.nextFresh)
          return s7(status = F)
      }
    }

    def evalWhile(s0: State, whileStmt: AST.Stmt.While): State = {
      val s1 = checkExps("Loop invariant", " at the beginning of while-loop", s0, whileStmt.invariants, reporter)
      if (!s1.status) {
        return s1
      }
      val modLocalVars = whileStmt.modifiedLocalVars
      val s0R: State = {  // TODO: rewrite Vars as well
        var srw = rewriteLocalVars(s0(nextFresh = s1.nextFresh), modLocalVars.keys)
        for (p <- modLocalVars.entries) {
          val (res, (tipe, pos)) = p
          val (srw1, sym) = srw.freshSym(tipe, pos)
          srw = srw1(claims = srw1.claims :+ State.Claim.Def.CurrentId(sym, res.context, res.id, Some(pos)))
        }
        srw
      }
      val s2 = State(T, s0R.claims ++ (for (i <- s0.claims.size until s1.claims.size) yield s1.claims(i)), s0R.nextFresh)
      val (s3, v) = evalExp(s2, whileStmt.cond, reporter)
      val pos = whileStmt.cond.posOpt.get
      val (s4, cond) = value2Sym(s3, v, pos)
      val prop = State.Claim.Prop(cond)
      val thenClaims = s4.claims :+ prop
      var thenSat = smt2.sat(s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", thenClaims)
      val nextFresh: Z = if (thenSat) {
        val s5 = evalStmts(s4(claims = thenClaims), whileStmt.body.stmts, reporter)
        thenSat = s5.status
        if (thenSat) {
          val s6 = checkExps("Loop invariant", " at the end of while-loop",
            s5, whileStmt.invariants, reporter)
          s6.nextFresh
        } else {
          s5.nextFresh
        }
      } else {
        s4.nextFresh
      }
      val negProp = State.Claim.Neg(prop)
      val elseClaims = s4.claims :+ negProp
      val elseSat = smt2.sat(s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", elseClaims)
      return State(status = elseSat, claims = elseClaims, nextFresh = nextFresh)
    }

    @pure def loopBound(ids: ISZ[String]): Z = {
      return config.loopBounds.get(ids).getOrElse(config.defaultLoopBound)
    }

    def evalWhileUnroll(s0: State, whileStmt: AST.Stmt.While): State = {
      val loopId: ISZ[String] = whileStmt.context
      def rec(current: State, numLoops: Z): State = {
        val s1 = checkExps("Loop invariant", " at the beginning of while-loop", current,
          whileStmt.invariants, reporter)
        if (!s1.status) {
          return s1
        }
        val (s2, v) = evalExp(s1, whileStmt.cond, reporter)
        val pos = whileStmt.cond.posOpt.get
        val (s3, cond) = value2Sym(s2, v, pos)
        val prop = State.Claim.Prop(cond)
        val thenClaims = s3.claims :+ prop
        var thenSat = smt2.sat(s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", thenClaims)
        val s6: State = if (thenSat) {
          val s4 = evalStmts(s3(claims = thenClaims), whileStmt.body.stmts, reporter)
          thenSat = s4.status
          if (thenSat) {
            val bound = loopBound(loopId)
            if (bound <= 0 || numLoops + 1 < loopBound(loopId)) {
              val s5 = rec(s4, numLoops + 1)
              s5
            } else {
              if (bound > 0) {
                reporter.warn(whileStmt.cond.posOpt, Logika.kind,
                  s"Under-approximation due to loop unrolling capped with bound $bound")
                s4(status = F)
              } else {
                s4
              }
            }
          } else {
            s4
          }
        } else {
          s3
        }
        val negProp = State.Claim.Neg(prop)
        val elseClaims = s3.claims :+ negProp
        val elseSat = smt2.sat(s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", elseClaims)
        (thenSat, elseSat) match {
          case (T, T) => return mergeStates(s3, cond, s6, s3, s6.nextFresh)
          case (T, F) => return s6(status = s6.status && !reporter.hasError)
          case (F, T) => return s3(status = s3.status && !reporter.hasError, nextFresh = s6.nextFresh)
          case _ =>
            val s7 = mergeStates(s3, cond, s6, s3, s6.nextFresh)
            return s7(status = F)
        }
      }
      return rec(s0, 0)
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
          case res: AST.ResolvedInfo.LocalVar =>
            return evalAssignLocal(T, state, res.context, res.id, stmt.initOpt.get, stmt.id.attr.posOpt.get)
          case _ => halt(s"TODO: $stmt") // TODO
        }
      case AST.Stmt.Assign(lhs: AST.Exp.Ident, rhs) =>
        lhs.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar =>
            return evalAssignLocal(F, state, res.context, res.id, rhs, lhs.posOpt.get)
          case _ => halt(s"TODO: $stmt") // TODO
        }
      case stmt: AST.Stmt.If => return evalIf(state, stmt)
      case stmt: AST.Stmt.While =>
        return if (stmt.modifies.nonEmpty) evalWhile(state, stmt) else evalWhileUnroll(state, stmt)
      case _: AST.Stmt.Import => return state
      case _ =>
        halt(s"TODO: $stmt") // TODO
    }

  }

  def checkExp(title: String, titleSuffix: String, s0: State, exp: AST.Exp, reporter: Reporter): State = {
    val (s1, v) = evalExp(s0, exp, reporter)
    val pos = exp.posOpt.get
    val (s2, sym) = value2Sym(s1, v, pos)
    val prop = State.Claim.Prop(sym)
    val valid: B = {
      val vld = smt2.valid(s"$title at [${pos.beginLine}, ${pos.beginColumn}]", s2.claims, prop)
      if (!vld) {
        reporter.error(exp.posOpt, Logika.kind,
          s"Cannot deduce the ${ops.StringOps(title).firstToLower} holds$titleSuffix")
      }
      vld
    }
    return s2(status = valid, claims = s2.claims :+ prop)
  }

  def checkExps(title: String, titleSuffix: String, s0: State, exps: ISZ[AST.Exp], reporter: Reporter): State = {
    var current = s0
    for (exp <- exps) {
      if (!current.status) {
        return current
      }
      current = checkExp(title, titleSuffix, current, exp, reporter)
    }
    return current
  }

  def mergeStates(s0: State, cond: State.Value.Sym, sT: State, sF: State, nextFresh: Z): State = {
    @pure def mergeClaimPrefix(tClaim: State.Claim, fClaim: State.Claim): State.Claim = {
      return if (tClaim == fClaim) tClaim else State.Claim.If(cond, tClaim, fClaim)
    }
    val size = s0.claims.size
    val prefixClaims: ISZ[State.Claim] =
      for (i <- 0 until size) yield mergeClaimPrefix(sT.claims(i), sF.claims(i))
    return State(s0.status, prefixClaims :+
      State.Claim.If(cond, State.Claim.And(ops.ISZOps(sT.claims).drop(size + 1)),
        State.Claim.And(ops.ISZOps(sF.claims).drop(size + 1))), nextFresh)
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

  def evalBody(state: State, body: AST.Body, reporter: Reporter): State = {
    val s0 = state
    val s1 = evalStmts(s0, body.stmts, reporter)
    if (!s1.status) {
      return s1
    }
    return rewriteLocalVars(s1, body.undecls)
  }

  def rewriteLocalVars(state: State, localVars: ISZ[AST.ResolvedInfo.LocalVar]): State = {
    var current = state
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)]
    for (l <- localVars) {
      val poss = StateTransformer(Logika.CurrentIdPossCollector(l.context, l.id)).
        transformState(ISZ(), current).ctx
      assert(poss.nonEmpty)
      val (s1, num) = current.fresh
      current = s1
      locals = locals + (l.context, l.id) ~> ((poss, num))
    }
    return if (locals.isEmpty) current
    else StateTransformer(Logika.CurrentIdRewriter(locals)).transformState(T, current).resultOpt.get
  }

  def evalBlock(state: State, block: AST.Stmt.Block, reporter: Reporter): State = {
    return evalBody(state, block.body, reporter)
  }

}
