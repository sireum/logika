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
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.{ast => AST}
import org.sireum.message.{Position, Reporter}
import StateTransformer.{PrePost, PreResult}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.Logika.{ContractCaseResult, InvokeMethodInfo}

object Logika {

  @datatype class CurrentIdPossCollector(context: ISZ[String], id: String) extends PrePost[ISZ[Position]] {
    override def preStateClaimLetCurrentId(ctx: ISZ[Position],
                                           o: State.Claim.Let.CurrentId): PreResult[ISZ[Position], State.Claim.Let] = {
      return if (o.defPosOpt.nonEmpty && o.context == context && o.id == id) PreResult(ctx :+ o.defPosOpt.get, T, None())
      else PreResult(ctx, T, None())
    }
  }

  @datatype class CurrentNamePossCollector(ids: ISZ[String]) extends PrePost[ISZ[Position]] {
    override def preStateClaimLetCurrentName(ctx: ISZ[Position],
                                             o: State.Claim.Let.CurrentName): PreResult[ISZ[Position], State.Claim.Let] = {
      return if (o.defPosOpt.nonEmpty && o.ids == ids) PreResult(ctx :+ o.defPosOpt.get, T, None())
      else PreResult(ctx, T, None())
    }
  }

  @datatype class CurrentIdRewriter(map: HashMap[(ISZ[String], String), (ISZ[Position], Z)]) extends PrePost[ISZ[State.Claim]] {
    override def preStateClaimLetCurrentId(ctx: ISZ[State.Claim],
                                           o: State.Claim.Let.CurrentId): PreResult[ISZ[State.Claim], State.Claim.Let] = {
      map.get((o.context, o.id)) match {
        case Some((poss, num)) => return PreResult(ctx :+ o, T, Some(State.Claim.Let.Id(o.sym, o.context, o.id, num, poss)))
        case _ => return PreResult(ctx, T, None())
      }
    }
  }

  @datatype class CurrentNameRewriter(map: HashMap[ISZ[String], (ISZ[Position], Z)]) extends PrePost[B] {
    override def preStateClaimLetCurrentName(ctx: B,
                                             o: State.Claim.Let.CurrentName): PreResult[B, State.Claim.Let] = {
      map.get(o.ids) match {
        case Some((poss, num)) => return PreResult(ctx, T, Some(State.Claim.Let.Name(o.sym, o.ids, num, poss)))
        case _ => return PreResult(ctx, T, None())
      }
    }
  }

  @datatype class Config(defaultLoopBound: Z,
                         loopBounds: HashMap[ISZ[String], Z],
                         smt2TimeoutInSeconds: Z,
                         logPc: B,
                         logRawPc: B,
                         logVc: B)

  object Context {
    @strictpure def empty: Context = Context(ISZ(), None(), ISZ())
  }

  @datatype class Context(typeParams: ISZ[AST.TypeParam],
                          methodOpt: Option[MethodContext],
                          caseLabels: ISZ[AST.Exp.LitString],
                         )

  @datatype class MethodContext(name: ISZ[String],
                                receiverTypeOpt: Option[AST.Typed],
                                sig: AST.MethodSig,
                                reads: ISZ[AST.Exp.Ident],
                                modifies: ISZ[AST.Exp.Ident],
                                objectVarInMap: HashMap[ISZ[String], State.Value.Sym],
                                fieldVarInMap: HashMap[String, State.Value.Sym],
                                localInMap: HashMap[String, State.Value.Sym],
                                posOpt: Option[Position]) {
    def objectVarMap(sm: HashMap[String, AST.Typed]): HashSMap[ISZ[String], AST.Typed] = {
      var r = HashSMap.empty[ISZ[String], AST.Typed]
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var if res.isInObject && !r.contains(res.owner :+ res.id) =>
            val ids = res.owner :+ res.id
            r = r + ids ~> x.typedOpt.get.subst(sm)
          case _ =>
        }
      }
      return r
    }

    def fieldVarMap(sm: HashMap[String, AST.Typed]): HashSMap[String, (AST.Typed, Option[Position])] = {
      var r = HashSMap.empty[String, (AST.Typed, Option[Position])]
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var if !res.isInObject && !r.contains(res.id) =>
            r = r + res.id ~> ((x.typedOpt.get.subst(sm), x.posOpt))
          case _ =>
        }
      }
      return r
    }

    def localMap(sm: HashMap[String, AST.Typed]): HashSMap[String, (ISZ[String], AST.Id, AST.Typed)] = {
      var r = HashSMap.empty[String, (ISZ[String], AST.Id, AST.Typed)]
      for (p <- sig.params) {
        r = r + p.id.value ~> ((name, p.id, p.tipe.typedOpt.get.subst(sm)))
      }
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar if !r.contains(x.id.value) =>
            r = r + x.id.value ~> ((res.context, x.id, x.typedOpt.get.subst(sm)))
          case _ =>
        }
      }
      return r
    }
  }

  @datatype class InvokeMethodInfo(sig: AST.MethodSig, contract: AST.MethodContract)

  @datatype class ContractCaseResult(isPreOK: B,
                                     state: State,
                                     retVal: State.Value,
                                     requiresClaim: State.Claim.Prop,
                                     messages: ISZ[message.Message]) {
    @strictpure def isOK: B = state.status
  }

  val kind: String = "Logika"

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
          val smt2 = smt2f(th)
          val logika = Logika(th, config, Context.empty, smt2)
          val state = logika.evalStmts(State.create, p.body.stmts, reporter)
          if (config.logPc && p.body.stmts.nonEmpty) {
            val lastPos = p.body.stmts(p.body.stmts.size - 1).posOpt.get
            logika.logPc(config.logPc, config.logRawPc, state, reporter, Some(Logika.afterPos(lastPos)))
          }

          def rec(stmts: ISZ[AST.Stmt]): Unit = {
            for (stmt <- stmts) {
              stmt match {
                case stmt: AST.Stmt.Method if stmt.bodyOpt.nonEmpty => checkMethod(th, stmt, config, smt2, reporter)
                case stmt: AST.Stmt.Object => rec(stmt.stmts)
                case stmt: AST.Stmt.Adt => rec(stmt.stmts)
                case stmt: AST.Stmt.Sig => rec(stmt.stmts)
                case _ =>
              }
            }
          }

          rec(p.body.stmts)
        }
      case _ =>
    }
  }

  def logikaMethod(th: TypeHierarchy, config: Config, smt2: Smt2, name: ISZ[String], receiverTypeOpt: Option[AST.Typed],
                   sig: AST.MethodSig, posOpt: Option[Position], reads: ISZ[AST.Exp.Ident], modifies: ISZ[AST.Exp.Ident],
                   caseLabels: ISZ[AST.Exp.LitString]): Logika = {
    val mctx = MethodContext(name, receiverTypeOpt, sig, reads, modifies, HashMap.empty, HashMap.empty, HashMap.empty, posOpt)
    val ctx = Context.empty(methodOpt = Some(mctx), caseLabels = caseLabels)
    return Logika(th, config, ctx, smt2)
  }

  def checkMethod(th: TypeHierarchy, method: AST.Stmt.Method, config: Config, smt2: Smt2, reporter: Reporter): Unit = {
    def checkCase(labelOpt: Option[AST.Exp.LitString], reads: ISZ[AST.Exp.Ident], requires: ISZ[AST.Exp],
                  modifies: ISZ[AST.Exp.Ident], ensures: ISZ[AST.Exp]): Unit = {
      var state = State.create
      labelOpt match {
        case Some(label) => state = state.addClaim(State.Claim.Label(label.value, label.posOpt.get))
        case _ =>
      }
      val logika: Logika = {
        val res = method.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
        val mname = res.owner :+ method.sig.id.value
        val receiverTypeOpt: Option[AST.Typed] = if (res.isInObject) {
          None()
        } else {
          th.typeMap.get(res.owner).get match {
            case ti: TypeInfo.Sig => Some(ti.tpe)
            case ti: TypeInfo.Adt => Some(ti.tpe)
            case _ => halt("Infeasible")
          }
        }
        val l = logikaMethod(th, config, smt2, mname, receiverTypeOpt, method.sig, method.posOpt, reads, modifies,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get))
        val mctx = l.context.methodOpt.get
        var objectVarInMap = mctx.objectVarInMap
        for (p <- mctx.objectVarMap(TypeChecker.emptySubstMap).entries) {
          val (ids, t) = p
          val posOpt = th.nameMap.get(ids).get.posOpt
          val (s, sym) = nameIntro(posOpt.get, state, ids, t, posOpt)
          objectVarInMap = objectVarInMap + ids ~> sym
          state = s
        }
        var fieldVarInMap = mctx.fieldVarInMap
        mctx.receiverTypeOpt match {
          case Some(receiverType) =>
            val (s0, thiz) = idIntro(method.posOpt.get, state, mname, "this", receiverType, method.sig.id.attr.posOpt)
            state = s0
            for (p <- mctx.fieldVarMap(TypeChecker.emptySubstMap).entries) {
              val (id, (t, posOpt)) = p
              val (s1, sym) = state.freshSym(t, posOpt.get)
              state = s1.addClaim(State.Claim.Let.FieldLookup(sym, thiz, id))
              fieldVarInMap = fieldVarInMap + id ~> sym
            }
          case _ =>
        }
        var localInMap = mctx.localInMap
        for (v <- mctx.localMap(TypeChecker.emptySubstMap).values) {
          val (mname, id, t) = v
          val posOpt = id.attr.posOpt
          val (s, sym) = idIntro(posOpt.get, state, mname, id.value, t, posOpt)
          localInMap = localInMap + id.value ~> sym
          state = s
        }
        l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
          localInMap = localInMap))))
      }
      for (r <- requires if state.status) {
        state = logika.evalAssume(F, "Precondition", state, r, reporter)._1
      }
      val stmts = method.bodyOpt.get.stmts
      state = logika.evalStmts(state, stmts, reporter)
      for (e <- ensures if state.status) {
        state = logika.evalAssert(F, "Postcondition", state, e, reporter)._1
      }
      if (stmts.nonEmpty) {
        logika.logPc(config.logPc, config.logRawPc, state, reporter,
          Some(Logika.afterPos(stmts(stmts.size - 1).posOpt.get)))
      }
    }

    method.contract match {
      case contract: AST.MethodContract.Simple =>
        checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures)
      case contract: AST.MethodContract.Cases =>
        for (c <- contract.cases) {
          checkCase(Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
        }
    }
  }

  @pure def idIntro(pos: Position, state: State, idContext: ISZ[String],
                    id: String, t: AST.Typed, idPosOpt: Option[Position]): (State, State.Value.Sym) = {
    val (s0, sym) = state.freshSym(t, pos)
    return (s0.addClaim(State.Claim.Let.CurrentId(sym, idContext, id, idPosOpt)), sym)
  }

  @pure def nameIntro(pos: Position, state: State, ids: ISZ[String], t: AST.Typed,
                      namePosOpt: Option[Position]): (State, State.Value.Sym) = {
    val (s0, sym) = state.freshSym(t, pos)
    return (s0.addClaim(State.Claim.Let.CurrentName(sym, ids, namePosOpt)), sym)
  }

  @pure def resIntro(pos: Position, state: State, context: ISZ[String], t: AST.Typed,
                     posOpt: Option[Position]): (State, State.Value.Sym) = {
    return idIntro(pos, state, context, "Res", t, posOpt)
  }

  def collectLocalPoss(s0: State, lcontext: ISZ[String], id: String): ISZ[Position] = {
    return StateTransformer(Logika.CurrentIdPossCollector(lcontext, id)).transformState(ISZ(), s0).ctx
  }

  def rewriteLocal(s0: State, lcontext: ISZ[String], id: String): State = {
    val poss = collectLocalPoss(s0, lcontext, id)
    assert(poss.nonEmpty)
    val (s1, num) = s0.fresh
    val locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)] + (lcontext, id) ~> ((poss, num))
    return StateTransformer(Logika.CurrentIdRewriter(locals)).transformState(ISZ(), s1).resultOpt.get
  }

  def rewriteLocals(s0: State, lcontext: ISZ[String], ids: ISZ[String]): (State, ISZ[State.Claim]) = {
    if (ids.isEmpty) {
      return (s0, ISZ())
    }
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)]
    var s1 = s0
    for (id <- ids) {
      val poss = collectLocalPoss(s0, lcontext, id)
      if (poss.nonEmpty) {
        val (s2, num) = s1.fresh
        locals = locals + (lcontext, id) ~> ((poss, num))
        s1 = s2
      }
    }
    val r = StateTransformer(Logika.CurrentIdRewriter(locals)).transformState(ISZ(), s1)
    return (r.resultOpt.getOrElse(s1), r.ctx)
  }

  def rewriteLocalVars(state: State, localVars: ISZ[AST.ResolvedInfo.LocalVar]): State = {
    if (localVars.isEmpty) {
      return state
    }
    var current = state
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)]
    for (l <- localVars) {
      val poss = StateTransformer(Logika.CurrentIdPossCollector(l.context, l.id)).
        transformState(ISZ(), current).ctx
      assert(poss.nonEmpty, s"No definition for $l")
      val (s1, num) = current.fresh
      current = s1
      locals = locals + (l.context, l.id) ~> ((poss, num))
    }
    return StateTransformer(Logika.CurrentIdRewriter(locals)).transformState(ISZ(), current).resultOpt.get
  }

  def rewriteObjectVars(state: State, objectVars: HashSMap[AST.ResolvedInfo.Var, (AST.Typed, Position)],
                        pos: Position): State = {
    if (objectVars.isEmpty) {
      return state
    }
    var current = state
    var vars = HashMap.empty[ISZ[String], (ISZ[Position], Z)]
    for (l <- objectVars.keys) {
      val ids = l.owner :+ l.id
      val poss = StateTransformer(Logika.CurrentNamePossCollector(ids)).
        transformState(ISZ(), current).ctx
      assert(poss.nonEmpty, s"No definition for $l")
      val (s1, num) = current.fresh
      current = s1
      vars = vars + ids ~> ((poss, num))
    }
    current = StateTransformer(Logika.CurrentNameRewriter(vars)).transformState(T, current).resultOpt.get
    for (p <- objectVars.entries) {
      val (x, (t, namePos)) = p
      current = nameIntro(pos, current, x.owner :+ x.id, t, Some(namePos))._1
    }
    return current
  }

  def conjunctClaimSuffix(s0: State, s1: State): State = {
    if (s1.claims.size - s0.claims.size <= 1) {
      assert(s1.claims.size - s0.claims.size >= 0)
      return s1
    }
    val size1 = s0.claims.size
    val size2 = s1.claims.size
    val claimsOps = ops.ISZOps(s1.claims)
    return s1(claims = claimsOps.slice(0, size1) :+ State.Claim.And(claimsOps.slice(size1, size2)))
  }

  @strictpure def afterPos(pos: Position): Position = message.FlatPos(pos.uriOpt,
    conversions.Z.toU32(pos.endLine + 1),
    conversions.Z.toU32(1),
    conversions.Z.toU32(pos.endLine + 1),
    conversions.Z.toU32(2),
    conversions.Z.toU32(pos.offset),
    conversions.Z.toU32(1))
}

@record class Logika(th: lang.tipe.TypeHierarchy,
                     config: Logika.Config,
                     context: Logika.Context,
                     smt2: Smt2) {

  val timeoutInMs: Z = config.smt2TimeoutInSeconds * 1000

  @pure def isBasic(t: AST.Typed): B = {
    if (Smt2.basicTypes.contains(t)) {
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
    halt(s"TODO: 0 of type $tipe") // TODO
  }

  def checkSeqIndexing(rtCheck: B, s0: State, seq: State.Value, i: State.Value, posOpt: Option[Position],
                       reporter: Reporter): State = {
    if (!rtCheck) {
      return s0
    }
    val pos = posOpt.get
    val (s1, v) = s0.freshSym(AST.Typed.b, pos)
    val s2 = s1.addClaim(State.Claim.Let.SeqInBound(v, seq, i))
    val claim = State.Claim.Prop(T, v)
    val valid = smt2.valid(config.logVc, s"Implicit Indexing Assertion at [${pos.beginLine}, ${pos.beginColumn}]",
      s2.claims, claim, timeoutInMs, reporter)
    if (valid) {
      return s2.addClaim(claim)
    } else {
      error(Some(pos), s"Could not deduce sequence indexing is in bound", reporter)
      return s2(status = F)
    }
  }

  def evalLit(lit: AST.Lit): State.Value = {
    lit match {
      case e: AST.Exp.LitB => return State.Value.B(e.value, e.posOpt.get)
      case e: AST.Exp.LitC => return State.Value.C(e.value, e.posOpt.get)
      case e: AST.Exp.LitF32 => return State.Value.F32(e.value, e.posOpt.get)
      case e: AST.Exp.LitF64 => return State.Value.F64(e.value, e.posOpt.get)
      case e: AST.Exp.LitR => return State.Value.R(e.value, e.posOpt.get)
      case e: AST.Exp.LitString => return State.Value.String(e.value, e.posOpt.get)
      case e: AST.Exp.LitZ => return State.Value.Z(e.value, e.posOpt.get)
    }
  }

  def evalThisIdH(state: State, id: String, t: AST.Typed, pos: Position): (State, State.Value.Sym) = {
    val mc = context.methodOpt.get
    val (s0, receiver) = Logika.idIntro(pos, state, mc.name, "this", mc.receiverTypeOpt.get, None())
    val (s1, r) = s0.freshSym(t, pos)
    return (s1.addClaim(State.Claim.Let.FieldLookup(r, receiver, id)), r)
  }

  def evalExp(rtCheck: B, state: State, e: AST.Exp, reporter: Reporter): (State, State.Value) = {
    if (!state.status) {
      return (state, State.errorValue)
    }

    def evalIdentH(res: AST.ResolvedInfo, t: AST.Typed, pos: Position): (State, State.Value) = {
      res match {
        case AST.ResolvedInfo.Var(T, F, T, AST.Typed.sireumName, id) if id == "T" || id == "F" =>
          return (state, if (id == "T") State.Value.B(T, pos) else State.Value.B(F, pos))
        case res: AST.ResolvedInfo.LocalVar =>
          val (s0, r) = Logika.idIntro(pos, state, res.context, res.id, t, None())
          return (s0, r)
        case res: AST.ResolvedInfo.Var =>
          if (res.isInObject) {
            val (s0, r) = Logika.nameIntro(pos, state, res.owner :+ res.id, t, None())
            return (s0, r)
          } else {
            val (s0, r) = evalThisIdH(state, res.id, t, pos)
            return (s0, r)
          }
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
          val (s1, v) = evalExp(rtCheck, s0, exp.exp, reporter)
          if (!s1.status) {
            return (s1, State.errorValue)
          }
          kind match {
            case AST.ResolvedInfo.BuiltIn.Kind.UnaryPlus => return (s1, v)
            case _ =>
              val (s2, sym) = s1.freshSym(v.tipe, exp.posOpt.get)
              return (s2(claims = s2.claims :+ State.Claim.Let.Unary(sym, exp.op, v)), sym)
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
        return rtCheck
      }

      def checkNonZero(s0: State, op: String, value: State.Value, pos: Position): State = {
        val (s1, sym) = s0.freshSym(AST.Typed.b, pos)
        val tipe = value.tipe.asInstanceOf[AST.Typed.Name]
        val claim = State.Claim.Let.Binary(sym, value, AST.Exp.BinaryOp.Ne, zero(tipe, pos), tipe)
        val valid = smt2.valid(config.logVc,
          s"non-zero second operand of '$op' at [${pos.beginLine}, ${pos.beginColumn}]",
          s0.claims :+ claim, State.Claim.Prop(T, sym), timeoutInMs, reporter)
        if (valid) {
          return s1.addClaim(claim)
        } else {
          error(Some(pos), s"Could not deduce non-zero second operand for ${exp.op}", reporter)
          return s1(status = F)
        }
      }

      val s0 = state

      exp.attr.resOpt.get match {
        case AST.ResolvedInfo.BuiltIn(kind) =>
          val (s1, v1) = evalExp(rtCheck, s0, exp.left, reporter)
          if (!s1.status) {
            return (s1, State.errorValue)
          }
          val tipe = v1.tipe
          if (isCond(kind)) {
            halt(s"TODO: $e") // TODO
          } else if (isSeq(kind)) {
            halt(s"TODO: $e") // TODO
          } else if (isBasic(tipe) || exp.op == "==" || exp.op == "!=") {
            val (s2, v2) = evalExp(rtCheck, s1, exp.right, reporter)
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
            val s5 = s4.addClaim(State.Claim.Let.Binary(rExp, v1, exp.op, v2, tipe))
            return (s5, rExp)
          } else {
            halt(s"TODO: $e") // TODO
          }
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalSelectH(res: AST.ResolvedInfo, receiverOpt: Option[AST.Exp], id: String, tipe: AST.Typed,
                    pos: Position): (State, State.Value) = {
      def evalField(t: AST.Typed): (State, State.Value) = {
        val (s0, o) = evalExp(rtCheck, state, receiverOpt.get, reporter)
        if (!s0.status) {
          return (s0, State.errorValue)
        }
        val (s1, sym) = s0.freshSym(t, pos)
        return (s1.addClaim(State.Claim.Let.FieldLookup(sym, o, id)), sym)
      }

      def evalEnumElement(eres: AST.ResolvedInfo.EnumElement): (State, State.Value) = {
        return (state, State.Value.Enum(tipe.asInstanceOf[AST.Typed.Name], eres.owner, eres.name, eres.ordinal, pos))
      }

      def evalTupleLit(tres: AST.ResolvedInfo.Tuple): (State, State.Value) = {
        val (s0, sym) = state.freshSym(tipe, pos)
        val (s1, v) = evalExp(rtCheck, s0, receiverOpt.get, reporter)
        if (!s1.status) {
          return (s1, State.errorValue)
        }
        return (s1.addClaim(State.Claim.Let.FieldLookup(sym, v, s"_${tres.index}")), sym)
      }

      res match {
        case res: AST.ResolvedInfo.Var =>
          assert(!res.isInObject && receiverOpt.nonEmpty)
          return evalField(tipe)
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method && res.tpeOpt.get.isByName =>
          return evalField(res.tpeOpt.get.ret)
        case res: AST.ResolvedInfo.LocalVar => return evalIdentH(res, tipe, pos)
        case res: AST.ResolvedInfo.EnumElement => return evalEnumElement(res)
        case res: AST.ResolvedInfo.Tuple =>
          assert(receiverOpt.nonEmpty)
          return evalTupleLit(res)
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalSelect(exp: AST.Exp.Select): (State, State.Value) = {
      val pos = exp.id.attr.posOpt.get
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Ext && res.owner.size == 3
          && ops.ISZOps(res.owner).dropRight(1) == AST.Typed.sireumName && res.id == "random" =>
          val s0 = state
          val (s1, sym) = s0.freshSym(res.tpeOpt.get.ret, pos)
          return (s1.addClaim(State.Claim.Def.Random(sym, pos)), sym)
        case res => return evalSelectH(res, exp.receiverOpt, exp.id.value, exp.typedOpt.get, pos)
      }
    }

    def evalConstructor(isCopy: B,
                        invokeReceiverOpt: Option[AST.Exp],
                        ident: AST.Exp.Ident,
                        eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]],
                        attr: AST.ResolvedAttr,
                        res: AST.ResolvedInfo.Method): (State, State.Value) = {
      val t = attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
      val (s0, receiverOpt): (State, Option[State.Value]) =
        if (isCopy) {
          val p = evalReceiver(invokeReceiverOpt, ident)
          (p._1, Some(p._2))
        } else {
          (state, None())
        }
      val (s1, sym) = s0.freshSym(t, attr.posOpt.get)
      var current = s1
      if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
        var args = ISZ[State.Value]()
        for (arg <- eargs.left) {
          val (s2, v) = evalExp(rtCheck, current, arg, reporter)
          if (!s2.status) {
            return (s2, State.errorValue)
          }
          current = s2
          args = args :+ v
        }
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
        smt2.addSeqLit(t, indices.size)
        return (current.addClaim(State.Claim.Def.SeqLit(sym, ops.ISZOps(indices).zip(args))), sym)
      } else {
        val ti = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
        val params = ti.ast.params
        val args = MSZ.create[Option[State.Value]](params.size, None[State.Value]())
        eargs match {
          case Either.Left(cargs) =>
            var i = 0
            for (arg <- cargs) {
              val (s3, v) = evalExp(rtCheck, current, arg, reporter)
              if (!s3.status) {
                return (s3, State.errorValue)
              }
              current = s3
              args(i) = Some(v)
              i = i + 1
            }
          case Either.Right(cargs) =>
            for (arg <- cargs) {
              val (s3, v) = evalExp(rtCheck, current, arg.arg, reporter)
              if (!s3.status) {
                return (s3, State.errorValue)
              }
              current = s3
              args(arg.index) = Some(v)
            }
            for (i <- 0 until args.size) {
              if (args(i).isEmpty) {
                val receiver = receiverOpt.get
                val param = params(i)
                val pt = param.tipe.typedOpt.get
                val (s4, sym) = current.freshSym(pt, param.id.attr.posOpt.get)
                current = s4.addClaim(State.Claim.Let.FieldLookup(sym, receiver, param.id.value))
                args(i) = Some(sym)
              }
            }
        }
        return (current.addClaim(State.Claim.Def.AdtLit(sym, args.toIS.map((vOpt: Option[State.Value]) => vOpt.get))), sym)
      }
    }

    def evalReceiver(receiverOpt: Option[AST.Exp], ident: AST.Exp.Ident): (State, State.Value) = {
      receiverOpt match {
        case Some(rcv) =>
          ident.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var =>
              return evalSelectH(res, receiverOpt, ident.id.value, ident.typedOpt.get, ident.posOpt.get)
            case _ => return evalExp(rtCheck, state, rcv, reporter)
          }
        case _ => return evalExp(rtCheck, state, ident, reporter)
      }
    }

    def evalSeqSelect(exp: AST.Exp.Invoke): (State, State.Value) = {
      val (s0, seq): (State, State.Value) = evalReceiver(exp.receiverOpt, exp.ident)
      val (s1, i) = evalExp(rtCheck, s0, exp.args(0), reporter)
      val s2 = checkSeqIndexing(rtCheck, s1, seq, i, exp.args(0).posOpt, reporter)
      val (s3, v) = s2.freshSym(exp.typedOpt.get, exp.posOpt.get)
      return (s3.addClaim(State.Claim.Let.SeqLookup(v, seq, i)), v)
    }

    def evalResult(exp: AST.Exp.Result): (State, State.Value) = {
      val (s, sym) = Logika.resIntro(exp.posOpt.get, state, context.methodOpt.get.name, exp.typedOpt.get, None())
      return (s, sym)
    }

    def evalInput(input: AST.Exp.Input): (State, State.Value) = {
      input.exp match {
        case exp: AST.Exp.Ident =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              context.methodOpt.get.localInMap.get(res.id) match {
                case Some(sym) => return (state, sym)
                case _ =>
                  error(exp.posOpt, s"Identifier ${exp.id.value} was not declared to be read/modified", reporter)
                  return (state(status = F), State.Value.B(F, e.posOpt.get))
              }
            case res: AST.ResolvedInfo.Var =>
              if (res.isInObject) {
                val ids = res.owner :+ res.id
                context.methodOpt.get.objectVarInMap.get(ids) match {
                  case Some(sym) => return (state, sym)
                  case _ =>
                    error(exp.posOpt, s"Identifier ${exp.id.value} was not declared to be read/modified", reporter)
                    return (state(status = F), State.Value.B(F, e.posOpt.get))
                }
              } else {
                context.methodOpt.get.fieldVarInMap.get(res.id) match {
                  case Some(sym) =>
                    return (state, sym)
                  case _ =>
                    error(exp.posOpt, s"Identifier ${exp.id.value} was not declared to be read/modified", reporter)
                    return (state(status = F), State.Value.B(F, e.posOpt.get))
                }
              }
            case _ => halt(s"Infeasible: $exp")
          }
        case _ => halt("TODO: non-simple input")
      }
    }

    def evalQuantType(quant: AST.Exp.QuantType): (State, State.Value) = {
      val s0 = state(claims = ISZ())
      val (s1, v) = evalAssignExp(rtCheck, s0, quant.fun.exp, reporter)
      val pos = quant.fun.exp.asStmt.posOpt.get
      val (s2, expSym) = value2Sym(s1, v, pos)
      val quantClaims = s1.claims :+ State.Claim.Prop(T, expSym)
      val (s3, sym) = s2(claims = state.claims).freshSym(AST.Typed.b, pos)
      val vars: ISZ[State.Claim.Let.Quant.Var] =
        for (p <- quant.fun.params) yield State.Claim.Let.Quant.Var.Id(p.idOpt.get.value, p.typedOpt.get)
      return (s3.addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, quantClaims)), sym)
    }

    def methodInfo(isInObject: B, owner: QName, id: String): InvokeMethodInfo = {
      if (isInObject) {
        th.nameMap.get(owner :+ id) match {
          case Some(mi: lang.symbol.Info.Method) => return InvokeMethodInfo(mi.ast.sig, mi.ast.contract)
          case info => halt(s"Infeasible: $owner.$id => $info")
        }
      } else {
        th.typeMap.get(owner) match {
          case Some(info: lang.symbol.TypeInfo.Adt) =>
            info.methods.get(id) match {
              case Some(mi) => return InvokeMethodInfo(mi.ast.sig, mi.ast.contract)
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) => return InvokeMethodInfo(mi.ast.sig, AST.MethodContract.Simple(ISZ(), ISZ(), ISZ(), ISZ()))
                  case _ => halt("Infeasible")
                }
            }
          case Some(info: lang.symbol.TypeInfo.Sig) =>
            info.methods.get(id) match {
              case Some(mi) => return InvokeMethodInfo(mi.ast.sig, mi.ast.contract)
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) => return InvokeMethodInfo(mi.ast.sig, AST.MethodContract.Simple(ISZ(), ISZ(), ISZ(), ISZ()))
                  case _ => halt("Infeasible")
                }
            }
          case Some(info) => halt(s"TODO: $info") // TODO
          case _ => halt("Infeasible")
        }
      }
    }

    def evalInvoke(s0: State,
                   invokeReceiverOpt: Option[AST.Exp],
                   ident: AST.Exp.Ident,
                   eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]],
                   attr: AST.ResolvedAttr): (State, State.Value) = {
      val res = attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val posOpt = attr.posOpt
      val pos = posOpt.get
      val receiverPosOpt: Option[Position] =
        if (invokeReceiverOpt.nonEmpty) invokeReceiverOpt.get.posOpt
        else ident.posOpt
      var typeSubstMap = TypeChecker.emptySubstMap
      var paramArgs = HashSMap.empty[AST.ResolvedInfo.LocalVar, (AST.Typed, AST.Exp)]
      val info = methodInfo(res.isInObject, res.owner, res.id)
      val contract = info.contract
      val isUnit = info.sig.returnType.typedOpt == AST.Typed.unitOpt
      val ctx = res.owner :+ res.id
      val modLocals = contract.modifiedLocalVars

      def modVarsResult(ms0: State, mposOpt: Option[Position], retType: AST.Typed): (State, State.Value) = {
        var ms1 = ms0
        val modObjectVars = contract.modifiedObjectVars
        val mpos = mposOpt.get
        ms1 = Logika.rewriteObjectVars(ms1, modObjectVars, mpos)
        ms1 = Logika.rewriteLocalVars(ms1, modLocals.keys)
        if (isUnit) {
          return (ms1, State.Value.Unit(mpos))
        } else {
          val (s5, v) = Logika.resIntro(mpos, ms1, ctx, retType, mposOpt)
          ms1 = s5
          return (ms1, v)
        }
      }

      def modVarsRewrite(ms0: State, currentReceiverOpt: Option[State.Value.Sym],
                         receiverOpt: Option[State.Value.Sym]): State = {
        var ms1 = ms0
        for (ptarg <- paramArgs.entries) {
          val (p, (t, arg)) = ptarg
          if (modLocals.contains(p)) {
            val (s6, v) = Logika.idIntro(arg.posOpt.get, ms1, p.context, p.id, t, None())
            ms1 = assignRec(s6, arg, v, reporter)
          }
        }
        var rwLocals = paramArgs.keys
        if (!isUnit) {
          rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "Res")
        }
        if (receiverOpt.nonEmpty) {
          rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "this")
        }
        ms1 = Logika.rewriteLocalVars(ms1, rwLocals)
        currentReceiverOpt match {
          case Some(receiver) =>
            ms1 = ms1.addClaim(State.Claim.Let.CurrentId(receiver, context.methodOpt.get.name, "this",
              context.methodOpt.get.posOpt))
          case _ =>
        }
        return ms1
      }

      var s1 = s0
      val receiverOpt: Option[State.Value.Sym] = if (res.isInObject) {
        None()
      } else {
        val p = evalReceiver(invokeReceiverOpt, ident)
        val p2 = value2Sym(p._1, p._2, receiverPosOpt.get)
        s1 = p2._1
        val receiver = p2._2
        val receiverType = receiver.tipe.asInstanceOf[AST.Typed.Name]
        th.typeMap.get(receiverType.ids) match {
          case Some(ti: TypeInfo.Adt) =>
            TypeChecker.buildTypeSubstMap(receiverType.ids, receiverPosOpt, ti.ast.typeParams, receiverType.args,
              reporter) match {
              case Some(sm) => typeSubstMap = typeSubstMap ++ sm.entries
              case _ => return (s1, State.errorValue)
            }
          case Some(ti: TypeInfo.Sig) =>
            TypeChecker.buildTypeSubstMap(receiverType.ids, receiverPosOpt, ti.ast.typeParams, receiverType.args,
              reporter) match {
              case Some(sm) => typeSubstMap = typeSubstMap ++ sm.entries
              case _ => return (s1, State.errorValue)
            }
          case _ => halt(s"Infeasible: $receiverType")
        }
        Some(receiver)
      }
      val currentReceiverOpt: Option[State.Value.Sym] = context.methodOpt match {
        case Some(m) => m.receiverTypeOpt match {
          case Some(currentReceiverType) =>
            val lcontext = context.methodOpt.get.name
            val p = Logika.idIntro(posOpt.get, s1, lcontext, "this", currentReceiverType, None())
            s1 = p._1
            s1 = Logika.rewriteLocal(s1, lcontext, "this")
            Some(p._2)
          case _ => None()
        }
        case _ => None()
      }
      receiverOpt match {
        case Some(receiver) =>
          s1 = s1.addClaim(State.Claim.Let.CurrentId(receiver, res.owner :+ res.id, "this", receiverPosOpt))
        case _ =>
      }
      val argTypes = MSZ.create[AST.Typed](info.sig.params.size, AST.Typed.nothing)
      eargs match {
        case Either.Left(args) =>
          var i = 0
          for (pArg <- ops.ISZOps(info.sig.params).zip(args)) {
            val (p, arg) = pArg
            val (s2, v) = evalExp(rtCheck, s1, arg, reporter)
            val argPos = arg.posOpt.get
            val (s3, sym) = value2Sym(s2, v, argPos)
            val id = p.id.value
            val argType = arg.typedOpt.get
            argTypes(i) = argType
            paramArgs = paramArgs + AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id) ~>
              ((argType, arg))
            s1 = s3.addClaim(State.Claim.Let.CurrentId(sym, ctx, id, Some(argPos)))
            i = i + 1
          }
        case Either.Right(nargs) =>
          for (narg <- nargs) {
            val p = info.sig.params(narg.index)
            val arg = narg.arg
            val (s2, v) = evalExp(rtCheck, s1, arg, reporter)
            val argPos = arg.posOpt.get
            val (s3, sym) = value2Sym(s2, v, argPos)
            val id = p.id.value
            val argType = arg.typedOpt.get
            argTypes(narg.index) = argType
            paramArgs = paramArgs + AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id) ~>
              ((argType, arg))
            s1 = s3.addClaim(State.Claim.Let.CurrentId(sym, ctx, id, Some(argPos)))
          }
      }
      val mType = info.sig.funType
      val invokeType = mType(args = argTypes.toIS, ret = attr.typedOpt.get)
      TypeChecker.unify(th, posOpt, TypeChecker.TypeRelation.Equal, invokeType, mType, reporter) match {
        case Some(sm) => typeSubstMap = typeSubstMap ++ sm.entries
        case _ => return (s1, State.errorValue)
      }
      val logikaComp: Logika = {
        val l = Logika.logikaMethod(th, config, smt2, ctx, receiverOpt.map(t => t.tipe), info.sig, receiverPosOpt,
          contract.reads, contract.modifies, ISZ())
        val mctx = l.context.methodOpt.get
        var objectVarInMap = mctx.objectVarInMap
        for (p <- mctx.objectVarMap(typeSubstMap).entries) {
          val (ids, t) = p
          val (s4, sym) = Logika.nameIntro(pos, s1, ids, t, None())
          objectVarInMap = objectVarInMap + ids ~> sym
          s1 = s4
        }
        var fieldVarInMap = mctx.fieldVarInMap
        mctx.receiverTypeOpt match {
          case Some(receiverType) =>
            val (s5, thiz) = Logika.idIntro(mctx.posOpt.get, s1, mctx.name, "this", receiverType, mctx.sig.id.attr.posOpt)
            s1 = s5
            for (p <- mctx.fieldVarMap(typeSubstMap).entries) {
              val (id, (t, posOpt)) = p
              val (s6, sym) = s1.freshSym(t, posOpt.get)
              s1 = s6.addClaim(State.Claim.Let.FieldLookup(sym, thiz, id))
              fieldVarInMap = fieldVarInMap + id ~> sym
            }
          case _ =>
        }
        var localInMap = mctx.localInMap
        for (p <- mctx.localMap(typeSubstMap).entries) {
          val (id, (ctx, _, t)) = p
          val (s7, sym) = Logika.idIntro(pos, s1, ctx, id, t, None())
          localInMap = localInMap + id ~> sym
          s1 = s7
        }
        l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
          localInMap = localInMap))))
      }
      val retType = info.sig.returnType.typedOpt.get.subst(typeSubstMap)

      def evalContractCase(assume: B, cs0: State, labelOpt: Option[AST.Exp.LitString], requires: ISZ[AST.Exp],
                           ensures: ISZ[AST.Exp]): ContractCaseResult = {
        val rep = Reporter.create
        var cs1 = cs0
        labelOpt match {
          case Some(label) => cs1 = cs1.addClaim(State.Claim.Label(label.value, label.posOpt.get))
          case _ =>
        }
        var requireSyms = ISZ[State.Value]()
        for (require <- requires if cs1.status) {
          val (cs2, sym): (State, State.Value.Sym) =
            if (assume) {
              val p = logikaComp.evalAssume(F, "Pre-condition", cs1, AST.Util.substExp(require, typeSubstMap), rep)
              val size = p._1.claims.size
              assert(p._1.claims(size - 1) == State.Claim.Prop(T, p._2))
              (p._1(claims = ops.ISZOps(p._1.claims).slice(0, size - 1)), p._2)
            } else {
              logikaComp.evalAssert(F, "Pre-condition", cs1, AST.Util.substExp(require, typeSubstMap), rep)
            }
          cs1 = cs2
          requireSyms = requireSyms :+ sym
          if (!cs1.status) {
            val (cs3, rsym) = cs1.freshSym(AST.Typed.b, pos)
            cs1 = cs3.addClaim(State.Claim.Let.And(rsym, requireSyms))
            return ContractCaseResult(F, cs1, State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
          }
        }
        val (cs4, result) = modVarsResult(cs1, posOpt, retType)
        cs1 = cs4
        for (ensure <- ensures if cs1.status) {
          cs1 = logikaComp.evalAssume(F, "Post-condition", cs1, AST.Util.substExp(ensure, typeSubstMap), rep)._1
          if (!cs1.status) {
            val (cs5, rsym) = cs1.freshSym(AST.Typed.b, pos)
            cs1 = cs5.addClaim(State.Claim.Let.And(rsym, requireSyms))
            return ContractCaseResult(T, cs1, State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
          }
        }
        cs1 = modVarsRewrite(cs1, currentReceiverOpt, receiverOpt)
        val (cs6, rsym) = cs1.freshSym(AST.Typed.b, pos)
        cs1 = cs6.addClaim(State.Claim.Let.And(rsym, requireSyms))
        return ContractCaseResult(T, Logika.conjunctClaimSuffix(cs0, cs1), result, State.Claim.Prop(T, rsym),
          rep.messages)
      }

      contract match {
        case contract: AST.MethodContract.Simple =>
          val ccr = evalContractCase(F, s1, None(), contract.requires, contract.ensures)
          reporter.reports(ccr.messages)
          return (ccr.state, ccr.retVal)
        case contract: AST.MethodContract.Cases =>
          val root = s1
          var isPreOK = F
          var ccrs = ISZ[ContractCaseResult]()
          var okCcrs = ISZ[ContractCaseResult]()
          for (cas <- contract.cases) {
            val ccr = evalContractCase(T, s1,
              if (cas.label.value == "") None() else Some(cas.label), cas.requires, cas.ensures)
            ccrs = ccrs :+ ccr
            isPreOK = isPreOK || ccr.isPreOK
            if (ccr.isOK) {
              okCcrs = okCcrs :+ ccr
            }
            s1 = s1(nextFresh = ccr.state.nextFresh)
          }
          if (!isPreOK) {
            for (ccr <- ccrs) {
              reporter.reports(ccr.messages)
            }
          }
          if (!isPreOK || okCcrs.isEmpty) {
            return (s1(status = F), State.errorValue)
          }
          if (okCcrs.size == 1) {
            val ccr = okCcrs(0)
            s1 = s1(claims = ccr.state.claims :+ ccr.requiresClaim)
            reporter.reports(ccr.messages)
            return (s1, ccr.retVal)
          } else {
            for (ccr <- okCcrs) {
              reporter.reports(ccr.messages)
            }
            var claims = ISZ[State.Claim]()
            for (i <- 0 until root.claims.size) {
              val rootClaim = root.claims(i)
              if (ops.ISZOps(okCcrs).forall((ccr: ContractCaseResult) => ccr.state.claims(i) == rootClaim)) {
                claims = claims :+ rootClaim
              } else {
                claims = claims :+ State.Claim.And(
                  for (ccr <- okCcrs) yield State.Claim.Imply(ISZ(ccr.requiresClaim, ccr.state.claims(i))))
              }
            }
            claims = claims :+ State.Claim.And(
              for (ccr <- okCcrs) yield
                State.Claim.Imply(ISZ(ccr.requiresClaim,
                  State.Claim.And(for (i <- root.claims.size until ccr.state.claims.size) yield ccr.state.claims(i)))))
            claims = claims :+ State.Claim.Or(for (ccr <- okCcrs) yield ccr.requiresClaim)
            s1 = s1(claims = claims)
            if (isUnit) {
              return (s1, okCcrs(0).retVal)
            } else {
              val (s7, sym) = s1.freshSym(retType, pos)
              s1 = s7
              return (s1.addClaim(State.Claim.And(
                for (ccr <- okCcrs) yield State.Claim.Imply(ISZ(ccr.requiresClaim,
                  State.Claim.Let.Eq(sym, ccr.retVal))))), sym)
            }
          }
      }
    }

    def evalTupleExp(tuple: AST.Exp.Tuple): (State, State.Value) = {
      if (tuple.args.size == 1) {
        return evalExp(rtCheck, state, tuple.args(0), reporter)
      }
      var s0 = state
      var args = ISZ[State.Value]()
      for (arg <- tuple.args) {
        val (s1, v) = evalExp(rtCheck, s0, arg, reporter)
        s0 = s1
        if (!s0.status) {
          return (s0, State.errorValue)
        }
        args = args :+ v
      }
      val (s2, sym) = s0.freshSym(tuple.typedOpt.get, tuple.posOpt.get)
      return (s2.addClaim(State.Claim.Let.TupleLit(sym, args)), sym)
    }

    val s0 = state
    e match {
      case lit: AST.Lit => return (s0, evalLit(lit))
      case e: AST.Exp.Ident => return evalIdent(e)
      case e: AST.Exp.Select => return evalSelect(e)
      case e: AST.Exp.Unary => return evalUnaryExp(e)
      case e: AST.Exp.Binary => return evalBinaryExp(e)
      case e: AST.Exp.Tuple => return evalTupleExp(e)
      case e: AST.Exp.Invoke =>
        e.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method =>
            res.mode match {
              case AST.MethodMode.Constructor => return evalConstructor(F, e.receiverOpt, e.ident, Either.Left(e.args), e.attr, res)
              case AST.MethodMode.Select => return evalSeqSelect(e)
              case AST.MethodMode.Method => return evalInvoke(state, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
              case _ =>
            }
          case _ =>
        }
        halt(s"TODO: $e") // TODO
      case e: AST.Exp.InvokeNamed =>
        e.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method =>
            res.mode match {
              case AST.MethodMode.Constructor => return evalConstructor(F, e.receiverOpt, e.ident, Either.Right(e.args), e.attr, res)
              case AST.MethodMode.Copy => return evalConstructor(T, e.receiverOpt, e.ident, Either.Right(e.args), e.attr, res)
              case AST.MethodMode.Method => return evalInvoke(state, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
              case _ =>
            }
          case _ =>
        }
        halt(s"TODO: $e") // TODO
      case e: AST.Exp.Result => return evalResult(e)
      case e: AST.Exp.Input => return evalInput(e)
      case e: AST.Exp.QuantType => return evalQuantType(e)
      case _ => halt(s"TODO: $e") // TODO
    }

  }

  def value2Sym(s0: State, v: State.Value, pos: Position): (State, State.Value.Sym) = {
    v match {
      case v: State.Value.Sym => return (s0, v)
      case _ =>
        val (s2, symV) = s0.freshSym(v.tipe, pos)
        return (s2.addClaim(State.Claim.Let.Eq(symV, v)), symV)
    }
  }

  def evalAssumeH(title: String, s0: State, sym: State.Value.Sym, posOpt: Option[Position],
                  reporter: Reporter): State = {
    val s1 = s0(claims = s0.claims :+ State.Claim.Prop(T, sym))
    val pos = posOpt.get
    val sat = smt2.sat(config.logVc, s"$title at [${pos.beginLine}, ${pos.beginColumn}]", s1.claims, reporter)
    return s1(status = sat)
  }

  def evalAssume(rtCheck: B, title: String, s0: State, cond: AST.Exp, reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = evalExp(rtCheck, s0, cond, reporter)
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssumeH(title, s2, sym, cond.posOpt, reporter), sym)
  }

  def evalAssertH(title: String, s0: State, sym: State.Value.Sym, posOpt: Option[Position],
                  reporter: Reporter): State = {
    val conclusion = State.Claim.Prop(T, sym)
    val pos = posOpt.get
    val valid = smt2.valid(config.logVc, s"$title at [${pos.beginLine}, ${pos.beginColumn}]", s0.claims,
      conclusion, timeoutInMs, reporter)
    if (!valid) {
      error(posOpt, s"Cannot deduce that the ${ops.StringOps(title).firstToLower} holds", reporter)
    }
    return s0(status = valid, claims = s0.claims :+ conclusion)
  }

  def evalAssert(rtCheck: B, title: String, s0: State, cond: AST.Exp, reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = evalExp(rtCheck, s0, cond, reporter)
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssertH(title, s2, sym, cond.posOpt, reporter), sym)
  }

  def evalAssignExp(rtCheck: B, s0: State, ae: AST.AssignExp, reporter: Reporter): (State, State.Value) = {
    ae match {
      case AST.Stmt.Expr(exp) => return evalExp(rtCheck, s0, exp, reporter)
      case _ => halt(s"TODO: $ae") // TODO
    }
  }

  def evalAssignLocalH(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: State.Value.Sym, idPos: Position): State = {
    val s1: State = if (decl) s0 else Logika.rewriteLocal(s0, lcontext, id)
    return s1(claims = s1.claims :+ State.Claim.Let.CurrentId(rhs, lcontext, id, Some(idPos)))
  }

  def evalAssignObjectVarH(s0: State, ids: ISZ[String], rhs: State.Value.Sym, namePos: Position): State = {
    val s2: State = {
      val poss = StateTransformer(Logika.CurrentNamePossCollector(ids)).transformState(ISZ(), s0).ctx
      assert(poss.nonEmpty)
      val (s1, num) = s0.fresh
      val objectVars = HashMap.empty[ISZ[String], (ISZ[Position], Z)] + ids ~> ((poss, num))
      StateTransformer(Logika.CurrentNameRewriter(objectVars)).transformState(T, s1).resultOpt.get
    }
    return s2(claims = s2.claims :+ State.Claim.Let.CurrentName(rhs, ids, Some(namePos)))
  }

  def evalAssignThisVarH(s0: State, id: String, rhs: State.Value, pos: Position): State = {
    val lcontext = context.methodOpt.get.name
    val receiverType = context.methodOpt.get.receiverTypeOpt.get
    val (s1, o) = Logika.idIntro(pos, s0, lcontext, "this", receiverType, None())
    val (s2, newSym) = s1.freshSym(receiverType, pos)
    return evalAssignLocalH(F, s2.addClaim(State.Claim.Def.FieldStore(newSym, o, id, rhs)), lcontext, "this",
      newSym, pos)
  }

  def assignRec(s0: State, lhs: AST.Exp, rhs: State.Value.Sym, reporter: Reporter): State = {
    lhs match {
      case lhs: AST.Exp.Ident =>
        lhs.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar =>
            return evalAssignLocalH(F, s0, res.context, res.id, rhs, lhs.posOpt.get)
          case res: AST.ResolvedInfo.Var =>
            if (res.isInObject) {
              return evalAssignObjectVarH(s0, res.owner :+ res.id, rhs, lhs.posOpt.get)
            } else {
              return evalAssignThisVarH(s0, lhs.id.value, rhs, lhs.posOpt.get)
            }
          case _ => halt(s"Infeasible: $lhs")
        }
      case lhs: AST.Exp.Invoke =>
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        val (s1, a) = evalExp(T, s0, receiver, reporter)
        val (s2, i) = evalExp(T, s1, lhs.args(0), reporter)
        val s3 = checkSeqIndexing(T, s2, a, i, lhs.args(0).posOpt, reporter)
        val (s4, newSym) = s3.freshSym(t, receiverPos)
        return assignRec(s4.addClaim(State.Claim.Def.SeqStore(newSym, a, i, rhs)), receiver,
          newSym, reporter)
      case lhs: AST.Exp.Select =>
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        val (s1, o) = evalExp(T, s0, receiver, reporter)
        val (s2, newSym) = s1.freshSym(t, receiverPos)
        val id = lhs.id.value
        return assignRec(s2.addClaim(State.Claim.Def.FieldStore(newSym, o, id, rhs)),
          receiver, newSym, reporter)
      case _ => halt(s"Infeasible: $lhs")
    }

  }

  def evalPattern(s0: State, v: State.Value, pattern: AST.Pattern, reporter: Reporter): (State, State.Value, Map[String, (State.Value, AST.Typed, Position)]) = {
    val posOpt = pattern.posOpt
    val pos = posOpt.get
    pattern match {
      case pattern: AST.Pattern.Literal =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==", evalLit(pattern.lit), v.tipe)), cond, Map.empty)
      case pattern: AST.Pattern.VarBinding =>
        pattern.tipeOpt match {
          case Some(tipe) =>
            val t = tipe.typedOpt.get
            val (s1, cond) = evalTypeTestH(s0, v, t, tipe.posOpt.get)
            return (s1, cond, Map.empty[String, (State.Value, AST.Typed, Position)] + pattern.id.value ~> ((v, t, pos)))
          case _ =>
            val t = pattern.attr.typedOpt.get
            return (s0, State.Value.B(T, pos),
              Map.empty[String, (State.Value, AST.Typed, Position)] + pattern.id.value ~> ((v, t, pos)))
        }
      case pattern: AST.Pattern.Wildcard =>
        pattern.typeOpt match {
          case Some(tipe) =>
            val (s1, cond) = evalTypeTestH(s0, v, tipe.typedOpt.get, tipe.posOpt.get)
            return (s1, cond, Map.empty)
          case _ =>
            return (s0, State.Value.B(T, pos), Map.empty)
        }
      case pattern: AST.Pattern.Structure =>
        var m = Map.empty[String, (State.Value, AST.Typed, Position)]
        pattern.idOpt match {
          case Some(id) => m = m + id.value ~> ((v, pattern.attr.typedOpt.get, id.attr.posOpt.get))
          case _ =>
        }
        if (pattern.nameOpt.nonEmpty) {
          val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
          if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
            val it = t.args(0).asInstanceOf[AST.Typed.Name]
            val et = t.args(1)
            val hasWildcard = ops.ISZOps(pattern.patterns).exists(
              (p: AST.Pattern) => p.isInstanceOf[AST.Pattern.SeqWildcard])
            val (s1, sizeSym) = s0.freshSym(AST.Typed.z, pos)
            val s2 = s1.addClaim(State.Claim.Let.FieldLookup(sizeSym, v, "size"))
            val (s3, cond) = s2.freshSym(AST.Typed.b, pos)
            val (op, size): (String, Z) =
              if (hasWildcard) (">=", pattern.patterns.size - 1) else ("==", pattern.patterns.size)
            var s4 = s3.addClaim(State.Claim.Let.Binary(cond, sizeSym, op, State.Value.Z(size, pos), AST.Typed.z))
            var conds = ISZ[State.Value](cond)
            val offset: Z = if (it == AST.Typed.z) 0 else th.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ].ast.index
            for (i <- 0 until size) {
              val sub = pattern.patterns(i)
              val subPos = sub.posOpt.get
              val (s5, sym) = s4.freshSym(et, subPos)
              val (s6, cond, subM) = evalPattern(s5.addClaim(
                State.Claim.Let.SeqLookup(sym, v, State.Value.Z(offset + i, subPos))), sym, sub, reporter)
              conds = conds :+ cond
              s4 = s6
              m = m ++ subM.entries
            }
            val (s7, aconds) = s4.freshSym(AST.Typed.b, pos)
            return (s7.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
          } else {
            val (s1, tcond) = evalTypeTestH(s0, v, t, pos)
            val ti = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
            val sm = TypeChecker.buildTypeSubstMap(t.ids, posOpt, ti.ast.typeParams, t.args, reporter).get
            val (s2, o) = s1.freshSym(t, pos)
            var s3 = s2.addClaim(State.Claim.Let.Eq(o, v))
            var conds = ISZ[State.Value](tcond)
            for (p <- ops.ISZOps(ti.extractorTypeMap.entries).zip(pattern.patterns)) {
              val f = p._1._1
              val ft = p._1._2.subst(sm)
              val sub = p._2
              val (s4, sym) = s3.freshSym(ft, sub.posOpt.get)
              s3 = s4.addClaim(State.Claim.Let.FieldLookup(sym, o, f))
              val (s5, cond, subM) = evalPattern(s3, sym, sub, reporter)
              s3 = s5
              conds = conds :+ cond
              m = m ++ subM.entries
            }
            val (s6, aconds) = s3.freshSym(AST.Typed.b, pos)
            return (s6.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
          }
        } else {
          val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Tuple]
          var s1 = s0
          var conds = ISZ[State.Value]()
          for (i <- 1 to pattern.patterns.size) {
            val sub = pattern.patterns(i - 1)
            val (s2, sym) = s1.freshSym(t.args(i - 1), sub.posOpt.get)
            val s3 = s2.addClaim(State.Claim.Let.FieldLookup(sym, v, s"_$i"))
            val (s4, cond, subM) = evalPattern(s3, sym, sub, reporter)
            s1 = s4
            conds = conds :+ cond
            m = m ++ subM.entries
          }
          val (s5, aconds) = s1.freshSym(AST.Typed.b, pos)
          return (s5.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
        }
      case pattern: AST.Pattern.Ref =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        pattern.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var =>
            if (res.owner == AST.Typed.sireumName && res.id == "T" || res.id == "F") {
              return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==",
                State.Value.B(res.id == "T", pos), AST.Typed.b)), cond, Map.empty)
            }
            val t = pattern.attr.typedOpt.get
            val (s2, sym): (State, State.Value.Sym) =
              if (res.isInObject) Logika.nameIntro(pos, s1, res.owner :+ res.id, t, None())
              else evalThisIdH(s1, res.id, t, pos)
            return (s2.addClaim(State.Claim.Let.Binary(cond, v, "==", sym, t)), cond, Map.empty)
          case res: AST.ResolvedInfo.EnumElement =>
            val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
            return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==",
              State.Value.Enum(t, res.owner, res.name, res.ordinal, pos), t)), cond, Map.empty)
          case _ => halt(s"Infeasible: $pattern")
        }
      case pattern: AST.Pattern.LitInterpolate => halt(s"TODO: $pattern") // TODO
      case _: AST.Pattern.SeqWildcard => halt(s"Infeasible")
    }
  }

  def evalMatch(state: State, stmt: AST.Stmt.Match, reporter: Reporter): State = {
    def addPatternVars(s0: State, lcontext: ISZ[String],
                       m: Map[String, (State.Value, AST.Typed, Position)]): (State, ISZ[State.Claim], ISZ[State.Value]) = {
      val ids = m.keys
      val (s1, oldIds) = Logika.rewriteLocals(s0, lcontext, ids)
      var s2 = s1
      var bindings = ISZ[State.Value]()
      for (p <- m.entries) {
        val (id, (v, t, pos)) = p
        val (s3, x) = Logika.idIntro(pos, s2, lcontext, id, t, Some(pos))
        val (s4, sym) = s3.freshSym(AST.Typed.b, pos)
        s2 = s4.addClaim(State.Claim.Let.Binary(sym, x, "==", v, t))
        bindings = bindings :+ sym
      }
      return (s2, oldIds, bindings)
    }

    val (s0, v) = evalExp(T, state, stmt.exp, reporter)
    if (!s0.status) {
      return s0
    }
    var caseSyms = ISZ[(AST.Case, State.Value.Sym, Map[String, (State.Value, AST.Typed, Position)])]()
    val lcontext: ISZ[String] = context.methodOpt match {
      case Some(mctx) => mctx.name
      case _ => ISZ()
    }
    var s1 = s0
    for (c <- stmt.cases) {
      val (s2, pcond, m) = evalPattern(s1, v, c.pattern, reporter)
      val (s3, oldIds, bindings) = addPatternVars(s2, lcontext, m)
      var conds = ISZ(pcond)
      val s6: State = c.condOpt match {
        case Some(cond) =>
          val (s4, ccond) = evalExp(T, s3, cond, reporter)
          if (bindings.nonEmpty) {
            val (s5, icond) = s4.freshSym(AST.Typed.b, c.pattern.posOpt.get)
            conds = conds :+ icond
            s5.addClaim(State.Claim.Let.Imply(icond, bindings :+ ccond))
          } else {
            conds = conds :+ ccond
            s4
          }
        case _ =>
          s3
      }
      val pos = c.pattern.posOpt.get
      val (s7, sym) = s6.freshSym(AST.Typed.b, pos)
      val s8 = s7.addClaim(State.Claim.Let.And(sym, conds))
      val s9 = Logika.rewriteLocals(s8, lcontext, m.keys)._1
      val s10 = s9.addClaims(oldIds)
      s1 = s1(nextFresh = s10.nextFresh).
        addClaim(State.Claim.And(for (i <- s1.claims.size until s10.claims.size) yield s10.claims(i)))
      caseSyms = caseSyms :+ ((c, sym, m))
    };
    {
      val pos = stmt.posOpt.get
      if (smt2.sat(config.logVc, s"pattern match inexhaustiveness at [${pos.beginLine}, ${pos.beginColumn}]",
        s1.claims :+ State.Claim.And(for (p <- caseSyms) yield State.Claim.Prop(F, p._2)), reporter)) {
        error(stmt.posOpt, "Inexhaustive pattern match", reporter)
        return s1(status = F)
      }
    }
    var leafClaims = ISZ[State.Claim]()
    var possibleCases = F
    for (i <- 0 until caseSyms.size) {
      val (c, sym, m) = caseSyms(i)
      val cond = State.Claim.And(
        (for (j <- 0 until i) yield State.Claim.Prop(F, caseSyms(j)._2).asInstanceOf[State.Claim]) :+
          State.Claim.Prop(T, sym))
      val posOpt = c.pattern.posOpt
      val pos = posOpt.get
      val s10 = s1.addClaim(cond)
      if (smt2.sat(config.logVc, s"match case pattern at [${pos.beginLine}, ${pos.beginColumn}]", s10.claims,
        reporter)) {
        possibleCases = T
        val (s11, _, bindings) = addPatternVars(s10, lcontext, m)
        val s12 = evalBody(s11.addClaim(State.Claim.And(for (b <- bindings) yield
          State.Claim.Prop(T, b.asInstanceOf[State.Value.Sym]))), c.body, reporter)
        s1 = s1(nextFresh = s12.nextFresh)
        if (s12.status) {
          leafClaims = leafClaims :+ State.Claim.Imply(ISZ(cond, State.Claim.And(
            ops.ISZOps(s12.claims).slice(s1.claims.size + 1, s12.claims.size)
          )))
        }
      } else {
        error(posOpt, "Impossible pattern matching case", reporter)
      }
    }
    if (leafClaims.isEmpty) {
      if (!possibleCases) {
        error(stmt.posOpt, "Impossible pattern matching cases", reporter)
      }
      return s1(status = F)
    }
    return s1.addClaim(State.Claim.And(leafClaims))
  }

  def evalStmt(state: State, stmt: AST.Stmt, reporter: Reporter): State = {
    if (!state.status) {
      return state
    }

    def evalAssignLocal(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: AST.AssignExp, idPos: Position): State = {
      val (s1, init) = evalAssignExp(T, s0, rhs, reporter)
      if (!s1.status) {
        return s1
      }
      val (s2, sym) = value2Sym(s1, init, rhs.asStmt.posOpt.get)
      return Logika.conjunctClaimSuffix(s0, evalAssignLocalH(decl, s2, lcontext, id, sym, idPos))
    }

    def evalAssign(s0: State, assignStmt: AST.Stmt.Assign): State = {

      val (s1, init) = evalAssignExp(T, s0, assignStmt.rhs, reporter)
      if (!s1.status) {
        return s1
      }
      val (s2, sym) = value2Sym(s1, init, assignStmt.rhs.asStmt.posOpt.get)
      return Logika.conjunctClaimSuffix(s0, assignRec(s2, assignStmt.lhs, sym, reporter))
    }

    def evalIf(s0: State, ifStmt: AST.Stmt.If): State = {
      val (s1, v) = evalExp(T, s0, ifStmt.cond, reporter)
      val pos = ifStmt.cond.posOpt.get
      val (s1c, cond) = value2Sym(s1, v, pos)
      if (!s1c.status) {
        return s1c
      }
      val s2 = Logika.conjunctClaimSuffix(s0, s1c)
      val prop = State.Claim.Prop(T, cond)
      val thenClaims = s2.claims :+ prop
      var thenSat = smt2.sat(config.logVc, s"if-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
        thenClaims, reporter)
      val s4: State = if (thenSat) {
        val s3 = evalBody(s2(claims = thenClaims), ifStmt.thenBody, reporter)
        thenSat = s3.status
        s3
      } else {
        s2(claims = thenClaims)
      }
      val negProp = State.Claim.Prop(F, cond)
      val elseClaims = s2.claims :+ negProp
      var elseSat = smt2.sat(config.logVc, s"if-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
        elseClaims, reporter)
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
      val s0w = checkExps(F, "Loop invariant", " at the beginning of while-loop", s0,
        whileStmt.invariants, reporter)
      if (!s0w.status) {
        return s0w
      }
      val s1 = Logika.conjunctClaimSuffix(s0, s0w)
      val modLocalVars = whileStmt.modifiedLocalVars
      if (whileStmt.modifiedObjectVars.nonEmpty || whileStmt.modifiedRecordVars.nonEmpty) {
        halt("TODO: rewrite Vars/fields as well") // TODO
      }
      val s0R: State = {
        var srw = Logika.rewriteLocalVars(s0(nextFresh = s1.nextFresh), modLocalVars.keys)
        for (p <- modLocalVars.entries) {
          val (res, (tipe, pos)) = p
          val (srw1, sym) = srw.freshSym(tipe, pos)
          srw = srw1(claims = srw1.claims :+ State.Claim.Let.CurrentId(sym, res.context, res.id, Some(pos)))
        }
        srw
      }
      val s2 = State(T, s0R.claims ++ (for (i <- s0.claims.size until s1.claims.size) yield s1.claims(i)), s0R.nextFresh)
      val (s3, v) = evalExp(T, s2, whileStmt.cond, reporter)
      val pos = whileStmt.cond.posOpt.get
      val (s4, cond) = value2Sym(s3, v, pos)
      val prop = State.Claim.Prop(T, cond)
      val thenClaims = s4.claims :+ prop
      var thenSat = smt2.sat(config.logVc, s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
        thenClaims, reporter)
      val nextFresh: Z = if (thenSat) {
        val s5 = evalStmts(s4(claims = thenClaims), whileStmt.body.stmts, reporter)
        thenSat = s5.status
        if (thenSat) {
          val s6 = checkExps(F, "Loop invariant", " at the end of while-loop",
            s5, whileStmt.invariants, reporter)
          s6.nextFresh
        } else {
          s5.nextFresh
        }
      } else {
        s4.nextFresh
      }
      val negProp = State.Claim.Prop(F, cond)
      val elseClaims = s4.claims :+ negProp
      val elseSat = smt2.sat(config.logVc, s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
        elseClaims, reporter)
      return State(status = elseSat, claims = elseClaims, nextFresh = nextFresh)
    }

    @pure def loopBound(ids: ISZ[String]): Z = {
      return config.loopBounds.get(ids).getOrElse(config.defaultLoopBound)
    }

    def evalWhileUnroll(s0: State, whileStmt: AST.Stmt.While): State = {
      val loopId: ISZ[String] = whileStmt.context

      def whileRec(current: State, numLoops: Z): State = {
        val s1 = checkExps(F, "Loop invariant", " at the beginning of while-loop", current,
          whileStmt.invariants, reporter)
        if (!s1.status) {
          return s1
        }
        val (s2, v) = evalExp(T, s1, whileStmt.cond, reporter)
        val pos = whileStmt.cond.posOpt.get
        val (s2w, cond) = value2Sym(s2, v, pos)
        val s3 = Logika.conjunctClaimSuffix(current, s2w)
        val prop = State.Claim.Prop(T, cond)
        val thenClaims = s3.claims :+ prop
        var thenSat = smt2.sat(config.logVc, s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
          thenClaims, reporter)
        val s6: State = if (thenSat) {
          val s4 = evalStmts(s3(claims = thenClaims), whileStmt.body.stmts, reporter)
          thenSat = s4.status
          if (thenSat) {
            val bound = loopBound(loopId)
            if (bound <= 0 || numLoops + 1 < loopBound(loopId)) {
              val s5 = whileRec(s4, numLoops + 1)
              s5
            } else {
              if (bound > 0) {
                warn(whileStmt.cond.posOpt, s"Under-approximation due to loop unrolling capped with bound $bound",
                  reporter)
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
        val negProp = State.Claim.Prop(F, cond)
        val elseClaims = s3.claims :+ negProp
        val elseSat = smt2.sat(config.logVc, s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
          elseClaims, reporter)
        (thenSat, elseSat) match {
          case (T, T) => return mergeStates(s3, cond, s6, s3, s6.nextFresh)
          case (T, F) => return s6(status = s6.status && !reporter.hasError)
          case (F, T) => return s3(status = s3.status && !reporter.hasError, nextFresh = s6.nextFresh)
          case _ =>
            val s7 = mergeStates(s3, cond, s6, s3, s6.nextFresh)
            return s7(status = F)
        }
      }

      return whileRec(s0, 0)
    }

    def evalReturn(s0: State, returnStmt: AST.Stmt.Return): State = {
      returnStmt.expOpt match {
        case Some(exp) =>
          val (s1, v) = evalExp(T, s0, exp, reporter)
          val pos = exp.posOpt.get
          val (s2, sym) = value2Sym(s1, v, pos)
          return Logika.conjunctClaimSuffix(s0,
            s2.addClaim(State.Claim.Let.CurrentId(sym, context.methodOpt.get.name, "Res", Some(pos))))
        case _ => return state
      }
    }

    def evalBlock(s0: State, block: AST.Stmt.Block): State = {
      return evalBody(s0, block.body, reporter)
    }

    def evalSpecBlock(s0: State, block: AST.Stmt.SpecBlock): State = {
      return evalBlock(s0, block.block)
    }

    stmt match {
      case AST.Stmt.Expr(e: AST.Exp.Invoke) =>
        logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
        e.attr.resOpt.get match {
          case AST.ResolvedInfo.BuiltIn(kind) =>
            kind match {
              case AST.ResolvedInfo.BuiltIn.Kind.Assert =>
                return Logika.conjunctClaimSuffix(state, evalAssert(T, "Assertion", state, e.args(0), reporter)._1)
              case AST.ResolvedInfo.BuiltIn.Kind.AssertMsg =>
                return Logika.conjunctClaimSuffix(state, evalAssert(T, "Assertion", state, e.args(0), reporter)._1)
              case AST.ResolvedInfo.BuiltIn.Kind.Assume =>
                return Logika.conjunctClaimSuffix(state, evalAssume(T, "Assumption", state, e.args(0), reporter)._1)
              case AST.ResolvedInfo.BuiltIn.Kind.AssumeMsg =>
                return Logika.conjunctClaimSuffix(state, evalAssume(T, "Assumption", state, e.args(0), reporter)._1)
              case _ =>
                halt(s"TODO: $stmt") // TODO
            }
          case _ => return Logika.conjunctClaimSuffix(state, evalExp(T, state, e, reporter)._1)
        }
      case stmt: AST.Stmt.Var if stmt.initOpt.nonEmpty =>
        logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
        stmt.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar =>
            return evalAssignLocal(T, state, res.context, res.id, stmt.initOpt.get, stmt.id.attr.posOpt.get)
          case _ => halt(s"TODO: $stmt") // TODO
        }
      case stmt: AST.Stmt.Assign =>
        logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
        return evalAssign(state, stmt)
      case stmt: AST.Stmt.If =>
        logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
        return evalIf(state, stmt)
      case stmt: AST.Stmt.While =>
        logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
        return if (stmt.modifies.nonEmpty) evalWhile(state, stmt) else evalWhileUnroll(state, stmt)
      case stmt: AST.Stmt.Return =>
        logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
        return evalReturn(state, stmt)
      case stmt: AST.Stmt.Block => return evalBlock(state, stmt)
      case stmt: AST.Stmt.SpecBlock => return evalSpecBlock(state, stmt)
      case stmt: AST.Stmt.Match => return evalMatch(state, stmt, reporter)
      case _: AST.Stmt.Object => return state
      case _: AST.Stmt.Import => return state
      case _: AST.Stmt.Method => return state
      case _: AST.Stmt.SpecMethod => return state
      case stmt: AST.Stmt.Var if stmt.isSpec => return state
      case _: AST.Stmt.SpecVar => return state
      case _: AST.Stmt.Enum => return state
      case _: AST.Stmt.Adt => return state
      case _: AST.Stmt.Sig => return state
      case _ =>
        halt(s"TODO: $stmt") // TODO
    }

  }

  def logPc(enabled: B, raw: B, state: State, reporter: Reporter, posOpt: Option[Position]): Unit = {
    if (enabled || raw) {
      val sts: ISZ[ST] =
        if (raw) State.Claim.claimsRawSTs(state.claims)
        else State.Claim.claimsSTs(state.claims, State.Claim.Defs.empty)
      if (sts.isEmpty) {
        reporter.info(posOpt, Logika.kind, "Path conditions = {}")
      } else {
        reporter.info(posOpt, Logika.kind,
          st"""Path conditions = {
              |      ${(sts, ",\n")}
              |    }""".
            render
        )
      }
    }
  }

  def evalTypeTestH(s0: State, v: State.Value, t: AST.Typed, pos: Position): (State, State.Value) = {
    t match {
      case t: AST.Typed.Name if t.ids != AST.Typed.isName && t.ids != AST.Typed.msName =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        th.typeMap.get(t.ids).get match {
          case ti: TypeInfo.Adt => return (s1.addClaim(State.Claim.Let.TypeTest(cond, !ti.ast.isRoot, v, t)), cond)
          case _: TypeInfo.Sig => return (s1.addClaim(State.Claim.Let.TypeTest(cond, F, v, t)), cond)
          case _ =>
        }
      case _ =>
    }
    assert(v.tipe == t)
    return (s0, State.Value.B(T, pos))
  }

  def checkExp(rtCheck: B, title: String, titleSuffix: String, s0: State, exp: AST.Exp, reporter: Reporter): State = {
    val (s1, v) = evalExp(rtCheck, s0, exp, reporter)
    val pos = exp.posOpt.get
    val (s2, sym) = value2Sym(s1, v, pos)
    val prop = State.Claim.Prop(T, sym)
    val valid: B = {
      val vld = smt2.valid(config.logVc, s"$title at [${pos.beginLine}, ${pos.beginColumn}]", s2.claims, prop,
        timeoutInMs, reporter)
      if (!vld) {
        error(exp.posOpt, s"Cannot deduce the ${ops.StringOps(title).firstToLower} holds$titleSuffix", reporter)
      }
      vld
    }
    return s2(status = valid, claims = s2.claims :+ prop)
  }

  def checkExps(rtCheck: B, title: String, titleSuffix: String, s0: State, exps: ISZ[AST.Exp], reporter: Reporter): State = {
    var current = s0
    for (exp <- exps) {
      if (!current.status) {
        return current
      }
      current = checkExp(rtCheck, title, titleSuffix, current, exp, reporter)
    }
    return current
  }

  def mergeStates(s0: State, cond: State.Value.Sym, sT: State, sF: State, nextFresh: Z): State = {
    @pure def mergeClaimPrefix(tClaim: State.Claim, fClaim: State.Claim): State.Claim = {
      return if (tClaim == fClaim) tClaim else State.Claim.If(cond, ISZ(tClaim), ISZ(fClaim))
    }

    val size = s0.claims.size
    val prefixClaims: ISZ[State.Claim] =
      for (i <- 0 until size) yield mergeClaimPrefix(sT.claims(i), sF.claims(i))
    return State(s0.status, prefixClaims :+
      State.Claim.If(cond, ops.ISZOps(sT.claims).drop(size + 1),
        ops.ISZOps(sF.claims).drop(size + 1)), nextFresh)
  }

  def evalStmts(state: State, stmts: ISZ[AST.Stmt], reporter: Reporter): State = {
    var current = state

    for (stmt <- stmts if current.status) {
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
    return Logika.rewriteLocalVars(s1, body.undecls)
  }

  def error(posOpt: Option[Position], msg: String, reporter: Reporter): Unit = {
    if (context.caseLabels.nonEmpty) {
      reporter.error(posOpt, Logika.kind, st"[${(for (l <- context.caseLabels) yield l.value, "; ")}] $msg".render)
    } else {
      reporter.error(posOpt, Logika.kind, msg)
    }
  }

  def warn(posOpt: Option[Position], msg: String, reporter: Reporter): Unit = {
    if (context.caseLabels.nonEmpty) {
      reporter.warn(posOpt, Logika.kind, st"[${(for (l <- context.caseLabels) yield l.value, "; ")}] $msg".render)
    } else {
      reporter.warn(posOpt, Logika.kind, msg)
    }
  }

}
