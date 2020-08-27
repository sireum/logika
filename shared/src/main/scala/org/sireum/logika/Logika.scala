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
import org.sireum.message.{Message, Position}
import StateTransformer.{PrePost, PreResult}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.Logika.{ContractCaseResult, InvokeMethodInfo}

object Logika {

  @enum object Split {
    'Default
    'Enabled
    'Disabled
  }

  @msig trait Reporter extends message.Reporter {
    def state(posOpt: Option[Position], s: State): Unit

    def query(pos: Position, r: Smt2Query.Result): Unit

    def halted(posOpt: Option[Position], s: State): Unit
  }

  @record class ReporterImpl(var _messages: ISZ[Message]) extends Reporter {
    var _ignore: B = F

    override def state(posOpt: Option[Position], s: State): Unit = {
    }

    override def query(pos: Position, r: Smt2Query.Result): Unit = {
    }

    override def halted(posOpt: Option[Position], s: State): Unit = {
    }

    override def messages: ISZ[Message] = {
      return _messages
    }

    override def ignore: B = {
      return _ignore
    }

    override def setIgnore(newIgnore: B): Unit = {
      _ignore = newIgnore
    }

    override def setMessages(newMessages: ISZ[Message]): Unit = {
      _messages = newMessages
    }
  }

  object Reporter {
    def create: Reporter = {
      return ReporterImpl(ISZ())
    }
  }

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

  object Context {
    @strictpure def empty: Context = Context(ISZ(), None(), ISZ())
  }

  @datatype class Context(typeParams: ISZ[AST.TypeParam],
                          methodOpt: Option[MethodContext],
                          caseLabels: ISZ[AST.Exp.LitString]) {
    @pure def methodName: ISZ[String] = {
      methodOpt match {
        case Some(m) => return m.name
        case _ => return ISZ()
      }
    }
  }

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

  @datatype class InvokeMethodInfo(sig: AST.MethodSig,
                                   contract: AST.MethodContract,
                                   res: AST.ResolvedInfo.Method,
                                   strictPureBodyOpt: Option[AST.AssignExp])

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
          val logika = Logika(th, config, Context.empty)
          for (state <- logika.evalStmts(Split.Default, smt2, None(), T, State.create, p.body.stmts, reporter) if state.status) {
            if (p.body.stmts.nonEmpty) {
              val lastPos = p.body.stmts(p.body.stmts.size - 1).posOpt.get
              logika.logPc(config.logPc, config.logRawPc, state, reporter, Some(Logika.afterPos(lastPos)))
            }
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

  def logikaMethod(th: TypeHierarchy, config: Config, name: ISZ[String], receiverTypeOpt: Option[AST.Typed],
                   sig: AST.MethodSig, posOpt: Option[Position], reads: ISZ[AST.Exp.Ident], modifies: ISZ[AST.Exp.Ident],
                   caseLabels: ISZ[AST.Exp.LitString]): Logika = {
    val mctx = MethodContext(name, receiverTypeOpt, sig, reads, modifies, HashMap.empty, HashMap.empty, HashMap.empty, posOpt)
    val ctx = Context.empty(methodOpt = Some(mctx), caseLabels = caseLabels)
    return Logika(th, config, ctx)
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
        val l = logikaMethod(th, config, mname, receiverTypeOpt, method.sig, method.posOpt, reads, modifies,
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
        state = logika.evalAssume(smt2, F, "Precondition", state, r, reporter)._1
      }
      val stmts = method.bodyOpt.get.stmts
      for (s <- logika.evalStmts(Split.Default, smt2, None(), T, state, stmts, reporter)) {
        var s2 = s
        for (e <- ensures if s2.status) {
          s2 = logika.evalAssert(smt2, F, "Postcondition", s2, e, reporter)._1
        }
        if (stmts.nonEmpty && s2.status) {
          logika.logPc(config.logPc, config.logRawPc, s2, reporter,
            Some(Logika.afterPos(stmts(stmts.size - 1).posOpt.get)))
        }
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
    return (s0.addClaim(State.Claim.Let.CurrentId(F, sym, idContext, id, idPosOpt)), sym)
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

  def constructAssume(cond: AST.Exp, posOpt: Option[Position]): AST.Stmt = {
    val assumeResAttr = AST.ResolvedAttr(
      posOpt = posOpt,
      resOpt = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.Assume)),
      typedOpt = Some(AST.Typed.Fun(F, F, ISZ(AST.Typed.b), AST.Typed.unit))
    )
    AST.Stmt.Expr(AST.Exp.Invoke(
      None(), AST.Exp.Ident(AST.Id("assume", AST.Attr(posOpt)), assumeResAttr), ISZ(), ISZ(cond),
      AST.ResolvedAttr(assumeResAttr.posOpt, assumeResAttr.resOpt, AST.Typed.unitOpt)
    ), AST.TypedAttr(posOpt, AST.Typed.unitOpt))
  }

  @strictpure def afterPos(pos: Position): Position = message.FlatPos(pos.uriOpt,
    conversions.Z.toU32(pos.endLine + 1),
    conversions.Z.toU32(1),
    conversions.Z.toU32(pos.endLine + 1),
    conversions.Z.toU32(2),
    conversions.Z.toU32(pos.offset),
    conversions.Z.toU32(1))
}

import Logika.Reporter
import Logika.Split

@datatype class Logika(th: lang.tipe.TypeHierarchy,
                       config: Config,
                       context: Logika.Context) {

  val timeoutInMs: Z = config.smt2TimeoutInSeconds * 1000

  @pure def isBasic(smt2: Smt2, t: AST.Typed): B = {
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

  def checkSeqIndexing(smt2: Smt2, rtCheck: B, s0: State, seq: State.Value, i: State.Value, posOpt: Option[Position],
                       reporter: Reporter): State = {
    if (!rtCheck) {
      return s0
    }
    val pos = posOpt.get
    val (s1, v) = s0.freshSym(AST.Typed.b, pos)
    val s2 = s1.addClaim(State.Claim.Let.SeqInBound(v, seq, i))
    val claim = State.Claim.Prop(T, v)
    val r = smt2.valid(config.logVc, config.logVcDirOpt, s"Implicit Indexing Assertion at [${pos.beginLine}, ${pos.beginColumn}]",
      pos, s2.claims, claim, timeoutInMs, reporter)
    r.kind match {
      case Smt2Query.Result.Kind.Unsat => return s2.addClaim(claim)
      case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Possibly out of bound sequence indexing", reporter)
      case Smt2Query.Result.Kind.Unknown => error(Some(pos), s"Could not deduce that the sequence indexing is in bound", reporter)
      case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the sequence indexing is in bound", reporter)
      case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the sequence indexing is in bound", reporter)
    }
    return s2(status = F)
  }

  def strictPureMethod(smt2: Smt2, state: State, imi: InvokeMethodInfo, substMap: HashMap[String, AST.Typed],
                       reporter: Reporter): (State, State.ProofFun) = {
    val funType = imi.res.tpeOpt.get.subst(substMap)
    val pf: State.ProofFun = {
      val res = imi.res
      val receiverTypeOpt: Option[AST.Typed] = if (res.isInObject) {
        None()
      } else {
        th.typeMap.get(res.owner).get match {
          case ti: TypeInfo.Sig => Some(ti.tpe.subst(substMap))
          case ti: TypeInfo.Adt => Some(ti.tpe.subst(substMap))
          case _ => halt("Infeasible")
        }
      }
      State.ProofFun(receiverTypeOpt, res.owner, res.id, res.paramNames, funType.args, funType.ret)
    }
    if (smt2.strictPureMethods.contains(pf)) {
      return (state, pf)
    } else {
      smt2.strictPureMethodsUp(smt2.strictPureMethods + pf ~> ((st"", st"")))
      val b = imi.strictPureBodyOpt.get
      val (res, prefix, svs): (State.Value.Sym, Z, ISZ[(State, State.Value)]) = {
        val body: AST.AssignExp = if (substMap.isEmpty) {
          b
        } else {
          AST.Util.TypeSubstitutor(substMap).transformAssignExp(b).getOrElse(b)
        }
        val posOpt = body.asStmt.posOpt
        val logika: Logika = Logika.logikaMethod(th, config, pf.context :+ pf.id, pf.receiverTypeOpt, imi.sig,
          posOpt, ISZ(), ISZ(), ISZ())
        val s0 = state(claims = ISZ())
        val (s1, r) = Logika.idIntro(posOpt.get, s0, pf.context, "Res", funType.ret, posOpt)
        (r, s0.claims.size, logika.evalAssignExpValue(Split.Enabled, smt2, funType.ret, T, s1, body, reporter))
      }

      smt2.addStrictPureMethod(b.asStmt.posOpt.get, pf, svs, res, prefix)

      val s1 = state(nextFresh = maxStateValuesNextFresh(svs))
      val posOpt = b.asStmt.posOpt
      if (!smt2.sat(config.logVc, config.logVcDirOpt, "Satisfiability of proof function", posOpt.get, s1.claims, reporter)) {
        reporter.error(posOpt, Logika.kind, "Unsatisfiable proof function derived from @strictpure method")
      }
      return (s1, pf)
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

  def text2SubZVal(ti: TypeInfo.SubZ, text: String, pos: Position): State.Value = {
    val t = ti.typedOpt.get.asInstanceOf[AST.Typed.Name]
    (ti.ast.isBitVector, ti.ast.bitWidth) match {
      case (T, 8) => return State.Value.S8(S8(text).get, t, pos)
      case (T, 16) => return State.Value.S16(S16(text).get, t, pos)
      case (T, 32) => return State.Value.S32(S32(text).get, t, pos)
      case (T, 64) => return State.Value.S64(S64(text).get, t, pos)
      case (F, 8) => return State.Value.U8(U8(text).get, t, pos)
      case (F, 16) => return State.Value.U16(U16(text).get, t, pos)
      case (F, 32) => return State.Value.U32(U32(text).get, t, pos)
      case (F, 64) => return State.Value.U64(U64(text).get, t, pos)
      case (_, _) => return State.Value.Range(org.sireum.Z(text).get, t, pos)
    }
  }

  def z2SubZVal(ti: TypeInfo.SubZ, n: Z, pos: Position): State.Value = {
    val t = ti.typedOpt.get.asInstanceOf[AST.Typed.Name]
    (ti.ast.isBitVector, ti.ast.bitWidth) match {
      case (T, 8) => return State.Value.S8(conversions.Z.toS8(n), t, pos)
      case (T, 16) => return State.Value.S16(conversions.Z.toS16(n), t, pos)
      case (T, 32) => return State.Value.S32(conversions.Z.toS32(n), t, pos)
      case (T, 64) => return State.Value.S64(conversions.Z.toS64(n), t, pos)
      case (F, 8) => return State.Value.U8(conversions.Z.toU8(n), t, pos)
      case (F, 16) => return State.Value.U16(conversions.Z.toU16(n), t, pos)
      case (F, 32) => return State.Value.U32(conversions.Z.toU32(n), t, pos)
      case (F, 64) => return State.Value.U64(conversions.Z.toU64(n), t, pos)
      case (_, _) => return State.Value.Range(n, t, pos)
    }
  }

  def evalInterpolate(lit: AST.Exp.StringInterpolate): State.Value = {
    lit.prefix match {
      case string"z" => return State.Value.Z(org.sireum.Z(lit.lits(0).value).get, lit.posOpt.get)
      case string"r" => return State.Value.R(org.sireum.R(lit.lits(0).value).get, lit.posOpt.get)
      case string"c" => return State.Value.C(conversions.String.toCis(lit.lits(0).value)(0), lit.posOpt.get)
      case string"f32" => return State.Value.F32(org.sireum.F32(lit.lits(0).value).get, lit.posOpt.get)
      case string"f64" => return State.Value.F64(org.sireum.F64(lit.lits(0).value).get, lit.posOpt.get)
      case _ =>
        val t = lit.typedOpt.get.asInstanceOf[AST.Typed.Name].ids
        th.typeMap.get(t).get match {
          case ti: TypeInfo.SubZ => return text2SubZVal(ti, lit.lits(0).value, lit.posOpt.get)
          case _ =>
        }
        halt(s"TODO: $lit")
    }
  }

  def evalThisIdH(state: State, id: String, t: AST.Typed, pos: Position): (State, State.Value.Sym) = {
    val mc = context.methodOpt.get
    val (s0, receiver) = Logika.idIntro(pos, state, mc.name, "this", mc.receiverTypeOpt.get, None())
    val (s1, r) = s0.freshSym(t, pos)
    return (s1.addClaim(State.Claim.Let.FieldLookup(r, receiver, id)), r)
  }

  def evalExps(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, numOfExps: Z, fe: Z => AST.Exp @pure,
               reporter: Reporter): ISZ[(State, ISZ[State.Value])] = {
    var done = ISZ[(State, ISZ[State.Value])]()
    var currents = ISZ((state, ISZ[State.Value]()))
    for (i <- 0 until numOfExps) {
      val e = fe(i)
      val cs = currents
      currents = ISZ()
      var nextFresh: Z = state.nextFresh
      for (current <- cs) {
        val (s0, vs) = current
        for (p <- evalExp(split, smt2, rtCheck, s0, e, reporter)) {
          val (s1, v) = p
          if (s1.status) {
            currents = currents :+ ((s1, vs :+ v))
            if (nextFresh < s1.nextFresh) {
              nextFresh = s1.nextFresh
            }
          } else {
            done = done :+ ((s1, vs :+ v))
          }
        }
      }
      currents = for (p <- currents) yield (p._1(nextFresh = nextFresh), p._2)
    }
    return currents ++ done
  }

  def evalArgs(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, numOfArgs: Z,
               eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]], reporter: Reporter): ISZ[(State, ISZ[Option[State.Value]])] = {
    eargs match {
      case Either.Left(es) =>
        @strictpure def fe(i: Z): AST.Exp = es(i)
        return for (p <- evalExps(split, smt2, rtCheck, state, es.size, fe _, reporter)) yield
          ((p._1, for (v <- p._2) yield Some(v)))
      case Either.Right(nargs) =>
        @strictpure def feM(i: Z): AST.Exp = nargs(i).arg
        var r = ISZ[(State, ISZ[Option[State.Value]])]()
        for (p <- evalExps(split, smt2, rtCheck, state, nargs.size, feM _, reporter)) {
          val (s0, args) = p
          var m = HashMap.empty[Z, Option[State.Value]]
          for (i <- 0 until args.size) {
            m = m + nargs(i).index ~> Some(args(i))
          }
          r = r :+ ((s0, for (i <- 0 until numOfArgs) yield m.get(i).getOrElse(None())))
        }
        return r
    }
  }

  def evalExp(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, e: AST.Exp, reporter: Reporter): ISZ[(State, State.Value)] = {
    if (!state.status) {
      return ISZ((state, State.errorValue))
    }

    def checkRange(s0: State, value: State.Value, pos: Position): State = {
      val t = value.tipe
      t match {
        case t: AST.Typed.Name =>
          th.typeMap.get(t.ids).get match {
            case ti: TypeInfo.SubZ if !ti.ast.isBitVector =>
              var s1 = s0
              if (ti.ast.hasMin) {
                val (s2, sym) = s1.freshSym(AST.Typed.b, pos)
                val s3 = s2.addClaim(State.Claim.Let.Binary(sym, z2SubZVal(ti, ti.ast.min, pos), AST.Exp.BinaryOp.Le, value, t))
                s1 = evalAssertH(smt2, s"Min range check for $t", s3, sym, e.posOpt, reporter)
              }
              if (s1.status && ti.ast.hasMax) {
                val (s4, sym) = s1.freshSym(AST.Typed.b, pos)
                val s5 = s4.addClaim(State.Claim.Let.Binary(sym, value, AST.Exp.BinaryOp.Le, z2SubZVal(ti, ti.ast.max, pos), t))
                s1 = evalAssertH(smt2, s"Max range check for $t", s5, sym, e.posOpt, reporter)
              }
              return s1
            case _ =>
          }
        case _ =>
      }
      return s0
    }

    def evalIdentH(s0: State, res: AST.ResolvedInfo, t: AST.Typed, pos: Position): (State, State.Value) = {
      res match {
        case AST.ResolvedInfo.Var(T, F, T, AST.Typed.sireumName, id) if id == "T" || id == "F" =>
          return (s0, if (id == "T") State.Value.B(T, pos) else State.Value.B(F, pos))
        case res: AST.ResolvedInfo.LocalVar =>
          val (s1, r) = Logika.idIntro(pos, s0, res.context, res.id, t, None())
          return (s1, r)
        case res: AST.ResolvedInfo.Var =>
          if (res.isInObject) {
            val (s1, r) = Logika.nameIntro(pos, s0, res.owner :+ res.id, t, None())
            return (s1, r)
          } else {
            val (s1, r) = evalThisIdH(s0, res.id, t, pos)
            return (s1, r)
          }
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalIdent(exp: AST.Exp.Ident): (State, State.Value) = {
      return evalIdentH(state, exp.attr.resOpt.get, exp.attr.typedOpt.get, exp.posOpt.get)
    }

    def evalUnaryExp(exp: AST.Exp.Unary): ISZ[(State, State.Value)] = {

      val s0 = state

      exp.attr.resOpt.get match {
        case AST.ResolvedInfo.BuiltIn(kind) if isBasic(smt2, exp.typedOpt.get) =>
          def evalUnaryExpH(p: (State, State.Value)): (State, State.Value) = {
            val (s1, v) = p
            if (!s1.status) {
              return (s1, State.errorValue)
            }
            kind match {
              case AST.ResolvedInfo.BuiltIn.Kind.UnaryPlus => return (s1, v)
              case _ =>
                val pos = exp.posOpt.get
                val (s2, sym) = s1.freshSym(v.tipe, pos)
                val s3 = s2(claims = s2.claims :+ State.Claim.Let.Unary(sym, exp.opString, v))
                return (checkRange(s3, sym, pos), sym)
            }
          }
          return for (p <- evalExp(split, smt2, rtCheck, s0, exp.exp, reporter)) yield evalUnaryExpH(p)
        case _ =>
          halt(s"TODO: $exp") // TODO
      }
    }

    def evalBinaryExp(exp: AST.Exp.Binary): ISZ[(State, State.Value)] = {
      @pure def isCond(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
          case _ => return F
        }
        return T
      }

      @pure def isSeq(m: AST.ResolvedInfo.Method): B = {
        m.id match {
          case AST.Exp.BinaryOp.Append =>
          case AST.Exp.BinaryOp.AppendAll =>
          case AST.Exp.BinaryOp.Prepend =>
          case AST.Exp.BinaryOp.RemoveAll => halt(s"TODO: $m")
          case _ => return F
        }
        return m.owner == AST.Typed.isName || m.owner == AST.Typed.msName
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
        val r = smt2.valid(config.logVc, config.logVcDirOpt,
          s"non-zero second operand of '$op' at [${pos.beginLine}, ${pos.beginColumn}]",
          pos, s0.claims :+ claim, State.Claim.Prop(T, sym), timeoutInMs, reporter)
        r.kind match {
          case Smt2Query.Result.Kind.Unsat => return s1.addClaim(claim)
          case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Possibly zero second operand for ${exp.op}", reporter)
          case Smt2Query.Result.Kind.Unknown => error(Some(pos), s"Could not deduce non-zero second operand for ${exp.op}", reporter)
          case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing non-zero second operand for ${exp.op}", reporter)
          case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing non-zero second operand for ${exp.op}", reporter)
        }
        return s1(status = F)
      }

      def evalBasic(s0: State, kind: AST.ResolvedInfo.BuiltIn.Kind.Type, v1: State.Value): ISZ[(State, State.Value)] = {
        def evalBasicH(p: (State, State.Value)): (State, State.Value) = {
          val (s1, v2) = p
          val s2: State = if (reqNonZeroCheck(kind)) {
            checkNonZero(s1, exp.op, v2, exp.right.posOpt.get)
          } else {
            s1
          }
          if (!s2.status) {
            return (s2, State.errorValue)
          }
          val rTipe = e.typedOpt.get
          val pos = e.posOpt.get
          val (s3, rExp) = s2.freshSym(rTipe, pos)
          val s4 = s3.addClaim(State.Claim.Let.Binary(rExp, v1, exp.op, v2, v1.tipe))
          return (checkRange(s4, rExp, pos), rExp)
        }
        return for (p <- evalExp(split, smt2, rtCheck, s0, exp.right, reporter)) yield evalBasicH(p)
      }

      def evalCond(s0: State, kind: AST.ResolvedInfo.BuiltIn.Kind.Type, v1: State.Value.Sym): ISZ[(State, State.Value)] = {
        val pos = exp.left.posOpt.get
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
            val s1 = s0.addClaim(State.Claim.Prop(T, v1))
            def evalCondAndH(p: (State, State.Value)): ISZ[(State, State.Value)] = {
              val (s2, v2) = p
              if (!s2.status) {
                return ISZ((s2, State.errorValue))
              }
              val (s3, r) = s2.freshSym(AST.Typed.b, exp.right.posOpt.get)
              val s4 = s3.addClaim(State.Claim.Let.Ite(r, v1, v2, State.Value.B(F, pos)))
              return ISZ((s4(claims = s0.claims ++ ops.ISZOps(s4.claims).slice(s1.claims.size, s4.claims.size)), r))
            }
            return for (p <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter); r <- evalCondAndH(p)) yield r
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
            val s1 = s0.addClaim(State.Claim.Prop(F, v1))
            def evalCondOrH(p: (State, State.Value)): ISZ[(State, State.Value)] = {
              val (s2, v2) = p
              if (!s2.status) {
                return ISZ((s2, State.errorValue))
              }
              val (s3, r) = s2.freshSym(AST.Typed.b, exp.right.posOpt.get)
              val s4 = s3.addClaim(State.Claim.Let.Ite(r, v1, State.Value.B(T, pos), v2))
              return ISZ((s4(claims = s0.claims ++ ops.ISZOps(s4.claims).slice(s1.claims.size, s4.claims.size)), r))
            }
            return for (p <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter); r <- evalCondOrH(p)) yield r
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
            val s1 = s0.addClaim(State.Claim.Prop(T, v1))
            def evalCondImplyH(p: (State, State.Value)): ISZ[(State, State.Value)] = {
              val (s2, v2) = p
              if (!s2.status) {
                return ISZ((s2, State.errorValue))
              }
              val (s3, r) = s2.freshSym(AST.Typed.b, exp.right.posOpt.get)
              val s4 = s3.addClaim(State.Claim.Let.Ite(r, v1, v2, State.Value.B(T, pos)))
              return ISZ((s4(claims = s0.claims ++ ops.ISZOps(s4.claims).slice(s1.claims.size, s4.claims.size)), r))
            }
            return for (p <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter); r <- evalCondImplyH(p)) yield r
          case _ => halt("Infeasible")
        }
      }

      def evalSeq(s0: State, m: AST.ResolvedInfo.Method): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        for (p1 <- evalExp(split, smt2, rtCheck, s0, exp.left, reporter)) {
          val (s1, v1) = p1
          if (s1.status) {
            for (p2 <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter)) {
              val (s2, v2) = p2
              if (s2.status) {
                val rTipe = e.typedOpt.get
                val (s3, rExp) = s2.freshSym(rTipe, e.posOpt.get)
                val s4 = s3.addClaim(State.Claim.Let.Binary(rExp, v1, exp.op, v2,
                  if (ops.StringOps(m.id).endsWith(":")) v2.tipe else v1.tipe))
                r = r :+ ((s4, rExp))
              } else {
                r = r :+ ((s2, State.errorValue))
              }
            }
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
        return r
      }

      val s0 = state

      exp.attr.resOpt.get match {
        case AST.ResolvedInfo.BuiltIn(kind) =>
          var r = ISZ[(State, State.Value)]()
          for (p <- evalExp(split, smt2, rtCheck, s0, exp.left, reporter)) {
            val (s1, v1) = p
            if (s1.status) {
              if (isCond(kind)) {
                val (s2, left) = value2Sym(s1, v1, exp.left.posOpt.get)
                r = r ++ evalCond(s2, kind, left)
              } else if (exp.op == "==" || exp.op == "!=" || isBasic(smt2, v1.tipe)) {
                r = r ++ evalBasic(s1, kind, v1)
              } else {
                halt(s"TODO: $e") // TODO
              }
            } else {
              r = r :+ ((s1, State.errorValue))
            }
          }
          return r
        case m: AST.ResolvedInfo.Method =>
          if (isSeq(m)) {
            return evalSeq(s0, m)
          }
          val posOpt = exp.posOpt
          return evalInvoke(s0, Some(exp.left), AST.Exp.Ident(AST.Id(exp.op, AST.Attr(posOpt)), exp.attr),
            Either.Left(ISZ(exp.right)), exp.attr)
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalSelectH(sp: Split.Type, res: AST.ResolvedInfo, receiverOpt: Option[AST.Exp], id: String, tipe: AST.Typed,
                    pos: Position): ISZ[(State, State.Value)] = {
      def evalField(t: AST.Typed): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        for (p <- evalExp(sp, smt2, rtCheck, state, receiverOpt.get, reporter)) {
          val (s0, o) = p
          if (s0.status) {
            val (s1, sym) = s0.freshSym(t, pos)
            r = r :+ ((s1.addClaim(State.Claim.Let.FieldLookup(sym, o, id)), sym))
          } else {
            r = r :+ ((s0, State.errorValue))
          }
        }
        return r
      }

      def evalEnumElement(eres: AST.ResolvedInfo.EnumElement): (State, State.Value) = {
        return (state, State.Value.Enum(tipe.asInstanceOf[AST.Typed.Name], eres.owner, eres.name, eres.ordinal, pos))
      }

      def evalTupleLit(tres: AST.ResolvedInfo.Tuple): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        val (s0, sym) = state.freshSym(tipe, pos)
        for (p <- evalExp(split, smt2, rtCheck, s0, receiverOpt.get, reporter)) {
          val (s1, v) = p
          if (s1.status) {
            r = r :+ ((s1.addClaim(State.Claim.Let.FieldLookup(sym, v, s"_${tres.index}")), sym))
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
        return r
      }

      res match {
        case res: AST.ResolvedInfo.Var =>
          assert(!res.isInObject && receiverOpt.nonEmpty)
          return evalField(tipe)
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method && res.tpeOpt.get.isByName =>
          return evalField(res.tpeOpt.get.ret)
        case res: AST.ResolvedInfo.LocalVar => return ISZ(evalIdentH(state, res, tipe, pos))
        case res: AST.ResolvedInfo.EnumElement => return ISZ(evalEnumElement(res))
        case res: AST.ResolvedInfo.Tuple =>
          assert(receiverOpt.nonEmpty)
          return evalTupleLit(res)
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalSelect(exp: AST.Exp.Select): ISZ[(State, State.Value)] = {
      val pos = exp.id.attr.posOpt.get
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Ext && res.owner.size == 3
          && ops.ISZOps(res.owner).dropRight(1) == AST.Typed.sireumName && res.id == "random" =>
          val s0 = state
          val (s1, sym) = s0.freshSym(res.tpeOpt.get.ret, pos)
          return ISZ((s1.addClaim(State.Claim.Def.Random(sym, pos)), sym))
        case res => return evalSelectH(split, res, exp.receiverOpt, exp.id.value, exp.typedOpt.get, pos)
      }
    }

    def evalConstructor(sp: Split.Type,
                        isCopy: B,
                        invokeReceiverOpt: Option[AST.Exp],
                        ident: AST.Exp.Ident,
                        eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]],
                        attr: AST.ResolvedAttr): ISZ[(State, State.Value)] = {
      val t = attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
      var r = ISZ[(State, State.Value)]()

      def evalSConstructor(): Unit = {
        val (s0, sym) = state.freshSym(t, attr.posOpt.get)
        for (p <- evalArgs(sp, smt2, rtCheck, s0, -1, eargs, reporter)) {
          val (s1, args) = p
          if (s1.status) {
            val it = t.args(0).asInstanceOf[AST.Typed.Name]
            var indices = ISZ[State.Value]()
            if (it == AST.Typed.z) {
              indices = for (i <- 0 until args.size) yield State.Value.Z(i, args(i).get.pos)
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
                indices = indices :+ z2subz(index, args(i).get.pos)
                index = index + 1
                i = i + 1
              }
            }
            smt2.addSeqLit(t, indices.size)
            val as: ISZ[State.Claim.Def.SeqLit.Arg] =
              for (p <- ops.ISZOps(indices).zip(args)) yield State.Claim.Def.SeqLit.Arg(p._1, p._2.get)
            r = r :+ ((s1.addClaim(State.Claim.Def.SeqLit(sym, as)), sym))
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
      }

      def evalAdtConstructor(s0: State, receiverOpt: Option[State.Value]): Unit = {
        val (s1, sym) = s0.freshSym(t, attr.posOpt.get)
        val ti = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
        val params = ti.ast.params
        for (p <- evalArgs(sp, smt2, rtCheck, s1, params.size, eargs, reporter)) {
          val s2 = p._1
          val args = p._2.toMS
          if (s2.status) {
            var s3 = s2
            eargs match {
              case Either.Right(_) =>
                for (i <- 0 until args.size) {
                  if (args(i).isEmpty) {
                    val receiver = receiverOpt.get
                    val param = params(i)
                    val pt = param.tipe.typedOpt.get
                    val (s4, sym) = s3.freshSym(pt, param.id.attr.posOpt.get)
                    s3 = s4.addClaim(State.Claim.Let.FieldLookup(sym, receiver, param.id.value))
                    args(i) = Some(sym)
                  }
                }
              case _ =>
            }
            r = r :+ ((s3.addClaim(State.Claim.Def.AdtLit(sym, args.toIS.map((vOpt: Option[State.Value]) => vOpt.get))), sym))
          } else {
            r = r :+ ((s2, State.errorValue))
          }
        }
      }

      if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
        evalSConstructor()
      } else {
        val stateReceiverOpts: ISZ[(State, Option[State.Value])] =
          if (isCopy) for (p <- evalReceiver(Split.Default, invokeReceiverOpt, ident)) yield (p._1, Some(p._2))
          else ISZ((state, None()))
        for (p <- stateReceiverOpts) {
          val (s0, receiverOpt) = p
          evalAdtConstructor(s0, receiverOpt)
        }
      }
      return r
    }

    def evalReceiver(sp: Split.Type, receiverOpt: Option[AST.Exp], ident: AST.Exp.Ident): ISZ[(State, State.Value)] = {
      receiverOpt match {
        case Some(rcv) =>
          ident.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var =>
              return evalSelectH(sp, res, receiverOpt, ident.id.value, ident.typedOpt.get, ident.posOpt.get)
            case _ => return evalExp(sp, smt2, rtCheck, state, rcv, reporter)
          }
        case _ => return evalExp(sp, smt2, rtCheck, state, ident, reporter)
      }
    }

    def evalSeqSelect(exp: AST.Exp.Invoke): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (p0 <- evalReceiver(split, exp.receiverOpt, exp.ident); p1 <- evalExp(split, smt2, rtCheck, p0._1, exp.args(0), reporter)) {
        val (_, seq) = p0
        val (s1, i) = p1
        val s2 = checkSeqIndexing(smt2, rtCheck, s1, seq, i, exp.args(0).posOpt, reporter)
        val (s3, v) = s2.freshSym(exp.typedOpt.get, exp.posOpt.get)
        r = r :+ ((s3.addClaim(State.Claim.Let.SeqLookup(v, seq, i)), v))
      }
      return r
    }

    def evalResult(exp: AST.Exp.Result): (State, State.Value) = {
      val (s, sym) = Logika.resIntro(exp.posOpt.get, state, context.methodOpt.get.name, exp.typedOpt.get, None())
      return (s, sym)
    }

    def evalThis(exp: AST.Exp.This): (State, State.Value) = {
      val (s, sym) = Logika.idIntro(exp.posOpt.get, state, context.methodOpt.get.name, "this", exp.typedOpt.get, None())
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
      var quantClaims = ISZ[State.Claim]()
      val (s0, sym) = state.freshSym(AST.Typed.b, quant.attr.posOpt.get)
      var nextFresh = s0.nextFresh
      for (p <- evalAssignExpValue(Split.Enabled, smt2, AST.Typed.b, rtCheck, s0, quant.fun.exp, reporter)) {
        val (s1, v) = p
        val (s2, expSym) = value2Sym(s1, v, quant.fun.exp.asStmt.posOpt.get)
        quantClaims = quantClaims :+ State.Claim.And(ops.ISZOps(s2.claims).slice(s0.claims.size, s2.claims.size) :+ State.Claim.Prop(T, expSym))
        if (nextFresh < s2.nextFresh) {
          nextFresh = s2.nextFresh
        }
      }
      val vars: ISZ[State.Claim.Let.Quant.Var] =
        for (p <- quant.fun.params) yield State.Claim.Let.Quant.Var.Id(p.idOpt.get.value, p.typedOpt.get)
      val qcs: ISZ[State.Claim] =
        if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
        else ISZ(State.Claim.And(quantClaims))
      return (s0(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym)
    }

    def evalQuantRange(quant: AST.Exp.QuantRange): ISZ[(State, State.Value)] = {
      val qVarType = quant.attr.typedOpt.get
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val s0 = state
      var r = ISZ[(State, State.Value)]()
      for (p1 <- evalExp(split, smt2, rtCheck, s0, quant.lo, reporter);
           p2 <- evalExp(split, smt2, rtCheck, p1._1, quant.hi, reporter)) {
        val (_, lo) = p1
        val (s2, hi) = p2
        if (s2.status) {
          val (s3, ident) = evalIdentH(s2, quant.attr.resOpt.get, qVarType, quant.fun.params(0).idOpt.get.attr.posOpt.get)
          val (s4, loSym) = s3.freshSym(AST.Typed.b, quant.lo.posOpt.get)
          val s5 = s4.addClaim(State.Claim.Let.Binary(loSym, lo, AST.Exp.BinaryOp.Le, ident, qVarType))
          val loProp = State.Claim.Prop(T, loSym)
          val (s6, hiSym) = s5.freshSym(AST.Typed.b, quant.hi.posOpt.get)
          val hiProp = State.Claim.Prop(T, hiSym)
          val s7 = s6.addClaim(State.Claim.Let.Binary(hiSym, ident,
            if (quant.hiExact) AST.Exp.BinaryOp.Le else AST.Exp.BinaryOp.Lt, hi, qVarType))
          val (s8, sym) = s7.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var.Id(qVarRes.id, qVarType))
          var quantClaims = ISZ[State.Claim]()
          var nextFresh: Z = s8.nextFresh
          for (p <- evalAssignExpValue(Split.Enabled, smt2, AST.Typed.b, rtCheck, s8.addClaims(ISZ(loProp, hiProp)), quant.fun.exp, reporter)) {
            val (s9, v) = p
            val (s10, expSym) = value2Sym(s9, v, quant.fun.exp.asStmt.posOpt.get)
            val props: ISZ[State.Claim] = ISZ(loProp, hiProp, State.Claim.Prop(T, expSym))
            val s10ClaimsOps = ops.ISZOps(s10.claims)
            val quantClaim = (s10ClaimsOps.slice(s2.claims.size, s8.claims.size) ++ s10ClaimsOps.slice(s8.claims.size + 2, s10.claims.size)) :+
              (if (quant.isForall) State.Claim.Imply(props) else State.Claim.And(props))
            quantClaims = quantClaims :+ State.Claim.And(quantClaim)
            if (nextFresh < s10.nextFresh) {
              nextFresh = s10.nextFresh
            }
          }
          val qcs: ISZ[State.Claim] =
            if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
            else ISZ(State.Claim.And(quantClaims))
          r = r :+ ((s2(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym))
        } else {
          r = r :+ ((s2, State.errorValue))
        }
      }
      return r
    }

    def evalQuantEachIndex(quant: AST.Exp.QuantEach, seqExp: AST.Exp): ISZ[(State, State.Value)] = {
      val qVarType = quant.attr.typedOpt.get
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val sType: AST.Typed.Name = seqExp.typedOpt.get match {
        case t: AST.Typed.Name => t
        case t: AST.Typed.Method => t.tpe.ret.asInstanceOf[AST.Typed.Name]
        case _ => halt("Infeasible")
      }
      val s0 = state
      val posOpt = seqExp.posOpt
      val firstIndexResAttr = AST.ResolvedAttr(posOpt, Some(AST.ResolvedInfo.Method(F, AST.MethodMode.Method, ISZ(),
        sType.ids, "firstIndex", ISZ(), Some(AST.Typed.Fun(T, T, ISZ(), qVarType)))), Some(qVarType))
      val lastIndexResAttr = AST.ResolvedAttr(posOpt, Some(AST.ResolvedInfo.Method(F, AST.MethodMode.Method, ISZ(),
        sType.ids, "lastIndex", ISZ(), Some(AST.Typed.Fun(T, T, ISZ(), qVarType)))), Some(qVarType))
      val firstIndexExp = AST.Exp.Select(Some(seqExp), AST.Id("firstIndex", AST.Attr(posOpt)), ISZ(), firstIndexResAttr)
      val lastIndexExp = AST.Exp.Select(Some(seqExp), AST.Id("lastIndex", AST.Attr(posOpt)), ISZ(), lastIndexResAttr)
      var r = ISZ[(State, State.Value)]()
      for (p1 <- evalExp(split, smt2, rtCheck, s0, firstIndexExp, reporter);
           p2 <- evalExp(split, smt2, rtCheck, p1._1, lastIndexExp, reporter)) {
        val (_, lo) = p1
        val (s2, hi) = p2
        if (s2.status) {
          val (s3, ident) = evalIdentH(s2, quant.attr.resOpt.get, qVarType, quant.fun.params(0).idOpt.get.attr.posOpt.get)
          val (s4, loSym) = s3.freshSym(AST.Typed.b, seqExp.posOpt.get)
          val s5 = s4.addClaim(State.Claim.Let.Binary(loSym, lo, AST.Exp.BinaryOp.Le, ident, qVarType))
          val loProp = State.Claim.Prop(T, loSym)
          val (s6, hiSym) = s5.freshSym(AST.Typed.b, seqExp.posOpt.get)
          val s7 = s6.addClaim(State.Claim.Let.Binary(hiSym, ident, AST.Exp.BinaryOp.Le, hi, qVarType))
          val hiProp = State.Claim.Prop(T, hiSym)
          val (s8, sym) = s7.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var.Id(qVarRes.id, qVarType))
          var quantClaims = ISZ[State.Claim]()
          var nextFresh: Z = s8.nextFresh
          for (p <- evalAssignExpValue(Split.Enabled, smt2, AST.Typed.b, rtCheck, s8.addClaims(ISZ(loProp, hiProp)), quant.fun.exp, reporter)) {
            val (s9, v) = p
            val (s10, expSym) = value2Sym(s9, v, quant.fun.exp.asStmt.posOpt.get)
            val props: ISZ[State.Claim] = ISZ(loProp, hiProp, State.Claim.Prop(T, expSym))
            val s10ClaimsOps = ops.ISZOps(s10.claims)
            val quantClaim = (s10ClaimsOps.slice(s2.claims.size, s8.claims.size) ++ s10ClaimsOps.slice(s8.claims.size + 2, s10.claims.size)) :+
              (if (quant.isForall) State.Claim.Imply(props) else State.Claim.And(props))
            quantClaims = quantClaims :+ State.Claim.And(quantClaim)
            if (nextFresh < s10.nextFresh) {
              nextFresh = s10.nextFresh
            }
          }
          val qcs: ISZ[State.Claim] =
            if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
            else ISZ(State.Claim.And(quantClaims))
          r = r :+ ((s2.addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym))
        } else {
          r = r :+ ((s2, State.errorValue))
        }
      }
      return r
    }

    def evalQuantEach(quant: AST.Exp.QuantEach): ISZ[(State, State.Value)] = {
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val sType: AST.Typed.Name = quant.seq.typedOpt.get match {
        case t: AST.Typed.Name => t
        case t: AST.Typed.Method => t.tpe.ret.asInstanceOf[AST.Typed.Name]
        case _ => halt("Infeasible")
      }
      val iType = sType.args(0)
      val eType = sType.args(1)
      val pos = quant.fun.params(0).idOpt.get.attr.posOpt.get
      var r = ISZ[(State, State.Value)]()
      for (p <- evalExp(split, smt2, rtCheck, state, quant.seq, reporter)) {
        val (s0, seq) = p
        if (s0.status) {
          val (s1, qvar) = Logika.idIntro(pos, s0, qVarRes.context, s"${qVarRes.id}$$Idx", iType, Some(pos))
          val (s2, inBound) = s1.freshSym(AST.Typed.b, pos)
          val s3 = s2.addClaim(State.Claim.Let.SeqInBound(inBound, seq, qvar))
          val inBoundProp = State.Claim.Prop(T, inBound)
          val (s4, select) = s3.freshSym(eType, pos)
          val s5 = s4.addClaim(State.Claim.Let.SeqLookup(select, seq, qvar))
          val s6 = s5.addClaim(State.Claim.Let.CurrentId(T, select, qVarRes.context, qVarRes.id, None()))
          val (s7, sym) = s6.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var.Sym(qvar))
          var quantClaims = ISZ[State.Claim]()
          var nextFresh: Z = s7.nextFresh
          for (p <- evalAssignExpValue(Split.Enabled, smt2, AST.Typed.b, rtCheck, s7.addClaim(inBoundProp), quant.fun.exp, reporter)) {
            val (s8, v) = p
            val (s9, expSym) = value2Sym(s8, v, quant.fun.exp.asStmt.posOpt.get)
            val props: ISZ[State.Claim] = ISZ(inBoundProp, State.Claim.Prop(T, expSym))
            val s9ClaimsOps = ops.ISZOps(s9.claims)
            val quantClaim = (s9ClaimsOps.slice(s1.claims.size, s7.claims.size) ++ s9ClaimsOps.slice(s7.claims.size + 1, s9.claims.size)) :+
              (if (quant.isForall) State.Claim.Imply(props) else State.Claim.And(props))
            quantClaims = quantClaims :+ State.Claim.And(quantClaim)
            if (nextFresh < s9.nextFresh) {
              nextFresh = s9.nextFresh
            }
          }
          val qcs: ISZ[State.Claim] =
            if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
            else ISZ(State.Claim.And(quantClaims))
          r = r :+ ((s0(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym))
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return r
    }

    def methodInfo(isInObject: B, owner: QName, id: String): InvokeMethodInfo = {
      def extractAssignExpOpt(mi: lang.symbol.Info.Method): Option[AST.AssignExp] = {
        if (mi.ast.purity == AST.Purity.StrictPure) {
          mi.ast.bodyOpt.get.stmts match {
            case ISZ(stmt: AST.Stmt.Var, _: AST.Stmt.Return) => return stmt.initOpt
            case stmts => halt(s"Infeasible: $stmts")
          }
        } else {
          return None()
        }
      }

      def extractResolvedInfo(attr: AST.ResolvedAttr): AST.ResolvedInfo.Method = {
        return attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      }

      if (isInObject) {
        th.nameMap.get(owner :+ id) match {
          case Some(mi: lang.symbol.Info.Method) =>
            return InvokeMethodInfo(mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr),
              extractAssignExpOpt(mi))
          case info => halt(s"Infeasible: $owner.$id => $info")
        }
      } else {
        th.typeMap.get(owner) match {
          case Some(info: lang.symbol.TypeInfo.Adt) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return InvokeMethodInfo(mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr),
                  extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return InvokeMethodInfo(mi.ast.sig, AST.MethodContract.Simple(ISZ(), ISZ(), ISZ(), ISZ()),
                      extractResolvedInfo(mi.ast.attr), None())
                  case _ => halt("Infeasible")
                }
            }
          case Some(info: lang.symbol.TypeInfo.Sig) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return InvokeMethodInfo(mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr),
                  extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return InvokeMethodInfo(mi.ast.sig, AST.MethodContract.Simple(ISZ(), ISZ(), ISZ(), ISZ()),
                      extractResolvedInfo(mi.ast.attr), None())
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
                   attr: AST.ResolvedAttr): ISZ[(State, State.Value)] = {
      val res = attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val posOpt = attr.posOpt
      val pos = posOpt.get
      val receiverPosOpt: Option[Position] =
        if (invokeReceiverOpt.nonEmpty) invokeReceiverOpt.get.posOpt
        else ident.posOpt
      val info = methodInfo(res.isInObject, res.owner, res.id)
      val contract = info.contract
      val isUnit = info.sig.returnType.typedOpt == AST.Typed.unitOpt
      val ctx = res.owner :+ res.id

      var r = ISZ[(State, State.Value)]()
      val stateSubstMapReceiverOpts: ISZ[(State, HashMap[String, AST.Typed], Option[State.Value.Sym])] =
        if (res.isInObject) {
          ISZ((s0, TypeChecker.emptySubstMap, None()))
        } else {
          var ssmros = ISZ[(State, HashMap[String, AST.Typed], Option[State.Value.Sym])]()
          for (p <- evalReceiver(split, invokeReceiverOpt, ident)) {
            var typeSubstMap = TypeChecker.emptySubstMap
            val p2 = value2Sym(p._1, p._2, receiverPosOpt.get)
            val s1 = p2._1
            val receiver = p2._2
            val receiverType = receiver.tipe.asInstanceOf[AST.Typed.Name]
            th.typeMap.get(receiverType.ids) match {
              case Some(ti: TypeInfo.Adt) =>
                TypeChecker.buildTypeSubstMap(receiverType.ids, receiverPosOpt, ti.ast.typeParams, receiverType.args,
                  reporter) match {
                  case Some(sm) => typeSubstMap = typeSubstMap ++ sm.entries
                  case _ => r = r :+ ((s1, State.errorValue))
                }
              case Some(ti: TypeInfo.Sig) =>
                TypeChecker.buildTypeSubstMap(receiverType.ids, receiverPosOpt, ti.ast.typeParams, receiverType.args,
                  reporter) match {
                  case Some(sm) => typeSubstMap = typeSubstMap ++ sm.entries
                  case _ => r = r :+ ((s1, State.errorValue))
                }
              case _ => halt(s"Infeasible: $receiverType")
            }
            ssmros = ssmros :+ ((s1, typeSubstMap, Some(receiver)))
          }
          ssmros
        }

      def strictPure(s1: State, typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed,
                     receiverOpt: Option[State.Value.Sym], paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]): Unit = {
        val (s2, pf) = strictPureMethod(smt2, s1, info, typeSubstMap, reporter)
        val (s3, re) = s2.freshSym(retType, pos)
        var args: ISZ[State.Value] = for (q <- paramArgs) yield q._4
        receiverOpt match {
          case Some(receiver) => args = receiver +: args
          case _ =>
        }
        r = r :+ ((s3.addClaim(State.Claim.Let.ProofFunApply(re, pf, args)), re))
      }

      def compositional(s: State, typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed,
                        receiverOpt: Option[State.Value.Sym], paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]): Unit = {
        var s1 = s
        for (q <- paramArgs) {
          val (l, _, arg, v) = q
          val (s3, sym) = value2Sym(s1, v, arg.posOpt.get)
          s1 = s3.addClaim(State.Claim.Let.CurrentId(F, sym, l.context, l.id, arg.posOpt))
        }

        def evalContractCase(logikaComp: Logika, currentReceiverOpt: Option[State.Value.Sym], assume: B, cs0: State,
                             labelOpt: Option[AST.Exp.LitString], requires: ISZ[AST.Exp],
                             ensures: ISZ[AST.Exp]): ContractCaseResult = {
          val modLocals = contract.modifiedLocalVars

          def modVarsResult(ms0: State, mposOpt: Option[Position]): (State, State.Value) = {
            var ms1 = ms0
            val modObjectVars = contract.modifiedObjectVars
            val mpos = mposOpt.get
            ms1 = Logika.rewriteObjectVars(ms1, modObjectVars, mpos)
            ms1 = Logika.rewriteLocalVars(ms1, modLocals.keys)
            if (isUnit) {
              return (ms1, State.Value.Unit(mpos))
            } else {
              val (ms2, v) = Logika.resIntro(mpos, ms1, ctx, retType, mposOpt)
              ms1 = ms2
              return (ms1, v)
            }
          }

          def modVarsRewrite(ms0: State): State = {
            var ms1 = ms0
            for (q <- paramArgs) {
              val (p, t, arg, _) = q
              if (modLocals.contains(p)) {
                val (ms2, v) = Logika.idIntro(arg.posOpt.get, ms1, p.context, p.id, t, None())
                ms1 = singleState(assignRec(Split.Disabled, smt2, ms2, arg, v, reporter))
              }
            }
            var rwLocals: ISZ[AST.ResolvedInfo.LocalVar] = for (q <- paramArgs) yield q._1
            if (!isUnit) {
              rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "Res")
            }
            if (receiverOpt.nonEmpty) {
              rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "this")
            }
            ms1 = Logika.rewriteLocalVars(ms1, rwLocals)
            currentReceiverOpt match {
              case Some(receiver) =>
                ms1 = ms1.addClaim(State.Claim.Let.CurrentId(F, receiver, context.methodOpt.get.name, "this",
                  context.methodOpt.get.posOpt))
              case _ =>
            }
            return ms1
          }

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
                val p = logikaComp.evalAssume(smt2, F, "Pre-condition", cs1, AST.Util.substExp(require, typeSubstMap), rep)
                val size = p._1.claims.size
                assert(p._1.claims(size - 1) == State.Claim.Prop(T, p._2))
                (p._1(claims = ops.ISZOps(p._1.claims).slice(0, size - 1)), p._2)
              } else {
                logikaComp.evalAssert(smt2, F, "Pre-condition", cs1, AST.Util.substExp(require, typeSubstMap), rep)
              }
            cs1 = cs2
            requireSyms = requireSyms :+ sym
            if (!cs1.status) {
              val (cs3, rsym) = cs1.freshSym(AST.Typed.b, pos)
              cs1 = cs3.addClaim(State.Claim.Let.And(rsym, requireSyms))
              return ContractCaseResult(F, cs1, State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
            }
          }
          val (cs4, result) = modVarsResult(cs1, posOpt)
          cs1 = cs4
          for (ensure <- ensures if cs1.status) {
            cs1 = logikaComp.evalAssume(smt2, F, "Post-condition", cs1, AST.Util.substExp(ensure, typeSubstMap), rep)._1
            if (!cs1.status) {
              val (cs5, rsym) = cs1.freshSym(AST.Typed.b, pos)
              cs1 = cs5.addClaim(State.Claim.Let.And(rsym, requireSyms))
              return ContractCaseResult(T, cs1, State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
            }
          }
          cs1 = modVarsRewrite(cs1)
          val (cs6, rsym) = cs1.freshSym(AST.Typed.b, pos)
          cs1 = cs6.addClaim(State.Claim.Let.And(rsym, requireSyms))
          return ContractCaseResult(T, Logika.conjunctClaimSuffix(cs0, cs1), result, State.Claim.Prop(T, rsym),
            rep.messages)
        }

        val logikaComp: Logika = {
          val l = Logika.logikaMethod(th, config, ctx, receiverOpt.map(t => t.tipe), info.sig, receiverPosOpt,
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
            s1 = s1.addClaim(State.Claim.Let.CurrentId(F, receiver, res.owner :+ res.id, "this", receiverPosOpt))
          case _ =>
        }
        contract match {
          case contract: AST.MethodContract.Simple =>
            val ccr = evalContractCase(logikaComp, currentReceiverOpt, F, s1, None(), contract.requires, contract.ensures)
            reporter.reports(ccr.messages)
            r = r :+ ((ccr.state, ccr.retVal))
          case contract: AST.MethodContract.Cases =>
            val root = s1
            var isPreOK = F
            var ccrs = ISZ[ContractCaseResult]()
            var okCcrs = ISZ[ContractCaseResult]()
            for (cas <- contract.cases) {
              val ccr = evalContractCase(logikaComp, currentReceiverOpt, T, s1,
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
              r = r :+ ((s1(status = F), State.errorValue))
            } else if (okCcrs.size == 1) {
              val ccr = okCcrs(0)
              s1 = s1(claims = ccr.state.claims :+ ccr.requiresClaim)
              reporter.reports(ccr.messages)
              r = r :+ ((s1, ccr.retVal))
            } else {
              val shouldSplit: B = split match {
                case Split.Default => config.splitAll || config.splitContract
                case Split.Enabled => T
                case Split.Disabled => F
              }
              for (ccr <- okCcrs) {
                reporter.reports(ccr.messages)
              }
              var nextFresh: Z =
                ops.ISZOps(okCcrs).foldLeft((nf: Z, ccr: ContractCaseResult) =>
                  if (nf < ccr.state.nextFresh) ccr.state.nextFresh else nf, -1)
              if (!isUnit) {
                nextFresh = nextFresh + 1
              }
              if (shouldSplit) {
                for (ccr <- okCcrs) {
                  val claims = root.claims :+ State.Claim.Imply(ISZ(ccr.requiresClaim,
                    State.Claim.And(ops.ISZOps(ccr.state.claims).slice(root.claims.size, ccr.state.claims.size))))
                  r = r :+ ((ccr.state(nextFresh = nextFresh, claims = claims), ccr.retVal))
                }
              } else {
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
                  r = r :+ ((s1(nextFresh = nextFresh), okCcrs(0).retVal))
                } else {
                  val (s7, sym) = s1.freshSym(retType, pos)
                  s1 = s7
                  r = r :+ ((s1(nextFresh = nextFresh).addClaim(State.Claim.And(
                    for (ccr <- okCcrs) yield State.Claim.Imply(ISZ(ccr.requiresClaim,
                      State.Claim.Let.Eq(sym, ccr.retVal))))), sym))
                }
              }
            }
        }
      }

      for (t <- stateSubstMapReceiverOpts) {
        var typeSubstMap = t._2
        val receiverOpt = t._3
        for (p <- evalArgs(split, smt2, rtCheck, t._1, info.sig.params.size, eargs, reporter)) {
          val (s1, vs) = p
          if (s1.status) {
            val argTypes = MSZ.create[AST.Typed](info.sig.params.size, AST.Typed.nothing)
            var paramArgs = ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]()
            eargs match {
              case Either.Left(args) =>
                var i = 0
                for (pArg <- ops.ISZOps(ops.ISZOps(info.sig.params).zip(args)).zip(vs)) {
                  val ((p, arg), vOpt) = pArg
                  val id = p.id.value
                  val argType = arg.typedOpt.get
                  argTypes(i) = argType
                  paramArgs = paramArgs :+
                    ((AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id), argType, arg, vOpt.get))
                  i = i + 1
                }
              case Either.Right(nargs) =>
                var m = HashMap.empty[Z, AST.Exp]
                for (narg <- nargs) {
                  m = m + narg.index ~> narg.arg
                }
                for (i <- 0 until vs.size) {
                  val v = vs(i).get
                  val param = info.sig.params(i)
                  val id = param.id.value
                  val arg = m.get(i).get
                  val argType = arg.typedOpt.get
                  argTypes(i) = argType
                  paramArgs = paramArgs :+
                    ((AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id), argType, arg, v))
                }
            }
            val mType = info.sig.funType
            val invokeType = mType(args = argTypes.toIS, ret = attr.typedOpt.get)
            TypeChecker.unify(th, posOpt, TypeChecker.TypeRelation.Equal, invokeType, mType, reporter) match {
              case Some(sm) =>
                typeSubstMap = typeSubstMap ++ sm.entries
                val retType = info.res.tpeOpt.get.ret.subst(typeSubstMap)
                if (info.strictPureBodyOpt.nonEmpty) {
                  strictPure(s1, typeSubstMap, retType, receiverOpt, paramArgs)
                } else {
                  compositional(s1, typeSubstMap, retType, receiverOpt, paramArgs)
                }
              case _ => r = r :+ ((s1, State.errorValue))
            }
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
      }

      return r
    }

    def evalTupleExp(tuple: AST.Exp.Tuple): ISZ[(State, State.Value)] = {
      if (tuple.args.size == 1) {
        return evalExp(split, smt2, rtCheck, state, tuple.args(0), reporter)
      }
      var r = ISZ[(State, State.Value)]()
      var nextFresh: Z = -1
      for (p <- evalExps(Split.Default, smt2, rtCheck, state, tuple.args.size, (i: Z) => tuple.args(i), reporter)) {
        val (s0, args) = p
        if (s0.status) {
          val (s1, sym) = s0.freshSym(tuple.typedOpt.get, tuple.posOpt.get)
          r = r :+ ((s1.addClaim(State.Claim.Let.TupleLit(sym, args)), sym))
          if (nextFresh < s1.nextFresh) {
            nextFresh = s1.nextFresh
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return if (r.size > 1) r else for (p <- r) yield (p._1(nextFresh = nextFresh), p._2)
    }

    def evalIfExp(sp: Split.Type, ifExp: AST.Exp.If): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      val shouldSplit: B = sp match {
        case Split.Default => config.splitAll || config.splitIf
        case Split.Enabled => T
        case Split.Disabled => F
      }
      val t = ifExp.typedOpt.get
      val pos = ifExp.posOpt.get
      for (p <- evalExp(sp, smt2, rtCheck, state, ifExp.cond, reporter)) {
        val (s0, cond) = p
        if (s0.status) {
          val (s1, sym) = value2Sym(s0, cond, ifExp.cond.posOpt.get)
          val prop = State.Claim.Prop(T, sym)
          val negProp = State.Claim.Prop(F, sym)
          val thenBranch = smt2.sat(config.logVc, config.logVcDirOpt, s"if-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, s1.claims :+ prop, reporter)
          val elseBranch = smt2.sat(config.logVc, config.logVcDirOpt, s"if-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, s1.claims :+ prop, reporter)
          (thenBranch, elseBranch) match {
            case (T, T) =>
              val (s2, re) = s1.freshSym(t, pos)
              val s3vs = evalExp(sp, smt2, rtCheck, s2.addClaim(prop), ifExp.thenExp, reporter)
              val s3NextFresh = maxStateValuesNextFresh(s3vs)
              val s4vs = evalExp(sp, smt2, rtCheck, s2(nextFresh = s3NextFresh).addClaim(negProp), ifExp.elseExp, reporter)
              val s4NextFresh = maxStateValuesNextFresh(s4vs)
              if (shouldSplit) {
                for (s3v <- s3vs) {
                  val (s3t, tv) = s3v
                  val s3 = s3t(nextFresh = s4NextFresh, claims = s2.claims :+ State.Claim.Imply(ISZ(
                    prop, State.Claim.And(ops.ISZOps(s3t.claims).slice(s2.claims.size + 1, s3t.claims.size))
                  )))
                  r = r :+ ((s3, tv))
                }
                for (s4v <- s4vs) {
                  val (s4t, ev) = s4v
                  val s4 = s4t(claims = s2.claims :+ State.Claim.Imply(ISZ(
                    negProp, State.Claim.And(ops.ISZOps(s4t.claims).slice(s2.claims.size + 1, s4t.claims.size))
                  )))
                  r = r :+ ((s4, ev))
                }
              } else {
                for (s3v <- s3vs; s4v <- s4vs) {
                  val (s3, tv) = s3v
                  val (s4, ev) = s4v
                  val s5 = mergeStates(s1, sym, s3, s4, s4.nextFresh)
                  r = r :+ ((s5.addClaim(State.Claim.If(sym,
                    ISZ(State.Claim.Let.Eq(re, tv)),
                    ISZ(State.Claim.Let.Eq(re, ev)))), re))
                }
              }
            case (T, F) => r = r ++ evalExp(sp, smt2, rtCheck, s1, ifExp.thenExp, reporter)
            case (F, T) => r = r ++ evalExp(sp, smt2, rtCheck, s1, ifExp.elseExp, reporter)
            case (_, _) => r = r :+ ((s0(status = F), State.errorValue))
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return r
    }

    def expH(s0: State): ISZ[(State, State.Value)] = {
      e match {
        case lit: AST.Lit => return ISZ((s0, evalLit(lit)))
        case lit: AST.Exp.StringInterpolate => return ISZ((s0, evalInterpolate(lit)))
        case e: AST.Exp.Ident => return ISZ(evalIdent(e))
        case e: AST.Exp.Select => return evalSelect(e)
        case e: AST.Exp.Unary => return evalUnaryExp(e)
        case e: AST.Exp.Binary => return evalBinaryExp(e)
        case e: AST.Exp.If => return evalIfExp(split, e)
        case e: AST.Exp.Tuple => return evalTupleExp(e)
        case e: AST.Exp.Invoke =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Select => return evalSeqSelect(e)
                case AST.MethodMode.Constructor =>
                  return evalConstructor(split, F, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
                case AST.MethodMode.Method =>
                  return evalInvoke(state, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
                case _ =>
              }
            case _ =>
          }
          halt(s"TODO: $e") // TODO
        case e: AST.Exp.InvokeNamed =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Constructor =>
                  return evalConstructor(split, F, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Copy =>
                  return evalConstructor(split, T, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Method =>
                  return evalInvoke(state, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case _ =>
              }
            case _ =>
          }
          halt(s"TODO: $e") // TODO
        case e: AST.Exp.Result => return ISZ(evalResult(e))
        case e: AST.Exp.Input => return ISZ(evalInput(e))
        case e: AST.Exp.QuantType => return ISZ(evalQuantType(e))
        case e: AST.Exp.QuantRange => return evalQuantRange(e)
        case e: AST.Exp.QuantEach =>
          e.seq match {
            case seq: AST.Exp.Select =>
              seq.attr.resOpt.get match {
                case res: AST.ResolvedInfo.Method if
                (res.owner == AST.Typed.isName || res.owner == AST.Typed.msName) &&
                  res.id == "indices" =>
                  return evalQuantEachIndex(e, seq.receiverOpt.get)
                case _ =>
              }
            case _ =>
          }
          return evalQuantEach(e)
        case e: AST.Exp.This => return ISZ(evalThis(e))
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def checkSplits(svs: ISZ[(State, State.Value)]): ISZ[(State, State.Value)] = {
      assert(svs.size > 0)
      var nextFresh: Z = -1
      for (sv <- svs if nextFresh == -1) {
        if (sv._1.status) {
          nextFresh = sv._1.nextFresh
        }
      }
      assert(svs.size == 1 || ops.ISZOps(svs).forall((p: (State, State.Value)) => !p._1.status || nextFresh == p._1.nextFresh))
      return svs
    }

    return checkSplits(expH(state))
  }

  def value2Sym(s0: State, v: State.Value, pos: Position): (State, State.Value.Sym) = {
    v match {
      case v: State.Value.Sym => return (s0, v)
      case _ =>
        val (s2, symV) = s0.freshSym(v.tipe, pos)
        return (s2.addClaim(State.Claim.Let.Eq(symV, v)), symV)
    }
  }

  def evalAssumeH(smt2: Smt2, title: String, s0: State, sym: State.Value.Sym, posOpt: Option[Position],
                  reporter: Reporter): State = {
    val s1 = s0(claims = s0.claims :+ State.Claim.Prop(T, sym))
    val pos = posOpt.get
    val sat = smt2.sat(config.logVc, config.logVcDirOpt, s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims, reporter)
    return s1(status = sat)
  }

  def evalAssume(smt2: Smt2, rtCheck: B, title: String, s0: State, cond: AST.Exp, reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = singleStateValue(evalExp(Split.Disabled, smt2, rtCheck, s0, cond, reporter))
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssumeH(smt2, title, s2, sym, cond.posOpt, reporter), sym)
  }

  def evalAssertH(smt2: Smt2, title: String, s0: State, sym: State.Value.Sym, posOpt: Option[Position],
                  reporter: Reporter): State = {
    val conclusion = State.Claim.Prop(T, sym)
    val pos = posOpt.get
    val r = smt2.valid(config.logVc, config.logVcDirOpt, s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos,
      s0.claims, conclusion, timeoutInMs, reporter)
    r.kind match {
      case Smt2Query.Result.Kind.Unsat => return s0.addClaim(conclusion)
      case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}", reporter)
      case Smt2Query.Result.Kind.Unknown => error(posOpt, s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds", reporter)
      case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower}", reporter)
      case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower}", reporter)
    }
    return s0(status = F, claims = s0.claims :+ conclusion)
  }

  def evalAssert(smt2: Smt2, rtCheck: B, title: String, s0: State, cond: AST.Exp, reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = singleStateValue(evalExp(Split.Disabled, smt2, rtCheck, s0, cond, reporter))
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssertH(smt2, title, s2, sym, cond.posOpt, reporter), sym)
  }

  def evalAssignExp(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State, ae: AST.AssignExp, reporter: Reporter): ISZ[State] = {
    ae match {
      case ae: AST.Stmt.Expr =>
        ae.exp match {
          case e: AST.Exp.Invoke =>
            var r = ISZ[State]()
            for (p <- evalExprInvoke(split, smt2, rtCheck, s0, ae, e, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.status => r = r :+ s1.addClaim(State.Claim.Let.Eq(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
          case _ =>
            var r = ISZ[State]()
            for (p <- evalExp(split, smt2, rtCheck, s0, ae.exp, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.status => r = r :+ s1.addClaim(State.Claim.Let.Eq(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
        }
      case ae: AST.Stmt.Block => return evalBlock(split, smt2, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.If => return evalIf(split, smt2, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Match => return evalMatch(split, smt2, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Return => return evalStmt(split, smt2, rtCheck, s0, ae, reporter)
    }
  }

  def evalAssignExpValue(split: Split.Type, smt2: Smt2, t: AST.Typed, rtCheck: B, s0: State, ae: AST.AssignExp,
                         reporter: Reporter): ISZ[(State, State.Value)] = {
    ae match {
      case ae: AST.Stmt.Expr => return evalExp(split, smt2, rtCheck, s0, ae.exp, reporter)
      case _ =>
        val (s1, sym) = s0.freshSym(t, ae.asStmt.posOpt.get)
        return for (s2 <- evalAssignExp(split, smt2, Some(sym), rtCheck, s1, ae, reporter)) yield (s2, sym)
    }
  }

  def evalAssignLocalH(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: State.Value.Sym, idPos: Position): State = {
    val s1: State = if (decl) s0 else Logika.rewriteLocal(s0, lcontext, id)
    return s1(claims = s1.claims :+ State.Claim.Let.CurrentId(F, rhs, lcontext, id, Some(idPos)))
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

  def assignRec(split: Split.Type, smt2: Smt2, s0: State, lhs: AST.Exp, rhs: State.Value.Sym, reporter: Reporter): ISZ[State] = {
    lhs match {
      case lhs: AST.Exp.Ident =>
        lhs.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar =>
            return ISZ(evalAssignLocalH(F, s0, res.context, res.id, rhs, lhs.posOpt.get))
          case res: AST.ResolvedInfo.Var =>
            if (res.isInObject) {
              return ISZ(evalAssignObjectVarH(s0, res.owner :+ res.id, rhs, lhs.posOpt.get))
            } else {
              return ISZ(evalAssignThisVarH(s0, lhs.id.value, rhs, lhs.posOpt.get))
            }
          case _ => halt(s"Infeasible: $lhs")
        }
      case lhs: AST.Exp.Invoke =>
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        var r = ISZ[State]()
        for (p1 <- evalExp(split, smt2, T, s0, receiver, reporter);
             p2 <- evalExp(split, smt2, T, p1._1, lhs.args(0), reporter)) {
          val (_, a) = p1
          val (s2, i) = p2
          val s3 = checkSeqIndexing(smt2, T, s2, a, i, lhs.args(0).posOpt, reporter)
          if (s3.status) {
            val (s4, newSym) = s3.freshSym(t, receiverPos)
            r = r ++ assignRec(split, smt2, s4.addClaim(State.Claim.Def.SeqStore(newSym, a, i, rhs)), receiver,
              newSym, reporter)
          } else {
            r = r :+ s3
          }
        }
        return r
      case lhs: AST.Exp.Select =>
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        var r = ISZ[State]()
        for (p <- evalExp(split, smt2, T, s0, receiver, reporter)) {
          val (s1, o) = p
          if (s1.status) {
            val (s2, newSym) = s1.freshSym(t, receiverPos)
            val id = lhs.id.value
            r = r ++ assignRec(split, smt2, s2.addClaim(State.Claim.Def.FieldStore(newSym, o, id, rhs)),
              receiver, newSym, reporter)
          } else {
            r = r :+ s1
          }
        }
        return r
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
      case pattern: AST.Pattern.LitInterpolate =>
        val lit = evalInterpolate(AST.Exp.StringInterpolate(pattern.prefix,
          ISZ(AST.Exp.LitString(pattern.value, AST.Attr(pattern.posOpt))), ISZ(), pattern.attr))
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==", lit, v.tipe)), cond, Map.empty)
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
      case _: AST.Pattern.SeqWildcard => halt(s"Infeasible")
    }
  }

  def evalMatch(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
                stmt: AST.Stmt.Match, reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    val shouldSplit: B = split match {
      case Split.Default => config.splitAll || config.splitMatch
      case Split.Enabled => T
      case Split.Disabled => F
    }
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

    for (p <- evalExp(split, smt2, rtCheck, state, stmt.exp, reporter)) {
      val (s0, v) = p
      if (s0.status) {
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
              val (s4, ccond) = singleStateValue(evalExp(Split.Disabled, smt2, rtCheck, s3, cond, reporter))
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
        }
        val stmtPos = stmt.posOpt.get
        if (smt2.sat(config.logVc, config.logVcDirOpt, s"pattern match inexhaustiveness at [${stmtPos.beginLine}, ${stmtPos.beginColumn}]",
          stmtPos, s1.claims :+ State.Claim.And(for (p <- caseSyms) yield State.Claim.Prop(F, p._2)), reporter)) {
          error(stmt.posOpt, "Inexhaustive pattern match", reporter)
          r = r :+ s1(status = F)
        } else {
          var leafClaims = ISZ[(State.Claim, ISZ[State.Claim])]()
          var possibleCases = F
          for (i <- 0 until caseSyms.size) {
            val (c, sym, m) = caseSyms(i)
            val cond = State.Claim.And(
              (for (j <- 0 until i) yield State.Claim.Prop(F, caseSyms(j)._2).asInstanceOf[State.Claim]) :+
                State.Claim.Prop(T, sym))
            val posOpt = c.pattern.posOpt
            val pos = posOpt.get
            val s10 = s1.addClaim(cond)
            if (smt2.sat(config.logVc, config.logVcDirOpt, s"match case pattern at [${pos.beginLine}, ${pos.beginColumn}]",
              pos, s10.claims, reporter)) {
              possibleCases = T
              val (s11, _, bindings) = addPatternVars(s10, lcontext, m)
              var claims = ISZ[State.Claim]()
              for (s12 <- evalBody(split, smt2, rOpt, rtCheck, s11.addClaim(State.Claim.And(for (b <- bindings) yield
                State.Claim.Prop(T, b.asInstanceOf[State.Value.Sym]))), c.body, reporter)) {
                s1 = s1(nextFresh = s12.nextFresh)
                if (s12.status) {
                  claims = claims :+ State.Claim.And(
                    ops.ISZOps(s12.claims).slice(s1.claims.size + 1, s12.claims.size
                  ))
                }
              }
              if (claims.nonEmpty) {
                leafClaims = leafClaims :+ ((cond, claims))
              }
            } else {
              error(posOpt, "Infeasible pattern matching case", reporter)
            }
          }
          if (leafClaims.isEmpty) {
            if (!possibleCases) {
              error(stmt.posOpt, "Infeasible pattern matching cases", reporter)
            }
            r = r :+ s1(status = F)
          }
          if (shouldSplit) {
            r = r ++ (for (p <- leafClaims; c <- p._2) yield s1.addClaims(ISZ(p._1, c)))
          } else {
            r = r :+ s1.addClaim(State.Claim.And(for (p <- leafClaims) yield State.Claim.Imply(ISZ(p._1, State.Claim.Or(p._2)))))
          }
        }
      } else {
        r = r :+ s0
      }
    }
    if (r.size > 1) {
      val nextFresh = maxStatesNextFresh(r)
      return for (s <- r) yield s(nextFresh = nextFresh)
    } else {
      return r
    }
  }

  def evalBlock(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State, block: AST.Stmt.Block,
                reporter: Reporter): ISZ[State] = {
    return evalBody(split, smt2, rOpt, rtCheck, s0, block.body, reporter)
  }

  def evalIf(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State, ifStmt: AST.Stmt.If,
             reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    val shouldSplit: B = split match {
      case Split.Default => config.splitAll || config.splitIf
      case Split.Enabled => T
      case Split.Disabled => F
    }
    for (p <- evalExp(split, smt2, rtCheck, s0, ifStmt.cond, reporter)) {
      val (s1, v) = p
      if (s1.status) {
        val pos = ifStmt.cond.posOpt.get
        val (s1c, cond) = value2Sym(s1, v, pos)
        if (!s1c.status) {
          r = r :+ s1c
        } else {
          val s2 = Logika.conjunctClaimSuffix(s0, s1c)
          val prop = State.Claim.Prop(T, cond)
          val thenClaims = s2.claims :+ prop
          val thenSat = smt2.sat(config.logVc, config.logVcDirOpt, s"if-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, thenClaims, reporter)
          val s4s: ISZ[State] = if (thenSat) {
            val s3s = evalBody(split, smt2, rOpt, rtCheck, s2(claims = thenClaims), ifStmt.thenBody, reporter)
            s3s
          } else {
            ISZ(s2(status = F, claims = thenClaims))
          }
          val s4NextFresh = maxStatesNextFresh(s4s)
          val negProp = State.Claim.Prop(F, cond)
          val elseClaims = s2.claims :+ negProp
          val elseSat = smt2.sat(config.logVc, config.logVcDirOpt, s"if-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, elseClaims, reporter)
          val s6s: ISZ[State] = if (elseSat) {
            val s5s = evalBody(split, smt2, rOpt, rtCheck, s2(claims = elseClaims, nextFresh = s4NextFresh), ifStmt.elseBody, reporter)
            s5s
          } else {
            ISZ(s2(status = F, claims = elseClaims, nextFresh = s4NextFresh))
          }
          val s6NextFresh = maxStatesNextFresh(s6s)
          (thenSat, elseSat) match {
            case (T, T) =>
              if (shouldSplit) {
                for (s4t <- s4s) {
                  val s4 = s4t(nextFresh = s6NextFresh, claims = s2.claims :+ State.Claim.Imply(ISZ(prop,
                    State.Claim.And(ops.ISZOps(s4t.claims).slice(s2.claims.size + 1, s4t.claims.size)))))
                  r = r :+ s4
                }
                for (s6t <- s6s) {
                  val s6 = s6t(claims = s2.claims :+ State.Claim.Imply(ISZ(negProp,
                    State.Claim.And(ops.ISZOps(s6t.claims).slice(s2.claims.size + 1, s6t.claims.size)))))
                  r = r :+ s6
                }
              } else {
                for (s4 <- s4s; s6 <- s6s) {
                  r = r :+ mergeStates(s2, cond, s4, s6, s6NextFresh)
                }
              }
            case (T, F) =>
              for (s4 <- s4s) {
                r = r :+ s4(status = s4.status && !reporter.hasError, nextFresh = s6NextFresh)
              }
            case (F, T) =>
              for (s6 <- s6s) {
                r = r :+ s6(status = s6.status && !reporter.hasError)
              }
            case _ =>
              for (s4 <- s4s; s6 <- s6s) {
                val s7 = mergeStates(s2, cond, s4, s6, s6NextFresh)
                r = r :+ s7(status = F)
              }
          }
        }
      } else {
        r = r :+ s1
      }
    }
    return r
  }

  def evalExprInvoke(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, stmt: AST.Stmt, e: AST.Exp.Invoke, reporter: Reporter): ISZ[(State, State.Value)] = {
    logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
    e.attr.resOpt.get match {
      case AST.ResolvedInfo.BuiltIn(kind) =>
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.Assert =>
            val (s0, v) = evalAssert(smt2, T, "Assertion", state, e.args(0), reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.AssertMsg =>
            val (s0, v) = evalAssert(smt2, T, "Assertion", state, e.args(0), reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.Assume =>
            val (s0, v) = evalAssume(smt2, T, "Assumption", state, e.args(0), reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.AssumeMsg =>
            val (s0, v) = evalAssume(smt2, T, "Assumption", state, e.args(0), reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.Halt =>
            val s0 = state(status = F)
            reporter.halted(e.posOpt, s0)
            return ISZ((s0, State.errorValue))
          case _ => halt(s"TODO: $stmt") // TODO
        }
      case _ =>
        return for (p <- evalExp(split, smt2, rtCheck, state, e, reporter)) yield (Logika.conjunctClaimSuffix(state, p._1), p._2)
    }
  }

  def evalStmt(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, stmt: AST.Stmt, reporter: Reporter): ISZ[State] = {
    if (!state.status) {
      return ISZ(state)
    }

    def evalAssignLocal(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: AST.AssignExp, lhsType: AST.Typed,
                        idPos: Position): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, lhsType, rtCheck, s0, rhs, reporter)) {
        val (s1, init) = p
        if (s1.status) {
          val (s2, sym) = value2Sym(s1, init, rhs.asStmt.posOpt.get)
          r = r :+ Logika.conjunctClaimSuffix(s0, evalAssignLocalH(decl, s2, lcontext, id, sym, idPos))
        } else {
          r = r :+ s1
        }
      }
      return r
    }

    def evalAssign(s0: State, assignStmt: AST.Stmt.Assign): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, assignStmt.lhs.typedOpt.get, rtCheck, s0, assignStmt.rhs, reporter)) {
        val (s1, init) = p
        if (s1.status) {
          val (s2, sym) = value2Sym(s1, init, assignStmt.rhs.asStmt.posOpt.get)
          r = r ++ (for (s3 <- assignRec(split, smt2, s2, assignStmt.lhs, sym, reporter)) yield Logika.conjunctClaimSuffix(s0, s3))
        } else {
          r = r :+ s1
        }
      }
      return r
    }

    def evalFor(s0: State, forStmt: AST.Stmt.For): ISZ[State] = {
      var r = ISZ[State]()

      def evalStep(s1: State, idSym: State.Value.Sym, step: AST.EnumGen.Range.Step): (ISZ[State], ISZ[State]) = {
        var done = ISZ[State]()
        var loop = ISZ[State]()
        for (p1 <- evalExp(split, smt2, rtCheck, s1, step.start, reporter);
             p2 <- evalExp(split, smt2, rtCheck, p1._1, step.end, reporter)) {
          val (_, start) = p1
          val (s3, end) = p2
          val s4vs: ISZ[(State, Option[State.Value])] = step.byOpt match {
            case Some(e) => for (p3 <- evalExp(split, smt2, rtCheck, s3, e, reporter)) yield (p3._1, Some(p3._2))
            case _ => ISZ((s3, None()))
          }
          for (p3 <- s4vs) {
            val (s4, _) = p3
            val (s5, lb) = s4.freshSym(AST.Typed.b, step.start.posOpt.get)
            val (s6, ub) = s5.freshSym(AST.Typed.b, step.end.posOpt.get)
            val (s7, lub) = s6.freshSym(AST.Typed.b, step.attr.posOpt.get)
            val s8 = s7.addClaim(State.Claim.Let.Binary(lb, start, AST.Exp.BinaryOp.Le, idSym, start.tipe))
            val s9 = s8.addClaim(State.Claim.Let.Binary(lb, idSym,
              if (step.isInclusive) AST.Exp.BinaryOp.Le else AST.Exp.BinaryOp.Lt, end, start.tipe))
            val s10 = s9.addClaim(State.Claim.Let.Binary(lub, lb, AST.Exp.BinaryOp.And, ub, AST.Typed.b))
            done = done :+ s10.addClaim(State.Claim.Prop(F, lub))
            loop = loop :+ s10.addClaim(State.Claim.Prop(T, lub))
          }
        }
        return (loop, done)
      }

      def evalEach(s1: State, enumGen: AST.EnumGen.Range.Expr): (ISZ[State], ISZ[State]) = {
        halt("TODO") // TODO
      }

      def evalEnumGen(s1: State, enumGen: AST.EnumGen.For): (ISZ[State], ISZ[State]) = {
        var done = ISZ[State]()
        var loop = ISZ[State]()
        enumGen.range match {
          case range: AST.EnumGen.Range.Step =>
            val pos: Position = enumGen.idOpt match {
              case Some(id) => id.attr.posOpt.get
              case _ => range.attr.posOpt.get
            }
            val (s2, idSym) = s1.freshSym(range.start.typedOpt.get, pos)
            val (s3, num) = s2.fresh
            val (ds, ls) = evalStep(s3, idSym, range)
            val ctx = context.methodOpt.get.name
            enumGen.idOpt match {
              case Some(id) =>
                for (d <- ds) {
                  done = done :+ d.addClaim(State.Claim.Let.Id(idSym, ctx, id.value, num, ISZ(pos)))
                }
                for (l <- ls) {
                  loop = loop :+ l.addClaim(State.Claim.Let.CurrentId(F, idSym, ctx, id.value, Some(pos)))
                }
              case _ =>
                done = done ++ ds
                loop = loop ++ ls
            }
          case range: AST.EnumGen.Range.Expr =>
            halt("TODO") // TODO
        }
        return (loop, done)
      }

      halt("TODO") // TODO

      //return r
    }

    def evalWhile(s0: State, whileStmt: AST.Stmt.While): ISZ[State] = {
      var r = ISZ[State]()
      for (s0w <- checkExps(split, smt2, F, "Loop invariant", " at the beginning of while-loop", s0,
        whileStmt.invariants, reporter)) {
        if (s0w.status) {
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
              srw = srw1(claims = srw1.claims :+ State.Claim.Let.CurrentId(F, sym, res.context, res.id, Some(pos)))
            }
            srw
          }
          val s2 = State(T, s0R.claims ++ (for (i <- s0.claims.size until s1.claims.size) yield s1.claims(i)), s0R.nextFresh)
          for (p <- evalExp(split, smt2, rtCheck, s2, whileStmt.cond, reporter)) {
            val (s3, v) = p
            val pos = whileStmt.cond.posOpt.get
            val (s4, cond) = value2Sym(s3, v, pos)
            val prop = State.Claim.Prop(T, cond)
            val thenClaims = s4.claims :+ prop
            val thenSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
              pos, thenClaims, reporter)
            var nextFresh: Z = s4.nextFresh
            if (thenSat) {
              for (s5 <- evalStmts(split, smt2, None(), rtCheck, s4(claims = thenClaims), whileStmt.body.stmts, reporter)) {
                if (s5.status) {
                  for (s6 <- checkExps(split, smt2, F, "Loop invariant", " at the end of while-loop",
                    s5, whileStmt.invariants, reporter)) {
                    if (nextFresh < s6.nextFresh) {
                      nextFresh = s6.nextFresh
                    }
                  }
                } else {
                  if (nextFresh < s5.nextFresh) {
                    nextFresh = s5.nextFresh
                  }
                }
              }
            }
            val negProp = State.Claim.Prop(F, cond)
            val elseClaims = s4.claims :+ negProp
            val elseSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
              pos, elseClaims, reporter)
            r = r :+ State(status = elseSat, claims = elseClaims, nextFresh = nextFresh)
          }
        } else {
          r = r :+ s0w
        }
      }
      return r
    }

    @pure def loopBound(ids: ISZ[String]): Z = {
      return config.loopBounds.get(LoopId(ids)).getOrElse(config.defaultLoopBound)
    }

    def evalWhileUnroll(sp: Split.Type, s0: State, whileStmt: AST.Stmt.While): ISZ[State] = {
      val loopId: ISZ[String] = whileStmt.context

      def whileRec(current: State, numLoops: Z): ISZ[State] = {
        if (!current.status) {
          return ISZ(current)
        }
        var r = ISZ[State]()
        for (s1 <- checkExps(sp, smt2, F, "Loop invariant", " at the beginning of while-loop", current,
          whileStmt.invariants, reporter)) {
          if (s1.status) {
            for (p <- evalExp(sp, smt2, rtCheck, s1, whileStmt.cond, reporter)) {
              val (s2, v) = p
              val pos = whileStmt.cond.posOpt.get
              val (s2w, cond) = value2Sym(s2, v, pos)
              val s3 = Logika.conjunctClaimSuffix(current, s2w)
              val prop = State.Claim.Prop(T, cond)
              val thenClaims = s3.claims :+ prop
              val thenSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
                pos, thenClaims, reporter)
              for (s4 <- evalStmts(sp, smt2, None(), rtCheck, s3(claims = thenClaims), whileStmt.body.stmts, reporter)) {
                val s6s: ISZ[State] = if (s4.status) {
                  val bound = loopBound(loopId)
                  if (bound <= 0 || numLoops + 1 < loopBound(loopId)) {
                    whileRec(s4(status = thenSat), numLoops + 1)
                  } else {
                    if (bound > 0) {
                      warn(whileStmt.cond.posOpt, s"Under-approximation due to loop unrolling capped with bound $bound",
                        reporter)
                      ISZ(s4(status = F))
                    } else {
                      ISZ(s4)
                    }
                  }
                } else {
                  ISZ(s4)
                }
                val nextFresh = maxStatesNextFresh(s6s)
                for (s6 <- s6s) {
                  val negProp = State.Claim.Prop(F, cond)
                  val elseClaims = s3.claims :+ negProp
                  val elseSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
                    pos, elseClaims, reporter)
                  (thenSat, elseSat) match {
                    case (T, T) =>
                    if (s6.status) {
                      r = r :+ mergeStates(s3, cond, s6, s3, nextFresh)
                    } else {
                      val claimsOps = ops.ISZOps(s3.claims)
                      r = r :+ s3(status = s3.status && !reporter.hasError, nextFresh = nextFresh,
                        claims = claimsOps.slice(0, s3.claims.size - 1) :+
                          State.Claim.Imply(ISZ(negProp, s3.claims(s3.claims.size - 1))))
                    }
                    case (T, F) => r = r :+ s6(status = s6.status && !reporter.hasError, nextFresh = nextFresh)
                    case (F, T) => r = r :+ s3(status = s3.status && !reporter.hasError, nextFresh = nextFresh)
                    case _ =>
                      val s7 = mergeStates(s3, cond, s6, s3, nextFresh)
                      r = r :+ s7(status = F)
                  }
                }
              }
            }
          } else {
            r = r :+ s1
          }
        }
        return r
      }

      return whileRec(s0, 0)
    }

    def evalReturn(s0: State, returnStmt: AST.Stmt.Return): ISZ[State] = {
      returnStmt.expOpt match {
        case Some(exp) =>
          var r = ISZ[State]()
          for (p <- evalExp(split, smt2, rtCheck, s0, exp, reporter)) {
            val (s1, v) = p
            val pos = exp.posOpt.get
            val (s2, sym) = value2Sym(s1, v, pos)
            r = r :+ Logika.conjunctClaimSuffix(s0,
              s2.addClaim(State.Claim.Let.CurrentId(F, sym, context.methodOpt.get.name, "Res", Some(pos))))
          }
          return r
        case _ => return ISZ(state)
      }
    }

    def evalSpecBlock(sp: Split.Type, s0: State, block: AST.Stmt.SpecBlock): ISZ[State] = {
      return evalBlock(sp, smt2, None(), rtCheck, s0, block.block, reporter)
    }

    def evalStmtH(): ISZ[State] = {
      stmt match {
        case stmt@AST.Stmt.Expr(e: AST.Exp.Invoke) =>
          return for (p <- evalExprInvoke(split, smt2, rtCheck, state, stmt, e, reporter)) yield p._1
        case stmt: AST.Stmt.Var if stmt.initOpt.nonEmpty =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          stmt.attr.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              return evalAssignLocal(T, state, res.context, res.id, stmt.initOpt.get, stmt.attr.typedOpt.get,
                stmt.id.attr.posOpt.get)
            case _ => halt(s"TODO: $stmt") // TODO
          }
        case stmt: AST.Stmt.Assign =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalAssign(state, stmt)
        case stmt: AST.Stmt.If =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalIf(split, smt2, None(), rtCheck, state, stmt, reporter)
        case stmt: AST.Stmt.While =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          if (stmt.modifies.nonEmpty) {
            return evalWhile(state, stmt)
          } else {
            if (!config.unroll) {
              error(stmt.posOpt, "Modifies clause is required when loop unrolling is disabled", reporter)
              return ISZ(state(status = F))
            }
            return evalWhileUnroll(split, state, stmt)
          }
        case stmt: AST.Stmt.For =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          if (stmt.modifies.nonEmpty) {
            return evalFor(state, stmt)
          } else {
            halt("TODO") // TODO
          }
        case stmt: AST.Stmt.Return =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalReturn(state, stmt)
        case stmt: AST.Stmt.Block => return evalBlock(split, smt2, None(), rtCheck, state, stmt, reporter)
        case stmt: AST.Stmt.SpecBlock => return evalSpecBlock(split, state, stmt)
        case stmt: AST.Stmt.Match => return evalMatch(split, smt2, None(), rtCheck, state, stmt, reporter)
        case _: AST.Stmt.Object => return ISZ(state)
        case _: AST.Stmt.Import => return ISZ(state)
        case _: AST.Stmt.Method => return ISZ(state)
        case _: AST.Stmt.SpecMethod => return ISZ(state)
        case stmt: AST.Stmt.Var if stmt.isSpec => return ISZ(state)
        case _: AST.Stmt.SpecVar => return ISZ(state)
        case _: AST.Stmt.Enum => return ISZ(state)
        case _: AST.Stmt.Adt => return ISZ(state)
        case _: AST.Stmt.Sig => return ISZ(state)
        case _ =>
          halt(s"TODO: $stmt") // TODO
      }
    }

    def checkSplits(): ISZ[State] = {
      val ss = evalStmtH()
      assert(ss.size > 0)
      var nextFresh: Z = -1
      for (s <- ss if nextFresh == -1) {
        if (s.status) {
          nextFresh = s.nextFresh
        }
      }
      assert(ss.size == 1 || ops.ISZOps(ss).forall((s: State) => !s.status || nextFresh == s.nextFresh))
      return ss
    }

    return extension.Cancel.cancellable(checkSplits _)
  }

  def logPc(enabled: B, raw: B, state: State, reporter: Reporter, posOpt: Option[Position]): Unit = {
    reporter.state(posOpt, state)
    if (enabled || raw) {
      val sts: ISZ[ST] =
        if (raw) State.Claim.claimsRawSTs(state.claims)
        else State.Claim.claimsSTs(state.claims, ClaimDefs.empty)
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

  def checkExp(split: Split.Type, smt2: Smt2, rtCheck: B, title: String, titleSuffix: String, s0: State, exp: AST.Exp, reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    for (p <- evalExp(split, smt2, rtCheck, s0, exp, reporter)) {
      val (s1, v) = p
      val pos = exp.posOpt.get
      val (s2, sym) = value2Sym(s1, v, pos)
      val prop = State.Claim.Prop(T, sym)
      val rvalid = smt2.valid(config.logVc, config.logVcDirOpt, s"$title at [${pos.beginLine}, ${pos.beginColumn}]",
        pos, s2.claims, prop, timeoutInMs, reporter)
      var ok = F
      rvalid.kind match {
        case Smt2Query.Result.Kind.Unsat => ok = T
        case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
        case Smt2Query.Result.Kind.Unknown => error(Some(pos), s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds$titleSuffix", reporter)
        case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
        case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
      }
      if (ok) {
        r = r :+ s2.addClaim(prop)
      } else {
        r = r :+ s2(status = F, claims = s2.claims :+ prop)
      }
    }
    return r
  }

  def checkExps(split: Split.Type, smt2: Smt2, rtCheck: B, title: String, titleSuffix: String, s0: State, exps: ISZ[AST.Exp], reporter: Reporter): ISZ[State] = {
    var currents = ISZ(s0)
    var done = ISZ[State]()
    for (exp <- exps) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.status) {
          currents = currents ++ checkExp(split, smt2, rtCheck, title, titleSuffix, current, exp, reporter)
        } else {
          done = done :+ current
        }
      }
    }
    return currents ++ done
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

  def evalStmts(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, state: State, stmts: ISZ[AST.Stmt],
                reporter: Reporter): ISZ[State] = {
    var currents = ISZ(state)
    var done = ISZ[State]()

    val size: Z = if (rOpt.nonEmpty) stmts.size - 1 else stmts.size
    for (i <- 0 until size) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.status) {
          currents = currents ++ evalStmt(split, smt2, rtCheck, current, stmts(i), reporter)
        } else {
          done = done :+ current
        }
      }
    }

    if (rOpt.nonEmpty) {
      return (for (current <- currents;
                   s <- evalAssignExp(split, smt2, rOpt, rtCheck, current, stmts(stmts.size - 1).asAssignExp, reporter))
        yield s) ++ done
    } else {
      return currents ++ done
    }
  }

  def evalBody(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, state: State, body: AST.Body,
               reporter: Reporter): ISZ[State] = {
    val s0 = state
    var r = ISZ[State]()
    for (s1 <- evalStmts(split, smt2, rOpt, rtCheck, s0, body.stmts, reporter)) {
      if (s1.status) {
        r = r :+ Logika.rewriteLocalVars(s1, body.undecls)
      } else {
        r = r :+ s1
      }
    }
    return r
  }

  @pure def singleStateValue(ps: ISZ[(State, State.Value)]): (State, State.Value) = {
    assert(ps.size == 1)
    return ps(0)
  }

  @pure def singleState(ss: ISZ[State]): State = {
    assert (ss.size == 1)
    return ss(0)
  }

  @pure def maxStatesNextFresh(ss: ISZ[State]): Z = {
    var r = ss(0).nextFresh
    if (ss.size > 1) {
      for (i <- 1 until ss.size) {
        val nf = ss(i).nextFresh
        if (r < nf) {
          r = nf
        }
      }
    }
    return r
  }

  @pure def maxStateValuesNextFresh(svs: ISZ[(State, State.Value)]): Z = {
    var r = svs(0)._1.nextFresh
    if (svs.size > 1) {
      for (i <- 1 until svs.size) {
        val nf = svs(i)._1.nextFresh
        if (r < nf) {
          r = nf
        }
      }
    }
    return r
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
