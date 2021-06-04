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
import org.sireum.message.Position
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.State.Claim
import org.sireum.logika.State.Claim.Let
import org.sireum.logika.State.Claim.Let.Quant

@record class ClaimSTs(var value: ISZ[ST]) {
  def add(st: ST): Unit = {
    value = value :+ st
  }
}

@record class ClaimDefs(var value: HashMap[Z, ISZ[State.Claim.Def]]) {
  def addDef(d: State.Claim.Def): Unit = {
    value.get(d.sym.num) match {
      case Some(s) => value = value + d.sym.num ~> (s :+ d)
      case _ => value = value + d.sym.num ~> ISZ(d)
    }
  }
  def hasDef(d: State.Claim.Def): B = {
    return value.contains(d.sym.num)
  }
}

object ClaimDefs {
  @strictpure def empty: ClaimDefs = ClaimDefs(HashMap.empty)

  def collectDefs(claim: State.Claim, defs: ClaimDefs): Unit = {
    def rec(c: State.Claim): Unit = {
      c match {
        case c: State.Claim.Let.CurrentId =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Let.CurrentName =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Let.Id =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Let.Name =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Def => defs.addDef(c)
        case _ =>
      }
      c match {
        case c: State.Claim.Composite =>
          for (cc <- c.claims) {
            rec(cc)
          }
        case _ =>
      }
    }
    rec(claim)
  }

}

object Util {
  @record class LetCollector(var value: HashMap[Z, HashSet[State.Claim.Let]]) extends MStateTransformer {

    override def preStateClaim(o: State.Claim): MStateTransformer.PreResult[State.Claim] = {
      o match {
        case o: State.Claim.Let.Binary if Smt2.imsOps.contains(o.op) => return super.preStateClaim(o)
        case o: State.Claim.Let.CurrentId if o.declId => return super.preStateClaim(o)
        case o: State.Claim.Let =>
          val key = o.sym.num
          val s = value.get(key).getOrElse(HashSet.empty) + o
          value = value + key ~> s
          return MStateTransformer.PreResult(F, MNone())
        case _ =>
          return super.preStateClaim(o)
      }
    }
  }

  @record class UsedSymsCurrentDeclIdCollector(var syms: HashSet[State.Value.Sym],
                                               var currentDeclIds: ISZ[State.Claim.Let.CurrentId]) extends MStateTransformer {
    override def preStateClaimLetQuant(o: State.Claim.Let.Quant): MStateTransformer.PreResult[State.Claim.Let] = {
      syms = syms + o.sym
      return MStateTransformer.PreResult(T, MNone())
    }

    override def preStateValueSym(o: State.Value.Sym): MStateTransformer.PreResult[State.Value] = {
      syms = syms + o
      return super.preStateValueSym(o)
    }

    override def preStateClaimLetCurrentId(o: State.Claim.Let.CurrentId): MStateTransformer.PreResult[State.Claim.Let] = {
      if (o.declId) {
        currentDeclIds = currentDeclIds :+ o
      }
      return super.preStateClaimLetCurrentId(o)
    }
  }

  @datatype class CurrentIdPossCollector(context: ISZ[String], id: String) extends StateTransformer.PrePost[Set[Position]] {
    override def preStateClaimLetCurrentId(ctx: Set[Position],
                                           o: State.Claim.Let.CurrentId): StateTransformer.PreResult[Set[Position], State.Claim.Let] = {
      return if (o.defPosOpt.nonEmpty && o.context == context && o.id == id) StateTransformer.PreResult(ctx + o.defPosOpt.get, T, None())
      else StateTransformer.PreResult(ctx, T, None())
    }
  }

  @datatype class CurrentNamePossCollector(ids: ISZ[String]) extends StateTransformer.PrePost[ISZ[Position]] {
    override def preStateClaimLetCurrentName(ctx: ISZ[Position],
                                             o: State.Claim.Let.CurrentName): StateTransformer.PreResult[ISZ[Position], State.Claim.Let] = {
      return if (o.defPosOpt.nonEmpty && o.ids == ids) StateTransformer.PreResult(ctx :+ o.defPosOpt.get, T, None())
      else StateTransformer.PreResult(ctx, T, None())
    }
  }

  @datatype class CurrentIdRewriter(map: HashMap[(ISZ[String], String), (ISZ[Position], Z)])
    extends StateTransformer.PrePost[B] {

    override def preStateClaimLetCurrentId(ctx: B,
                                           o: State.Claim.Let.CurrentId): StateTransformer.PreResult[B, State.Claim.Let] = {
      map.get((o.context, o.id)) match {
        case Some((poss, num)) =>
          return StateTransformer.PreResult(ctx, T, Some(State.Claim.Let.Id(o.sym, o.context, o.id, num, poss)))
        case _ =>
          return StateTransformer.PreResult(ctx, T, None())
      }
    }
  }

  @datatype class CurrentNameRewriter(map: HashMap[ISZ[String], (ISZ[Position], Z)])
    extends StateTransformer.PrePost[HashMap[ISZ[String], State.Value.Sym]] {
    override def preStateClaimLetCurrentName(ctx: HashMap[ISZ[String], State.Value.Sym],
                                             o: State.Claim.Let.CurrentName): StateTransformer.PreResult[HashMap[ISZ[String], State.Value.Sym], State.Claim.Let] = {
      map.get(o.ids) match {
        case Some((poss, num)) => return StateTransformer.PreResult(ctx + o.ids ~> o.sym,
          T, Some(State.Claim.Let.Name(o.sym, o.ids, num, poss)))
        case _ => return StateTransformer.PreResult(ctx, T, None())
      }
    }
  }

  def collectLetClaims(enabled: B, claims: ISZ[State.Claim]): HashMap[Z, ISZ[State.Claim.Let]] = {
    if (enabled) {
      val lc = LetCollector(HashMap.empty)
      for (c <- claims) {
        lc.transformStateClaim(c)
      }
      return HashMap.empty[Z, ISZ[State.Claim.Let]] ++ (for (p <- lc.value.entries) yield (p._1, p._2.elements))
    } else {
      return HashMap.empty
    }
  }

  def value2ST(smt2: Smt2, lets: HashMap[Z, ISZ[State.Claim.Let]]): State.Value => ST = {
    if (lets.isEmpty) {
      return smt2.v2ST _
    }
    var cache = HashMap.empty[Z, ST]
    def sv2ST(v: State.Value): ST = {
      v match {
        case v: State.Value.Sym =>
          cache.get(v.num) match {
            case Some(r) => return r
            case _ =>
              val r: ST = lets.get(v.num) match {
                case Some(ls) if ls.size == 1 => smt2.l2RhsST(ls(0), sv2ST _, lets)
                case _ => smt2.v2ST(v)
              }
              cache = cache + v.num ~> r
              return r
          }
        case _ => return smt2.v2ST(v)
      }
    }
    return sv2ST _
  }


  def logikaMethod(th: TypeHierarchy, config: Config, name: ISZ[String], inPfc: B, receiverTypeOpt: Option[AST.Typed],
                   params: ISZ[(AST.Id, AST.Typed)], posOpt: Option[Position], reads: ISZ[AST.Exp.Ident],
                   modifies: ISZ[AST.Exp.Ident], caseLabels: ISZ[AST.Exp.LitString], plugins: ISZ[plugin.Plugin]): Logika = {
    val mctx = Context.Method(name, receiverTypeOpt, params, reads, modifies, HashMap.empty, HashMap.empty,
      HashMap.empty, posOpt)
    val ctx = Context.empty(methodOpt = Some(mctx), caseLabels = caseLabels)
    return Logika(th, config, ctx, inPfc, plugins)
  }

  def checkInv(isPre: B, state: State, logika: Logika, smt2: Smt2, invs: ISZ[lang.symbol.Info.Inv], posOpt: Option[Position], reporter: Reporter): State = {
    var s0 = state
    for (inv <- invs) {
      var i = 0
      val id = inv.ast.id.value
      val isSingle = inv.ast.claims.size == 1
      val methodName: String =
        if (logika.context.methodName.size == 1) logika.context.methodName(0)
        else if (logika.context.methodOpt.get.receiverTypeOpt.isEmpty) st"${(logika.context.methodName, ".")}".render
        else st"${(ops.ISZOps(logika.context.methodName).dropRight(1), ".")}#${logika.context.methodName(0)}".render
      if (isPre) {
        for (claim <- inv.ast.claims if s0.status) {
          val title: String =
            if (isSingle) s"Method $methodName pre-invariant $id"
            else s"Method $methodName pre-invariant $id#$i"
          s0 = logika(context = logika.context(implicitCheckOpt = Some(s"$title: "))).evalAssume(smt2, T, title, s0,
            claim, posOpt, reporter)._1
          i = i + 1
        }
      } else {
        for (claim <- inv.ast.claims if s0.status) {
          val title: String =
            if (isSingle) s"Method $methodName post-invariant $id"
            else s"Method $methodName post-invariant $id#$i"
          s0 = logika(context = logika.context(implicitCheckOpt = Some(s"$title: "))).evalAssert(smt2, T, title, s0,
            claim, posOpt, reporter)._1
          i = i + 1
        }
      }
    }
    val s0Ops = ops.ISZOps(s0.claims)
    return s0(claims = s0Ops.slice(0, state.claims.size) :+ State.Claim.And(
      s0Ops.slice(state.claims.size, s0.claims.size)
    ))
  }

  def checkMethod(th: TypeHierarchy,
                  plugins: ISZ[plugin.Plugin],
                  method: AST.Stmt.Method,
                  config: Config,
                  smt2: Smt2,
                  reporter: Reporter): Unit = {
    def checkCase(labelOpt: Option[AST.Exp.LitString], reads: ISZ[AST.Exp.Ident], requires: ISZ[AST.Exp],
                  modifies: ISZ[AST.Exp.Ident], ensures: ISZ[AST.Exp]): Unit = {
      var state = State.create
      labelOpt match {
        case Some(label) if label.value != "" => state = state.addClaim(State.Claim.Label(label.value, label.posOpt.get))
        case _ =>
      }
      val res = method.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val logika: Logika = {
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
        val l = logikaMethod(th, config, mname, F, receiverTypeOpt, method.sig.paramIdTypes, method.posOpt, reads, modifies,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get), plugins)
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
      val statePreReqInvSize = state.claims.size
      if (logika.context.methodName.size == 1 && !method.isHelper) {
        state = checkInv(T, state, logika, smt2, th.worksheetInvs, method.posOpt, reporter)
      }
      val stmts = method.bodyOpt.get.stmts
      val hasPreReqInv = state.claims.size != statePreReqInvSize
      val statePreReqSize = state.claims.size
      for (r <- requires if state.status) {
        state = logika.evalAssume(smt2, T, "Precondition", state, r, r.posOpt, reporter)._1
      }
      if (state.claims.size != statePreReqSize) {
        val stateOps = ops.ISZOps(state.claims)
        state = state(claims = stateOps.slice(0, statePreReqSize) :+ State.Claim.And(
          stateOps.slice(statePreReqSize, state.claims.size)
        ))
      }
      if (hasPreReqInv && state.claims.size != statePreReqSize) {
        val stateOps = ops.ISZOps(state.claims)
        state = state(claims = stateOps.slice(0, statePreReqInvSize) :+ State.Claim.And(
          stateOps.slice(statePreReqInvSize, state.claims.size)
        ))
      }
      val ss: ISZ[State] = if (method.purity == AST.Purity.StrictPure) {
        val body = stmts(0).asInstanceOf[AST.Stmt.Var].initOpt.get
        logika.evalAssignExp(Split.Default, smt2, None(), T, state, body, reporter)
      } else {
        logika.evalStmts(Split.Default, smt2, None(), T, state, stmts, reporter)
      }
      for (s <- ss) {
        var s2 = s
        val statePreEnInvSize = state.claims.size
        if (logika.context.methodName.size == 1 && !method.isHelper) {
          s2 = checkInv(F, s2, logika, smt2, th.worksheetInvs, method.posOpt, reporter)
        }
        val hasPreEnInv = state.claims.size != statePreEnInvSize
        val statePreEnSize = state.claims.size
        for (e <- ensures if s2.status) {
          s2 = logika.evalAssert(smt2, T, "Postcondition", s2, e, e.posOpt, reporter)._1
        }
        if (state.claims.size != statePreEnSize) {
          val stateOps = ops.ISZOps(state.claims)
          state = state(claims = stateOps.slice(0, statePreEnSize) :+ State.Claim.And(
            stateOps.slice(statePreEnSize, state.claims.size)
          ))
        }
        if (hasPreEnInv && state.claims.size != statePreEnSize) {
          val stateOps = ops.ISZOps(state.claims)
          state = state(claims = stateOps.slice(0, statePreEnInvSize) :+ State.Claim.And(
            stateOps.slice(statePreEnInvSize, state.claims.size)
          ))
        }
        if (stmts.nonEmpty && s2.status) {
          logika.logPc(config.logPc, config.logRawPc, s2, reporter,
            Some(afterPos(stmts(stmts.size - 1).posOpt.get)))
        }
      }
    }

    method.contract match {
      case contract: AST.MethodContract.Simple =>
        checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures)
      case contract: AST.MethodContract.Cases =>
        for (c <- contract.cases) {
          checkCase(if (c.label.value === "") None() else Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
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
    return StateTransformer(CurrentIdPossCollector(lcontext, id)).transformState(Set.empty, s0).ctx.elements
  }

  def rewriteLocal(th: TypeHierarchy, s0: State, lcontext: ISZ[String], id: String, posOpt: Option[Position],
                   reporter: Reporter): State = {
    val poss = collectLocalPoss(s0, lcontext, id)
    if (poss.isEmpty) {
      reporter.error(posOpt, Logika.kind, s"Missing Modifies clause for $id")
      return s0(status = F)
    }
    val (s1, num) = s0.fresh
    val locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)] + (lcontext, id) ~> ((poss, num))
    val r = StateTransformer(CurrentIdRewriter(locals)).transformState(F, s1)
    val s2 = r.resultOpt.get
    return s2
  }

  def rewriteLocals(th: TypeHierarchy, s0: State, lcontext: ISZ[String], ids: ISZ[String]): State = {
    if (ids.isEmpty) {
      return s0
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
    val r = StateTransformer(CurrentIdRewriter(locals)).transformState(F, s1)
    return r.resultOpt.getOrElse(s1)
  }

  def rewriteLocalVars(th: TypeHierarchy, state: State, localVars: ISZ[AST.ResolvedInfo.LocalVar], posOpt: Option[Position], reporter: Reporter): State = {
    if (localVars.isEmpty) {
      return state
    }
    var current = state
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)]
    for (l <- localVars) {
      val poss = StateTransformer(CurrentIdPossCollector(l.context, l.id)).
        transformState(Set.empty, current).ctx.elements
      if (poss.isEmpty) {
        reporter.error(posOpt, Logika.kind, s"Missing Modifies clause for ${l.id}")
        return state(status = F)
      }
      val (s1, num) = current.fresh
      current = s1
      locals = locals + (l.context, l.id) ~> ((poss, num))
    }
    val r = StateTransformer(CurrentIdRewriter(locals)).transformState(F, current)
    current = r.resultOpt.get
    return current
  }

  def rewriteObjectVars(th: TypeHierarchy, state: State, objectVars: HashSMap[AST.ResolvedInfo.Var, (AST.Typed, Position)],
                        pos: Position, reporter: Reporter): State = {
    if (objectVars.isEmpty) {
      return state
    }
    var current = state
    var vars = HashMap.empty[ISZ[String], (ISZ[Position], Z)]
    for (l <- objectVars.keys) {
      val ids = l.owner :+ l.id
      val poss = StateTransformer(CurrentNamePossCollector(ids)).
        transformState(ISZ(), current).ctx
      if (poss.isEmpty) {
        reporter.error(Some(pos), Logika.kind, s"Missing Modifies clause for ${(l.owner, ".")}.${l.id}")
        return state(status = F)
      }
      val (s1, num) = current.fresh
      current = s1
      vars = vars + ids ~> ((poss, num))
    }
    val rt = StateTransformer(CurrentNameRewriter(vars)).transformState(HashMap.empty, current)
    current = rt.resultOpt.get
    for (p <- objectVars.entries) {
      val (x, (t, namePos)) = p
      val name =  x.owner :+ x.id
      val (s2, sym) = nameIntro(pos, current, name, t, Some(namePos))
      current = s2
      val tipe = sym.tipe
      if (!th.isMutable(tipe, T)) {
        val (s3, cond) = current.freshSym(AST.Typed.b, pos)
        current = s3.addClaims(ISZ(State.Claim.Let.Binary(cond, sym, AST.Exp.BinaryOp.Eq, rt.ctx.get(name).get, tipe),
          State.Claim.Prop(T, cond)))
      } else if (AST.Util.isSeq(tipe)) {
        val (s3, size1) = current.freshSym(AST.Typed.z, pos)
        val (s4, size2) = s3.freshSym(AST.Typed.z, pos)
        val (s5, cond) = s4.freshSym(AST.Typed.b, pos)
        val o1 = rt.ctx.get(name).get
        current = s5.addClaims(ISZ(
          State.Claim.Let.FieldLookup(size1, o1, "size"),
          State.Claim.Let.FieldLookup(size2, sym, "size"),
          State.Claim.Let.Binary(cond, size2, AST.Exp.BinaryOp.Eq, size1, AST.Typed.z),
          State.Claim.Prop(T, cond)
        ))
      }
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

  def strictPureMethod(th: TypeHierarchy, config: Config, plugins: ISZ[plugin.Plugin], smt2: Smt2, state: State,
                       receiverTypeOpt: Option[AST.Typed], funType: AST.Typed.Fun, owner: ISZ[String], id: String,
                       paramIds: ISZ[AST.Id], body: AST.AssignExp, reporter: Reporter): (State, State.ProofFun) = {
    val pf = State.ProofFun(receiverTypeOpt, owner, id, for (id <- paramIds) yield id.value, funType.args, funType.ret)
    if (smt2.strictPureMethods.contains(pf)) {
      return (state, pf)
    } else {
      val posOpt = body.asStmt.posOpt
      smt2.strictPureMethodsUp(smt2.strictPureMethods + pf ~> ((st"", st"")))
      val (res, prefix, svs): (State.Value.Sym, Z, ISZ[(State, State.Value)]) = {
        val context = pf.context :+ pf.id
        val logika: Logika = logikaMethod(th, config, context, T, pf.receiverTypeOpt,
          ops.ISZOps(paramIds).zip(funType.args), posOpt, ISZ(), ISZ(), ISZ(), plugins)
        val s0 = state(claims = ISZ())
        val (s1, r) = idIntro(posOpt.get, s0, context, "Res", funType.ret, posOpt)
        val split: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
        (r, s0.claims.size, logika.evalAssignExpValue(split, smt2, funType.ret, T, s1, body, reporter))
      }

      val pos = posOpt.get
      smt2.addStrictPureMethod(pos, pf, svs, res, prefix)

      val s1 = state(nextFresh = maxStateValuesNextFresh(svs))
      if (config.sat) {
        val title: String = s"the derived proof function of $id"
        if (!smt2.sat(config.logVc, config.logVcDirOpt, title, pos, s1.claims, reporter)) {
          reporter.error(posOpt, Logika.kind, "Unsatisfiable proof function derived from @strictpure method")
        }
      }
      return (s1, pf)
    }
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

  @record class VarSubstitutor(val context: ISZ[String], var hasThis: B,
                               var map: HashSMap[AST.ResolvedInfo, (AST.Exp, AST.Exp.Ident)])
    extends AST.MTransformer {
    def introIdent(o: AST.Exp, res: AST.ResolvedInfo, id: AST.Id, typedOpt: Option[AST.Typed]): MOption[AST.Exp] = {
      map.get(res) match {
        case Some((_, ident)) => return MSome(ident)
        case _ =>
          val lres = AST.ResolvedInfo.LocalVar(context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id.value)
          val ident = AST.Exp.Ident(id, AST.ResolvedAttr(id.attr.posOpt, Some(lres), typedOpt))
          map = map + res ~> ((o, ident))
          return MSome(ident)
      }
    }
    override def postExpIdent(o: AST.Exp.Ident): MOption[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Var =>
          if (res.isInObject) {
            return introIdent(o, res, o.id, o.typedOpt)
          } else {
            hasThis = T
          }
        case res: AST.ResolvedInfo.LocalVar => return introIdent(o, res, o.id, o.typedOpt)
        case _ =>
      }
      return super.postExpIdent(o)
    }

    override def postExpThis(o: AST.Exp.This): MOption[AST.Exp] = {
      hasThis = T
      return super.postExpThis(o)
    }

    override def postExpSelect(o: AST.Exp.Select): MOption[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Var if res.isInObject =>
          return introIdent(o, res, o.id, o.typedOpt)
        case _ =>
      }
      return super.postExpSelect(o)
    }
  }

  def evalExtractPureMethod(logika: Logika, smt2: Smt2, state: State, receiverTypeOpt: Option[AST.Typed],
                            owner: ISZ[String], id: String, exp: AST.Exp, reporter: Reporter): (State, State.Value) = {
    val posOpt = exp.posOpt
    val tOpt = exp.typedOpt
    val t = tOpt.get
    val vs = VarSubstitutor(owner :+ id, F, HashSMap.empty)
    val newExp = vs.transformExp(exp).getOrElse(exp)
    if (vs.hasThis || vs.map.nonEmpty) {
      var paramIds = ISZ[AST.Id]()
      var paramTypes = ISZ[AST.Typed]()
      var s0 = state
      var args = ISZ[State.Value]()
      if (vs.hasThis) {
        paramIds = paramIds :+ AST.Id("this", AST.Attr(posOpt))
        paramTypes = paramTypes :+ receiverTypeOpt.get
        val e = AST.Exp.This(AST.TypedAttr(posOpt, receiverTypeOpt))
        val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, T, s0, e, reporter)
        s0 = s1
        args = args :+ arg
      }
      for (pair <- vs.map.values) {
        val (e, paramIdent) = pair
        paramIds = paramIds :+ paramIdent.id
        paramTypes = paramTypes :+ paramIdent.typedOpt.get
        val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, T, s0, e, reporter)
        s0 = s1
        args = args :+ arg
      }
      val (s2, pf) = strictPureMethod(logika.th, logika.config, logika.plugins, smt2, s0, None(),
        AST.Typed.Fun(T, F, paramTypes, t), owner, id, paramIds,
        AST.Stmt.Expr(newExp, AST.TypedAttr(posOpt, tOpt)), reporter)
      val (s3, sym) = s2.freshSym(t, posOpt.get)
      return (s3.addClaim(State.Claim.Let.ProofFunApply(sym, pf, args)), sym)
    } else {
      return logika.evalExp(Split.Disabled, smt2, T, state, newExp, reporter)(0)
    }
  }
}