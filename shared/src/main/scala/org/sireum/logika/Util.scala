// #Sireum
/*
 Copyright (c) 2017-2021, Robby, Kansas State University
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
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.Logika.{Reporter, Split}

object Util {

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

  @record class UnsupportedFeatureDetector(val posOpt: Option[Position], val id: String, val reporter: Reporter) extends AST.MTransformer {
    override def preExpQuantEach(o: AST.Exp.QuantEach): AST.MTransformer.PreResult[AST.Exp.Quant] = {
      transformExp(o.seq)
      for (p <- o.fun.params) {
        transformExpFunParam(p)
      }
      transformAssignExp(o.fun.exp)
      return AST.MTransformer.PreResultExpQuantEach(continu = F)
    }

    override def preExpQuantType(o: AST.Exp.QuantType): AST.MTransformer.PreResult[AST.Exp.Quant] = {
      for (p <- o.fun.params) {
        transformExpFunParam(p)
      }
      transformAssignExp(o.fun.exp)
      return AST.MTransformer.PreResultExpQuantType(continu = F)
    }

    override def preExpQuantRange(o: AST.Exp.QuantRange): AST.MTransformer.PreResult[AST.Exp.Quant] = {
      transformExp(o.lo)
      transformExp(o.hi)
      for (p <- o.fun.params) {
        transformExpFunParam(p)
      }
      transformAssignExp(o.fun.exp)
      return AST.MTransformer.PreResultExpQuantRange(continu = F)
    }

    override def postTypeFun(o: AST.Type.Fun): MOption[AST.Type] = {
      val t = o.typedOpt.get.asInstanceOf[AST.Typed.Fun]
      if (reporter.messages.isEmpty && !t.isPureFun) {
        reporter.warn(posOpt, Logika.kind, s"Verification of $id was skipped due to impure function (currently unsupported): $t")
      }
      return AST.MTransformer.PostResultTypeFun
    }

    override def postExpFun(o: AST.Exp.Fun): MOption[AST.Exp] = {
      if (reporter.messages.isEmpty && !o.typedOpt.get.asInstanceOf[AST.Typed.Fun].isPureFun) {
        reporter.warn(posOpt, Logika.kind, s"Verification of $id was skipped due to impure function (currently unsupported): $o")
      }
      return AST.MTransformer.PostResultExpFun
    }

    override def postExpEta(o: AST.Exp.Eta): MOption[AST.Exp] = {
      if (reporter.messages.isEmpty && !o.typedOpt.get.asInstanceOf[AST.Typed.Fun].isPureFun) {
        reporter.warn(posOpt, Logika.kind, s"Verification of $id was skipped due to impure function (currently unsupported): $o")
      }
      return AST.MTransformer.PostResultExpEta
    }
  }

  @record class VarSubstitutor(val context: ISZ[String],
                               val receiverTypeOpt: Option[AST.Typed],
                               var hasThis: B,
                               var resultOpt: Option[(AST.Exp, AST.Exp.Ident)],
                               var map: HashSMap[AST.ResolvedInfo, (AST.Exp, AST.Exp.Ident)],
                               var inputMap: HashSMap[AST.ResolvedInfo, (AST.Exp, AST.Exp.Ident)])
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

    def introInputIdent(o: AST.Exp, res: AST.ResolvedInfo, id: AST.Id, typedOpt: Option[AST.Typed]): AST.MTransformer.PreResult[AST.Exp] = {
      inputMap.get(res) match {
        case Some((_, ident)) => return AST.MTransformer.PreResult(F, MSome(ident))
        case _ =>
          val inId = s"${id.value}.in"
          val lres = AST.ResolvedInfo.LocalVar(context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, inId)
          val ident = AST.Exp.Ident(id(value = inId), AST.ResolvedAttr(id.attr.posOpt, Some(lres), typedOpt))
          inputMap = inputMap + res ~> ((o, ident))
          return AST.MTransformer.PreResult(F, MSome(ident))
      }
    }

    override def preExpInput(o: AST.Exp.Input): AST.MTransformer.PreResult[AST.Exp] = {
      o.exp match {
        case exp: AST.Exp.Ident =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var => return introInputIdent(o, res, exp.id, exp.typedOpt)
            case res: AST.ResolvedInfo.LocalVar => return introInputIdent(o, res, exp.id, exp.typedOpt)
            case _ =>
          }
        case exp: AST.Exp.Select =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var if res.isInObject =>
              return introInputIdent(o, res, exp.id, exp.typedOpt)
            case _ =>
          }
        case _ =>
      }
      halt("Non-simple input")
    }

    override def postExpResult(o: AST.Exp.Result): MOption[AST.Exp] = {
      val id = AST.Id("return", AST.Attr(o.posOpt))
      val lres = AST.ResolvedInfo.LocalVar(context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id.value)
      val ident = AST.Exp.Ident(id, AST.ResolvedAttr(o.attr.posOpt, Some(lres), o.typedOpt))
      resultOpt = Some((o, ident))
      return MSome(ident)
    }

    override def postExpIdent(o: AST.Exp.Ident): MOption[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Var =>
          if (res.isInObject) {
            return introIdent(o, res, o.id, o.typedOpt)
          } else {
            hasThis = T
            val id = AST.Id("this", AST.Attr(o.posOpt))
            val lres = AST.ResolvedInfo.LocalVar(context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id.value)
            val ident = AST.Exp.Ident(id, AST.ResolvedAttr(o.attr.posOpt, Some(lres), receiverTypeOpt))
            return MSome(AST.Exp.Select(Some(ident), o.id, o.targs, o.attr))
          }
        case res: AST.ResolvedInfo.LocalVar => return introIdent(o, res, o.id, o.typedOpt)
        case _ =>
      }
      return AST.MTransformer.PostResultExpIdent
    }

    override def postExpThis(o: AST.Exp.This): MOption[AST.Exp] = {
      hasThis = T
      val id = AST.Id("this", AST.Attr(o.posOpt))
      val lres = AST.ResolvedInfo.LocalVar(context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id.value)
      val ident = AST.Exp.Ident(id, AST.ResolvedAttr(o.attr.posOpt, Some(lres), o.typedOpt))
      return MSome(ident)
    }

    override def postExpSelect(o: AST.Exp.Select): MOption[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Var if res.isInObject =>
          return introIdent(o, res, o.id, o.typedOpt)
        case _ =>
      }
      return AST.MTransformer.PostResultExpSelect
    }
  }

  @record class LetCollector(var value: HashMap[Z, HashSet[State.Claim.Let]]) extends MStateTransformer {

    override def preStateClaim(o: State.Claim): MStateTransformer.PreResult[State.Claim] = {
      o match {
        case o: State.Claim.Let.Binary if Smt2.imsOps.contains(o.op) => return MStateTransformer.PreResultStateClaimProp
        case o: State.Claim.Let.CurrentId if o.declId => return MStateTransformer.PreResultStateClaimProp
        case o: State.Claim.Let =>
          val key = o.sym.num
          val s = value.get(key).getOrElse(HashSet.empty) + o
          value = value + key ~> s
          return MStateTransformer.PreResult(F, MNone())
        case _ =>
          return MStateTransformer.PreResultStateClaimProp
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
      return MStateTransformer.PreResultStateValueSym
    }

    override def preStateClaimLetCurrentId(o: State.Claim.Let.CurrentId): MStateTransformer.PreResult[State.Claim.Let] = {
      if (o.declId) {
        currentDeclIds = currentDeclIds :+ o
      }
      return MStateTransformer.PreResultStateClaimLetCurrentId
    }
  }

  @datatype class CurrentIdPossCollector(val context: ISZ[String], val id: String) extends StateTransformer.PrePost[Set[Position]] {
    override def preStateClaimLetCurrentId(ctx: Set[Position],
                                           o: State.Claim.Let.CurrentId): StateTransformer.PreResult[Set[Position], State.Claim.Let] = {
      return if (o.defPosOpt.nonEmpty && o.context == context && o.id == id) StateTransformer.PreResult(ctx + o.defPosOpt.get, T, None())
      else StateTransformer.PreResult(ctx, T, None())
    }
  }

  @datatype class CurrentNamePossCollector(val ids: ISZ[String]) extends StateTransformer.PrePost[ISZ[Position]] {
    override def preStateClaimLetCurrentName(ctx: ISZ[Position],
                                             o: State.Claim.Let.CurrentName): StateTransformer.PreResult[ISZ[Position], State.Claim.Let] = {
      return if (o.defPosOpt.nonEmpty && o.ids == ids) StateTransformer.PreResult(ctx :+ o.defPosOpt.get, T, None())
      else StateTransformer.PreResult(ctx, T, None())
    }
  }

  @datatype class CurrentIdRewriter(val map: HashMap[(ISZ[String], String), (ISZ[Position], Z)])
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

  @datatype class CurrentNameRewriter(val map: HashMap[ISZ[String], (ISZ[Position], Z)])
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

  val builtInTypeNames: HashSet[ISZ[String]] = HashSet ++ ISZ(
    AST.Typed.bName, AST.Typed.zName, AST.Typed.cName, AST.Typed.stringName, AST.Typed.f32Name, AST.Typed.f64Name,
    AST.Typed.rName, AST.Typed.stName, AST.Typed.isName, AST.Typed.msName
  )

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


  def logikaMethod(th: TypeHierarchy, config: Config, name: ISZ[String], receiverTypeOpt: Option[AST.Typed],
                   params: ISZ[(AST.Id, AST.Typed)], retType: AST.Typed, posOpt: Option[Position], reads: ISZ[AST.Exp.Ident],
                   modifies: ISZ[AST.Exp.Ident], caseLabels: ISZ[AST.Exp.LitString], plugins: ISZ[plugin.Plugin],
                   implicitContext: Option[(String, Position)]): Logika = {
    val mctx = Context.Method(name, receiverTypeOpt, params, retType, reads, modifies, HashMap.empty, HashMap.empty,
      HashMap.empty, posOpt)
    val ctx = Context.empty(methodOpt = Some(mctx), caseLabels = caseLabels, implicitCheckTitlePosOpt = implicitContext)
    return Logika(th, config, ctx, plugins)
  }

  def checkInv(isPre: B, state: State, logika: Logika, smt2: Smt2, invs: ISZ[lang.symbol.Info.Inv],
               posOpt: Option[Position], substMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
    val methodName: String =
      if (logika.context.methodName.size == 1) logika.context.methodName(0)
      else if (logika.context.methodOpt.get.receiverTypeOpt.isEmpty) st"${(logika.context.methodName, ".")}".render
      else st"${(ops.ISZOps(logika.context.methodName).dropRight(1), ".")}#${logika.context.methodName(0)}".render
    val title: String = if (isPre) s"Method $methodName pre-invariant" else s"Method $methodName post-invariant"
    return checkInvs(logika, posOpt, isPre, title, smt2, T, state, logika.context.receiverTypeOpt, invs, substMap, reporter)
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
        val l = logikaMethod(th, config, mname, receiverTypeOpt, method.sig.paramIdTypes,
          method.sig.returnType.typedOpt.get, method.posOpt, reads, modifies,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get), plugins, None())
        val mctx = l.context.methodOpt.get
        var objectVarInMap = mctx.objectVarInMap
        var objectNames = HashSMap.empty[ISZ[String], Position]
        for (p <- (mctx.readObjectVarMap(TypeChecker.emptySubstMap) ++
          mctx.modObjectVarMap(TypeChecker.emptySubstMap).entries).entries) {
          val (ids, (t, posOpt)) = p
          val pos = posOpt.get
          val info = th.nameMap.get(ids).get.asInstanceOf[Info.Var]
          objectNames = objectNames + info.owner ~> pos
          val (s0, sym) = nameIntro(posOpt.get, state, ids, t, posOpt)
          state = assumeValueInv(l, smt2, T, s0, sym, pos, reporter)
          objectVarInMap = objectVarInMap + ids ~> sym
        }
        for (p <- objectNames.entries) {
          val (objectName, pos) = p
          state = assumeObjectInv(l, smt2, objectName, state, pos, reporter)
        }
        var fieldVarInMap = mctx.fieldVarInMap
        mctx.receiverTypeOpt match {
          case Some(receiverType) =>
            val (s0, thiz) = idIntro(method.sig.id.attr.posOpt.get, state, mname, "this", receiverType, method.sig.id.attr.posOpt)
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
          val (s0, sym) = idIntro(posOpt.get, state, mname, id.value, t, posOpt)
          state = assumeValueInv(l, smt2, T, s0, sym, posOpt.get, reporter)
          localInMap = localInMap + id.value ~> sym
        }
        l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
          localInMap = localInMap))))
      }
      val invs = logika.retrieveInvs(res.owner, res.isInObject)
      val statePreReqInvSize = state.claims.size
      state = checkInv(T, state, logika, smt2, invs, method.sig.id.attr.posOpt, TypeChecker.emptySubstMap, reporter)
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
        s2 = checkInv(F, s2, logika, smt2, invs, method.sig.id.attr.posOpt, TypeChecker.emptySubstMap, reporter)
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

    if (method.mcontract.isEmpty) {
      checkCase(None(), ISZ(), ISZ(), ISZ(), ISZ())
    } else {
      method.mcontract match {
        case contract: AST.MethodContract.Simple =>
          checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures)
        case contract: AST.MethodContract.Cases =>
          for (c <- contract.cases) {
            checkCase(if (c.label.value === "") None() else Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
          }
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

  def rewriteLocal(s0: State, lcontext: ISZ[String], id: String, posOpt: Option[Position], reporter: Reporter): State = {
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

  def rewriteLocals(s0: State, lcontext: ISZ[String], ids: ISZ[String]): State = {
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

  def rewriteLocalVars(state: State, localVars: ISZ[AST.ResolvedInfo.LocalVar], posOpt: Option[Position], reporter: Reporter): State = {
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

  def rewriteObjectVars(logika: Logika, smt2: Smt2, rtCheck: B, state: State,
                        objectVars: HashSMap[AST.ResolvedInfo.Var, (AST.Typed, Position)], pos: Position,
                        reporter: Reporter): State = {
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
      val name = x.owner :+ x.id
      val (s2, sym) = nameIntro(pos, current, name, t, Some(namePos))
      current = assumeValueInv(logika, smt2, rtCheck, s2, sym, namePos, reporter)
      val tipe = sym.tipe
      if (!logika.th.isMutable(tipe, T)) {
        val (s3, cond) = current.freshSym(AST.Typed.b, pos)
        current = s3.addClaims(ISZ(State.Claim.Let.Binary(cond, sym, AST.Exp.BinaryOp.Eq, rt.ctx.get(name).get, tipe),
          State.Claim.Prop(T, cond)))
      } else if (AST.Util.isSeq(tipe)) {
        val (s4, size1) = current.freshSym(AST.Typed.z, pos)
        val (s5, size2) = s4.freshSym(AST.Typed.z, pos)
        val (s6, cond) = s5.freshSym(AST.Typed.b, pos)
        val o1 = rt.ctx.get(name).get
        current = s6.addClaims(ISZ(
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
                       paramIds: ISZ[AST.Id], body: AST.AssignExp, reporter: Reporter,
                       implicitContextOpt: Option[(String, Position)]): (State, State.ProofFun) = {
    val pf = State.ProofFun(receiverTypeOpt, owner, id, for (id <- paramIds) yield id.value, funType.args, funType.ret)
    if (smt2.strictPureMethods.contains(pf)) {
      return (state, pf)
    } else {
      val posOpt = body.asStmt.posOpt
      val pos = posOpt.get
      val (res, svs, maxFresh): (State.Value.Sym, ISZ[(State, State.Value.Sym)], Z) = {
        val context = pf.context :+ pf.id
        val logika: Logika = logikaMethod(th, config, context,  pf.receiverTypeOpt,
          ops.ISZOps(paramIds).zip(funType.args), funType.ret, posOpt, ISZ(), ISZ(), ISZ(), plugins, implicitContextOpt)
        var s0 = state(claims = ISZ())
        val (s1, r) = idIntro(posOpt.get, s0, context, "Res", funType.ret, posOpt)
        ;{
          val s2 = assumeValueInv(logika, smt2, T, s1, r, pos, reporter)
          smt2.addStrictPureMethodDecl(pf, r, ops.ISZOps(s2.claims).slice(s1.claims.size, s2.claims.size))
          s0 = s1(nextFresh = s2.nextFresh)
        }
        for (pair <- ops.ISZOps(paramIds).zip(pf.paramTypes) if pair._1.value =!= "this") {
          val (pid, pt) = pair
          val (s0_1, pv) = idIntro(pos, s0, context, pid.value, pt, pid.attr.posOpt)
          val s0_2 = assumeValueInv(logika, smt2, T, s0_1, pv, pos, reporter)
          if (s0_2.claims.size > s0_1.claims.size) {
            s0 = s0_2
          }
        }
        val split: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
        val svs = logika.evalAssignExpValue(split, smt2, funType.ret, T, s0, body, reporter)
        var sss = ISZ[(State, State.Value.Sym)]()
        var maxFresh: Z = -1
        for (sv <- svs) {
          val (s, v) = sv
          val (s2, sym) = logika.value2Sym(s, v, pos)
          sss = sss :+ ((s2, sym))
          if (maxFresh < s2.nextFresh) {
            maxFresh = s2.nextFresh
          }
        }
        (r, sss, maxFresh)
      }

      smt2.addStrictPureMethod(pos, pf, svs, res, 0)

      val s1 = state(nextFresh = maxFresh)
      if (config.sat) {
        val title: String = s"the derived proof function of $id"
        if (!smt2.sat(T, config.logVc, config.logVcDirOpt, title, pos, s1.claims, reporter)) {
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

  def evalExtractPureMethod(logika: Logika, smt2: Smt2, state: State, receiverTypeOpt: Option[AST.Typed],
                            receiverOpt: Option[State.Value.Sym], owner: ISZ[String], id: String, exp: AST.Exp,
                            reporter: Reporter): (State, State.Value) = {
    val posOpt = exp.posOpt
    val tOpt = exp.typedOpt
    val t = tOpt.get
    val vs = VarSubstitutor(owner :+ id, receiverTypeOpt, F, None(), HashSMap.empty, HashSMap.empty)
    val newExp = vs.transformExp(exp).getOrElse(exp)
    if (vs.hasThis || vs.map.nonEmpty) {
      var paramIds = ISZ[AST.Id]()
      var paramTypes = ISZ[AST.Typed]()
      var s0 = state
      var args = ISZ[State.Value]()
      if (vs.hasThis) {
        receiverOpt match {
          case Some(receiver) =>
            paramIds = paramIds :+ AST.Id("this", AST.Attr(posOpt))
            paramTypes = paramTypes :+ receiverTypeOpt.get
            s0 = s0.addClaim(State.Claim.Let.CurrentId(T, receiver, logika.context.methodName, "this", None()))
            args = args :+ receiver
          case _ =>
            paramIds = paramIds :+ AST.Id("this", AST.Attr(posOpt))
            paramTypes = paramTypes :+ receiverTypeOpt.get
            val e = AST.Exp.This(AST.TypedAttr(posOpt, receiverTypeOpt))
            val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, T, s0, e, reporter)
            s0 = s1
            args = args :+ arg
        }
      }
      for (pair <- vs.map.values) {
        val (e, paramIdent) = pair
        paramIds = paramIds :+ paramIdent.id
        paramTypes = paramTypes :+ paramIdent.typedOpt.get
        val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, T, s0, e, reporter)
        s0 = s1
        args = args :+ arg
      }
      for (pair <- vs.inputMap.values) {
        val (e, paramIdent) = pair
        paramIds = paramIds :+ paramIdent.id
        paramTypes = paramTypes :+ paramIdent.typedOpt.get
        val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, T, s0, e, reporter)
        s0 = s1
        args = args :+ arg
      }
      vs.resultOpt match {
        case Some((_, ident)) =>
          paramIds = paramIds :+ ident.id
          paramTypes = paramTypes :+ ident.typedOpt.get
          val e = AST.Exp.Result(None(), AST.TypedAttr(posOpt, ident.typedOpt))
          val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, T, s0, e, reporter)
          s0 = s1
          args = args :+ arg
        case _ =>
      }
      val (s2, pf) = strictPureMethod(logika.th, logika.config, logika.plugins, smt2, s0, None(),
        AST.Typed.Fun(T, F, paramTypes, t), owner, id, paramIds,
        AST.Stmt.Expr(newExp, AST.TypedAttr(posOpt, tOpt)), reporter, logika.context.implicitCheckTitlePosOpt)
      val (s3, sym) = s2.freshSym(t, posOpt.get)
      val s4 = s3.addClaim(State.Claim.Let.ProofFunApply(sym, pf, args))
      val s4ClaimsOps = ops.ISZOps(s4.claims)
      val s5: State = if (vs.hasThis && receiverOpt.nonEmpty)
        s4(claims = s4ClaimsOps.slice(0, state.claims.size) ++ s4ClaimsOps.slice(state.claims.size + 1, s4.claims.size))
      else s4
      return (s5, sym)
    } else {
      return logika.evalExp(Split.Disabled, smt2, T, state, newExp, reporter)(0)
    }
  }

  @strictpure def strictPureClaimId(i: Z, pos: Position): String = s"claim_${i}_${pos.beginLine}_${pos.beginColumn}"

  def detectUnsupportedFeatures(stmt: AST.Stmt.Method): ISZ[message.Message] = {
    val ufd = UnsupportedFeatureDetector(stmt.sig.id.attr.posOpt, stmt.sig.id.value, Reporter.create)
    for (p <- stmt.sig.params) {
      p.tipe match {
        case t: AST.Type.Fun if t.isByName =>
          ufd.reporter.warn(ufd.posOpt, Logika.kind, s"Verification of ${ufd.id} was skipped due to impure function (currently unsupported): ${t.typedOpt.get}")
        case _ =>
      }
      ufd.transformParam(p)
    }
    ufd.transformMethodContract(stmt.contract)
    ufd.transformType(stmt.sig.returnType)
    stmt.bodyOpt match {
      case Some(body) => ufd.transformBody(body)
      case _ =>
    }
    return ufd.reporter.messages
  }

  @pure def invOwnerId(invs: ISZ[Info.Inv], typeArgsOpt: Option[ISZ[AST.Typed]]): (ISZ[String], String) = {
    val res = invs(0).resOpt.get.asInstanceOf[AST.ResolvedInfo.Inv]
    val tOpt: Option[ST] = typeArgsOpt match {
      case Some(typeArgs) if typeArgs.nonEmpty => Some(st"[${(typeArgs, ", ")}]")
      case _ => None()
    }
    val id = st"inv${if (res.isInObject) '.' else '#'}$tOpt".render
    return (res.owner, id)
  }

  def addObjectInv(logika: Logika, smt2: Smt2, name: ISZ[String], state: State, pos: Position,
                   reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    val invs = logika.retrieveInvs(name, T)
    if (invs.isEmpty) {
      return (state, ISZ())
    }
    val (owner, id) = invOwnerId(invs, None())
    val inv = logika.invs2exp(invs, HashMap.empty).get
    val (s0, v) = evalExtractPureMethod(logika, smt2, state, None(), None(), owner, id, inv, reporter)
    val (s1, sym) = logika.value2Sym(s0, v, pos)
    return (s1, ISZ(sym))
  }

  def assumeObjectInv(logika: Logika, smt2: Smt2, name: ISZ[String], state: State, pos: Position,
                   reporter: Reporter): State = {
    val (s0, conds) = addObjectInv(logika, smt2, name, state, pos, reporter)
    return s0.addClaims(for (cond <- conds) yield State.Claim.Prop(T, cond))
  }

  def addValueInv(logika: Logika, smt2: Smt2, rtCheck: B, state: State, receiver: State.Value.Sym, pos: Position,
                  reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    def addTupleInv(s0: State, t: AST.Typed.Tuple): (State, ISZ[State.Value.Sym]) = {
      var s1 = s0
      var i = 1
      var ss = ISZ[State.Value.Sym]()
      for (arg <- t.args) {
        val (s2, sym) = s1.freshSym(arg, pos)
        val s3 = s2.addClaim(State.Claim.Let.FieldLookup(sym, receiver, s"_$i"))
        val (s4, syms) = Util.addValueInv(logika, smt2, rtCheck, s3, sym, pos, reporter)
        ss = ss ++ syms
        s1 = s4
        i = i + 1
      }
      return (s1, ss)
    }
    def addSubZInv(s0: State, v: State.Value.Sym, ti: TypeInfo.SubZ): (State, ISZ[State.Value.Sym]) = {
      var s1 = s0
      var ss = ISZ[State.Value.Sym]()
      val t = ti.typedOpt.get
      if (ti.ast.hasMin) {
        val (s2, minCond) = s0.freshSym(AST.Typed.b, pos)
        s1 = s2.addClaim(State.Claim.Let.Binary(minCond, z2SubZVal(ti, ti.ast.min, pos),
          AST.Exp.BinaryOp.Le, v, t))
        ss = ss :+ minCond
      }
      if (ti.ast.hasMax) {
        val (s3, maxCond) = s1.freshSym(AST.Typed.b, pos)
        s1 = s3.addClaim(State.Claim.Let.Binary(maxCond, v, AST.Exp.BinaryOp.Le,
          z2SubZVal(ti, ti.ast.min, pos), t))
        ss = ss :+ maxCond
      }
      return (s1, ss)
    }
    val t = receiver.tipe
    val (ti, targs): (TypeInfo, ISZ[AST.Typed]) = t match {
      case t: AST.Typed.Name =>
        if (builtInTypeNames.contains(t.ids)) {
          return (state, ISZ())
        } else {
          (logika.th.typeMap.get(t.ids).get, t.args)
        }
      case t: AST.Typed.Tuple => return addTupleInv(state, t)
      case _: AST.Typed.Fun => return (state, ISZ())
      case _: AST.Typed.TypeVar => return (state, ISZ())
      case _ => halt(s"Infeasible: $t")
    }
    val ((owner, id), inv): ((ISZ[String], String), AST.Exp) = ti match {
      case ti: TypeInfo.SubZ =>
        return addSubZInv(state, receiver, ti)
      case ti: TypeInfo.Adt =>
        val is = ti.invariants.values
        if (ti.invariants.isEmpty) {
          return (state, ISZ())
        }
        val substMap = TypeChecker.buildTypeSubstMap(ti.owner, Some(pos), ti.ast.typeParams, targs, reporter).get
        logika.invs2exp(is, substMap) match {
          case Some(e) => (invOwnerId(is, Some(targs)), e)
          case _ => return (state, ISZ())
        }
      case ti: TypeInfo.Sig =>
        val is = ti.invariants.values
        if (ti.invariants.isEmpty) {
          return (state, ISZ())
        }
        val substMap = TypeChecker.buildTypeSubstMap(ti.owner, Some(pos), ti.ast.typeParams, targs, reporter).get
        logika.invs2exp(is, substMap) match {
          case Some(e) => (invOwnerId(is, Some(targs)), e)
          case _ => return (state, ISZ())
        }
      case _: TypeInfo.Enum => return (state, ISZ())
      case _ => halt(s"Infeasible: $ti")
    }
    val (s5, cond) = evalExtractPureMethod(logika, smt2, state, Some(receiver.tipe), Some(receiver), owner, id, inv, reporter)
    val (s6, sym) = logika.value2Sym(s5, cond, pos)
    return (s6, ISZ(sym))
  }

  def assumeValueInv(logika: Logika, smt2: Smt2, rtCheck: B, state: State, receiver: State.Value.Sym, pos: Position,
                  reporter: Reporter): State = {
    val (s0, conds) = addValueInv(logika, smt2, rtCheck, state, receiver, pos, reporter)
    return s0.addClaims(for (cond <- conds) yield State.Claim.Prop(T, cond))
  }

  @pure def z2SubZVal(ti: TypeInfo.SubZ, n: Z, pos: Position): State.Value = {
    val t = ti.typedOpt.get.asInstanceOf[AST.Typed.Name]
    if (ti.ast.isBitVector) {
      ti.ast.bitWidth match {
        case 8 => return State.Value.S8(conversions.Z.toS8(n), t, pos)
        case 16 => return State.Value.S16(conversions.Z.toS16(n), t, pos)
        case 32 => return State.Value.S32(conversions.Z.toS32(n), t, pos)
        case 64 => return State.Value.S64(conversions.Z.toS64(n), t, pos)
        case _ =>
      }
    } else {
      ti.ast.bitWidth match {
        case 8 => return State.Value.U8(conversions.Z.toU8(n), t, pos)
        case 16 => return State.Value.U16(conversions.Z.toU16(n), t, pos)
        case 32 => return State.Value.U32(conversions.Z.toU32(n), t, pos)
        case 64 => return State.Value.U64(conversions.Z.toU64(n), t, pos)
        case _ =>
      }
    }
    return State.Value.Range(n, t, pos)
  }

  def checkInvs(logika: Logika, posOpt: Option[Position], isAssume: B, title: String, smt2: Smt2, rtCheck: B, s0: State,
                receiverTypeOpt: Option[AST.Typed], invs: ISZ[Info.Inv], substMap: HashMap[String, AST.Typed],
                reporter: Reporter): State = {
    val pos = posOpt.get
    def spInv(): Option[State] = {
      val claim: AST.Exp = logika.invs2exp(invs, substMap) match {
        case Some(exp) => exp
        case _ => return Some(s0)
      }
      val tOpt: Option[ISZ[AST.Typed]] = receiverTypeOpt match {
        case Some(receiverType: AST.Typed.Name) if substMap.nonEmpty => Some(receiverType.args)
        case _ => None()
      }
      val (owner, id) = Util.invOwnerId(invs, tOpt)
      val (s1, v) = evalExtractPureMethod(logika, smt2, s0, receiverTypeOpt, None(), owner, id, claim, reporter)
      if (!s1.status) {
        return None()
      }
      val (s2, sym) = logika.value2Sym(s1, v, pos)
      if (isAssume) {
        val s3 = logika.evalAssumeH(T, smt2, title, s2, sym, posOpt, reporter)
        return Some(s3)
      } else {
        val s3 = logika.evalAssertH(T, smt2, title, s2, sym, posOpt, reporter)
        if (!s3.status) {
          return None()
        }
        return Some(s3)
      }
    }
    val oldIgnore = reporter.ignore
    reporter.setIgnore(T)
    val sOpt = spInv()
    reporter.setIgnore(oldIgnore)
    sOpt match {
      case Some(s) => return s
      case _ =>
    }
    var s4 = s0
    for (inv <- invs if s4.status) {
      s4 = logika.evalInv(posOpt, isAssume, title, smt2, rtCheck, s4, inv.ast, reporter)
    }
    return s4
  }
}