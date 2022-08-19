// #Sireum
/*
 Copyright (c) 2017-2022, Robby, Kansas State University
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
import org.sireum.logika.State.Value

object Util {

  @record class ClaimSTs(var value: ISZ[ST]) {
    def add(st: ST): Unit = {
      value = value :+ st
    }
  }

  @record class ClaimDefs(var value: HashMap[Z, ISZ[State.Claim.Let]]) {
    def addDef(d: State.Claim.Let): Unit = {
      value.get(d.sym.num) match {
        case Some(s) => value = value + d.sym.num ~> (Set(s) + d).elements
        case _ => value = value + d.sym.num ~> ISZ(d)
      }
    }

    def hasDef(d: State.Claim.Let): B = {
      return value.contains(d.sym.num)
    }
  }

  @record class NumMap(var value: HashMap[String, Z]) {
    def toST(prefix: ST, num: Z): ST = {
      val ps = prefix.render
      value.get(ps) match {
        case Some(n) => return if (n != num) st"$prefix#$num" else prefix
        case _ =>
          value = value + ps ~> num
          return prefix
      }
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
          case c: State.Claim.Let => defs.addDef(c)
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
      if (reporter.messages.isEmpty) {
        o.typedOpt.get match {
          case t: AST.Typed.Fun if !t.isPureFun =>
            reporter.warn(posOpt, Logika.kind, s"Verification of $id was skipped due to impure function (currently unsupported): $o")
          case _ =>
        }
      }
      return AST.MTransformer.PostResultExpEta
    }
  }

  @record class Substitutor(val substMap: HashMap[String, AST.Typed],
                            val context: ISZ[String],
                            val paramMap: HashSMap[String, AST.Exp],
                            val reporter: Reporter) extends AST.MTransformer {
    override def preTyped(o: AST.Typed): AST.MTransformer.PreResult[AST.Typed] = {
      o match {
        case o: AST.Typed.TypeVar =>
          substMap.get(o.id) match {
            case Some(t) => return AST.MTransformer.PreResult(F, MSome(t))
            case _ =>
          }
        case _ =>
      }
      return AST.MTransformer.PreResultTypedTypeVar
    }

    override def preResolvedInfoMethod(o: AST.ResolvedInfo.Method): AST.MTransformer.PreResult[AST.ResolvedInfo] = {
      return AST.MTransformer.PreResult(F, MNone())
    }

    override def preExpIdent(o: AST.Exp.Ident): AST.MTransformer.PreResult[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.LocalVar if paramMap.contains(res.id) && res.context == context =>
          return AST.MTransformer.PreResult(F, MSome(paramMap.get(res.id).get))
        case _ =>
      }
      return AST.MTransformer.PreResultExpIdent
    }

    override def preExpInvoke(o: AST.Exp.Invoke): AST.MTransformer.PreResult[AST.Exp] = {
      val res: AST.ResolvedInfo.LocalVar = o.ident.attr.resOpt.get match {
        case lv: AST.ResolvedInfo.LocalVar if paramMap.contains(lv.id) && lv.context == context => lv
        case _ => return AST.MTransformer.PreResultExpInvoke
      }
      val arg = paramMap.get(res.id).get
      arg match {
        case arg: AST.Exp.Fun =>
          arg.exp match {
            case argExp: AST.Stmt.Expr =>
              var fParamMap = HashSMap.empty[String, AST.Exp]
              for (pArg <- ops.ISZOps(arg.params).zip(o.args)) {
                pArg._1.idOpt match {
                  case Some(id) => fParamMap = fParamMap + id.value ~> pArg._2
                  case _ =>
                }
              }
              val subst = Substitutor(substMap, arg.context, fParamMap, Reporter.create)
              val expOpt = subst.transformExp(argExp.exp)
              reporter.reports(subst.reporter.messages)
              if (expOpt.isEmpty) {
                return AST.MTransformer.PreResult(T, MSome(o(receiverOpt = paramMap.get(res.id),
                  ident = o.ident(id = AST.Id("apply", o.ident.id.attr), attr = o.ident.attr(resOpt = TypeChecker.applyResOpt)))))
              } else {
                return AST.MTransformer.PreResult(T, expOpt)
              }
            case _ =>
              reporter.error(arg.posOpt, Logika.kind, "Invalid argument form for inception")
          }
        case AST.Exp.Eta(ref) =>
          ref match {
            case ref: AST.Exp.Ident =>
              return AST.MTransformer.PreResult(T, MSome(o(receiverOpt = None(), ident = ref)))
            case ref: AST.Exp.Select =>
              return AST.MTransformer.PreResult(T, MSome(o(receiverOpt = ref.receiverOpt, ident = AST.Exp.Ident(ref.id, ref.attr))))
          }
        case _ =>
          reporter.error(arg.posOpt, Logika.kind, "Invalid argument form for inception")
      }
      return AST.MTransformer.PreResult(F, MSome(paramMap.get(res.id).get))
    }
  }

  @record class VarSubstitutor(val context: ISZ[String],
                               val receiverTypeOpt: Option[AST.Typed],
                               var hasThis: B,
                               var resultOpt: Option[(AST.Exp, AST.Exp.Ident)],
                               var map: HashSMap[AST.ResolvedInfo, (AST.Exp, AST.Exp.Ident)],
                               var inputMap: HashSMap[AST.ResolvedInfo, (AST.Exp, AST.Exp.Ident)],
                               var invokeIdents: HashSet[AST.Exp.Ident],
                               var ignoreLocals: HashSet[ISZ[String]])
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

    override def preExpFun(o: AST.Exp.Fun): AST.MTransformer.PreResult[AST.Exp] = {
      for (p <- o.params) {
        p.idOpt match {
          case Some(id) => ignoreLocals = ignoreLocals + (o.context :+ id.value)
          case _ =>
        }
      }
      return AST.MTransformer.PreResultExpFun
    }

    override def preExpInput(o: AST.Exp.Input): AST.MTransformer.PreResult[AST.Exp] = {
      o.exp match {
        case exp: AST.Exp.Ident =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var => return introInputIdent(o, res, exp.id, exp.typedOpt)
            case res: AST.ResolvedInfo.LocalVar if res.context === context => return introInputIdent(o, res, exp.id, exp.typedOpt)
            case _ =>
          }
        case exp: AST.Exp.Select =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var if res.isInObject =>
              return introInputIdent(o, res, exp.id, exp.typedOpt)
            case _ =>
          }
        case _: AST.Exp.This => return AST.MTransformer.PreResultExpInput
        case _ =>
      }
      halt("Non-simple input")
    }

    override def preExpInvoke(o: AST.Exp.Invoke): AST.MTransformer.PreResult[AST.Exp] = {
      invokeIdents = invokeIdents + o.ident
      return AST.MTransformer.PreResultExpInvoke
    }

    override def preExpInvokeNamed(o: AST.Exp.InvokeNamed): AST.MTransformer.PreResult[AST.Exp] = {
      invokeIdents = invokeIdents + o.ident
      return AST.MTransformer.PreResultExpInvokeNamed
    }

    override def postExpResult(o: AST.Exp.Result): MOption[AST.Exp] = {
      val id = AST.Id("return", AST.Attr(o.posOpt))
      val lres = AST.ResolvedInfo.LocalVar(context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id.value)
      val ident = AST.Exp.Ident(id, AST.ResolvedAttr(o.attr.posOpt, Some(lres), o.typedOpt))
      resultOpt = Some((o, ident))
      return MSome(ident)
    }

    override def postExpIdent(o: AST.Exp.Ident): MOption[AST.Exp] = {
      if (invokeIdents.contains(o)) {
        return AST.MTransformer.PostResultExpIdent
      }
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
        case res: AST.ResolvedInfo.LocalVar if !ignoreLocals.contains(res.context :+ res.id) =>
          return introIdent(o, res, o.id, o.typedOpt)
        case _ =>
      }
      return AST.MTransformer.PostResultExpIdent
    }

    def invokeIdentH(ident: AST.Exp.Ident): Option[(Option[AST.Exp], AST.Exp.Ident, ISZ[AST.Type])] = {
      invokeIdents = invokeIdents - ident
      postExpIdent(ident) match {
        case MSome(exp: AST.Exp.Ident) => return Some((None(), exp, ISZ()))
        case MSome(exp: AST.Exp.Select) => return Some((exp.receiverOpt, AST.Exp.Ident(exp.id, exp.attr), exp.targs))
        case _ =>
      }
      return None()
    }

    override def postExpInvoke(o: AST.Exp.Invoke): MOption[AST.Exp] = {
      invokeIdentH(o.ident) match {
        case Some((Some(receiver), ident, targs)) =>
          val rident = receiver.asInstanceOf[AST.Exp.Ident]
          o.receiverOpt match {
            case Some(rcv) =>
              return MSome(o(receiverOpt = Some(AST.Exp.Select(Some(rcv), rident.id, targs, rident.attr)), ident = ident))
            case _ => return MSome(o(receiverOpt = Some(receiver), ident = ident))
          }
        case Some((_, ident, _)) => return MSome(o(ident = ident))
        case _ =>
      }
      return AST.MTransformer.PostResultExpInvoke
    }

    override def postExpInvokeNamed(o: AST.Exp.InvokeNamed): MOption[AST.Exp] = {
      invokeIdentH(o.ident) match {
        case Some((Some(receiver), ident, targs)) =>
          val rident = receiver.asInstanceOf[AST.Exp.Ident]
          o.receiverOpt match {
            case Some(rcv) => return MSome(o(receiverOpt = Some(AST.Exp.Select(Some(rcv), rident.id, targs, rident.attr)), ident = ident))
            case _ => return MSome(o(receiverOpt = Some(receiver), ident = ident))
          }
        case Some((_, ident, _)) => return MSome(o(ident = ident))
        case _ =>
      }
      return AST.MTransformer.PostResultExpInvokeNamed
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

  @record class LetCollector(var value: HashMap[Z, HashSet[State.Claim.Let]],
                             var syms: HashSSet[State.Value.Sym]) extends MStateTransformer {

    override def preStateClaim(o: State.Claim): MStateTransformer.PreResult[State.Claim] = {
      o match {
        case o: State.Claim.Let.Binary if Smt2.isSimpsOp(o) => syms = syms + o.sym
        case o: State.Claim.Let.CurrentId if o.declId =>
        case o: State.Claim.Let =>
          if (o.isInstanceOf[State.Claim.Let.Random]) {
            syms = syms + o.sym
          }
          val key = o.sym.num
          val s = value.get(key).getOrElse(HashSet.empty) + o
          value = value + key ~> s
        case _ =>
      }
      return MStateTransformer.PreResultStateClaimProp
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

  @record class SymAddRewriter(val min: Z, val add: Z) extends MStateTransformer {
    override def postStateValueSym(o: Value.Sym): MOption[State.Value] = {
      return if (o.num < min) MNone() else MSome(o(num = o.num + add))
    }
  }

  val builtInTypeNames: HashSet[ISZ[String]] = HashSet ++ ISZ(
    AST.Typed.bName, AST.Typed.zName, AST.Typed.cName, AST.Typed.stringName, AST.Typed.f32Name, AST.Typed.f64Name,
    AST.Typed.rName, AST.Typed.stName, AST.Typed.isName, AST.Typed.msName
  )

  def collectLetClaims(enabled: B, claims: ISZ[State.Claim]): (HashMap[Z, ISZ[State.Claim.Let]], HashSSet[State.Value.Sym]) = {
    if (enabled) {
      val lc = LetCollector(HashMap.empty, HashSSet.empty)
      for (c <- claims) {
        lc.transformStateClaim(c)
      }
      return (HashMap.empty[Z, ISZ[State.Claim.Let]] ++ (for (p <- lc.value.entries) yield (p._1, p._2.elements)), lc.syms)
    } else {
      return (HashMap.empty, HashSSet.empty)
    }
  }

  def value2ST(smt2: Smt2, lets: HashMap[Z, ISZ[State.Claim.Let]], declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): State.Value => ST = {
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
                case Some(ls) if ls.size == 1 && !ls(0).isInstanceOf[State.Claim.Let.Random] =>
                  smt2.l2RhsST(ls(0), sv2ST _, lets, declIds)
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


  def logikaMethod(th: TypeHierarchy, config: Config, owner: ISZ[String], id: String, receiverTypeOpt: Option[AST.Typed],
                   params: ISZ[(AST.Id, AST.Typed)], retType: AST.Typed, posOpt: Option[Position],
                   reads: ISZ[AST.Exp.Ref], requires: ISZ[AST.Exp], modifies: ISZ[AST.Exp.Ref],
                   ensures: ISZ[AST.Exp], caseLabels: ISZ[AST.Exp.LitString], plugins: ISZ[plugin.Plugin],
                   implicitContext: Option[(String, Position)], compMethods: HashSet[ISZ[String]]): Logika = {
    val mctx = Context.Method(owner, id, receiverTypeOpt, params, retType, reads, requires, modifies, ensures,
      HashMap.empty, HashMap.empty, HashMap.empty, posOpt)
    val ctx = Context.empty(methodOpt = Some(mctx), caseLabels = caseLabels, implicitCheckTitlePosOpt = implicitContext,
      compMethods = compMethods)
    return Logika(th, config, ctx, plugins)
  }

  def checkInv(isPre: B, state: State, logika: Logika, smt2: Smt2, cache: Smt2.Cache, invs: ISZ[lang.symbol.Info.Inv],
               posOpt: Option[Position], substMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
    val methodName: String =
      if (logika.context.methodName.size == 1) logika.context.methodName(0)
      else if (logika.context.methodOpt.get.receiverTypeOpt.isEmpty) st"${(logika.context.methodName, ".")}".render
      else st"${(ops.ISZOps(logika.context.methodName).dropRight(1), ".")}#${logika.context.methodName(0)}".render
    val title: String = if (isPre) s"Method $methodName pre-invariant" else s"Method $methodName post-invariant"
    return checkInvs(logika, posOpt, isPre, title, smt2, cache, T, state, logika.context.receiverTypeOpt, None(), invs,
      substMap, reporter)
  }

  def checkMethodPre(logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, state: State,
                     methodPosOpt: Option[Position], invs: ISZ[Info.Inv], requires: ISZ[AST.Exp]): State = {
    var s = state
    s = checkInv(T, s, logika, smt2, cache, invs, methodPosOpt, TypeChecker.emptySubstMap, reporter)
    for (r <- requires if s.status) {
      s = logika.evalAssume(smt2, cache, T, "Precondition", s, r, r.posOpt, reporter)._1
    }
    return s
  }

  def checkMethodPost(logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, states: ISZ[State],
                      methodPosOpt: Option[Position], invs: ISZ[Info.Inv], ensures: ISZ[AST.Exp], logPc: B, logRawPc: B,
                      postPosOpt: Option[Position]): ISZ[State] = {
    var r = ISZ[State]()
    for (state <- states) {
      if (!state.status) {
        r = r :+ state
      } else {
        var s = state
        s = checkInv(F, s, logika, smt2, cache, invs, methodPosOpt, TypeChecker.emptySubstMap, reporter)
        for (e <- ensures if s.status) {
          s = logika.evalAssert(smt2, cache, T, "Postcondition", s, e, e.posOpt, reporter)._1
        }
        if (postPosOpt.nonEmpty && s.status) {
          logika.logPc(logPc, logRawPc, s(status = F), reporter, postPosOpt)
        }
        r = r :+ s
      }
    }
    return r
  }

  def checkMethod(th: TypeHierarchy,
                  plugins: ISZ[plugin.Plugin],
                  method: AST.Stmt.Method,
                  caseIndex: Z,
                  config: Config,
                  smt2: Smt2,
                  cache: Smt2.Cache,
                  reporter: Reporter): Unit = {
    val mconfig: Config = if (caseIndex >= 0) config(checkInfeasiblePatternMatch = F) else config
    def checkCase(labelOpt: Option[AST.Exp.LitString], reads: ISZ[AST.Exp.Ref], requires: ISZ[AST.Exp],
                  modifies: ISZ[AST.Exp.Ref], ensures: ISZ[AST.Exp]): Unit = {
      var state = State.create
      labelOpt match {
        case Some(label) if label.value != "" => state = state.addClaim(State.Claim.Label(label.value, label.posOpt.get))
        case _ =>
      }
      val res = method.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val methodPosOpt = method.sig.id.attr.posOpt
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
        val l = logikaMethod(th, mconfig, res.owner, method.sig.id.value, receiverTypeOpt, method.sig.paramIdTypes,
          method.sig.returnType.typedOpt.get, methodPosOpt, reads, requires, modifies, ensures,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get), plugins, None(), HashSet.empty)
        val mctx = l.context.methodOpt.get
        var objectVarInMap = mctx.objectVarInMap
        var objectNames = HashSMap.empty[ISZ[String], Position]
        for (p <- (mctx.readObjectVarMap(TypeChecker.emptySubstMap) ++
          mctx.modObjectVarMap(TypeChecker.emptySubstMap).entries).entries) {
          val (ids, (t, posOpt)) = p
          val pos = posOpt.get
          val owner: ISZ[String] = th.nameMap.get(ids).get match {
            case info: Info.Var => info.owner
            case info: Info.SpecVar => info.owner
            case info => halt(s"Unexpected: $info")
          }
          objectNames = objectNames + owner ~> pos
          val (s0, sym) = nameIntro(posOpt.get, state, ids, t, posOpt)
          state = assumeValueInv(l, smt2, cache, T, s0, sym, pos, reporter)
          objectVarInMap = objectVarInMap + ids ~> sym
        }
        for (p <- objectNames.entries) {
          val (objectName, pos) = p
          state = assumeObjectInv(l, smt2, cache, objectName, state, pos, reporter)
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
          if (id.value =!= "this") {
            val (s0, sym) = idIntro(posOpt.get, state, mname, id.value, t, posOpt)
            state = assumeValueInv(l, smt2, cache, T, s0, sym, posOpt.get, reporter)
            localInMap = localInMap + id.value ~> sym
          } else {
            val (s0, sym) = idIntro(posOpt.get, state, mname, id.value, t, None())
            state = s0
            localInMap = localInMap + id.value ~> sym
          }
        }
        l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
          localInMap = localInMap))))
      }
      val invs = logika.retrieveInvs(res.owner, res.isInObject)
      state = checkMethodPre(logika, smt2, cache, reporter, state, methodPosOpt, invs, requires)
      val body = method.bodyOpt.get
      val stmts = body.stmts
      val ss: ISZ[State] = if (method.purity == AST.Purity.StrictPure) {
        val spBody = stmts(0).asInstanceOf[AST.Stmt.Var].initOpt.get
        logika.evalAssignExp(Split.Default, smt2, cache, None(), T, state, spBody, reporter)
      } else {
        logika.evalStmts(!(body.allReturns && config.branchPar =!= Config.BranchPar.Disabled), Split.Default, smt2,
          cache, None(), T, state, stmts, reporter)
      }
      checkMethodPost(logika, smt2, cache, reporter, ss, methodPosOpt, invs, ensures, mconfig.logPc, mconfig.logRawPc,
        if (stmts.nonEmpty) stmts(stmts.size - 1).posOpt else None())
    }

    if (method.mcontract.isEmpty) {
      checkCase(None(), ISZ(), ISZ(), ISZ(), ISZ())
    } else {
      method.mcontract match {
        case contract: AST.MethodContract.Simple =>
          checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures)
        case contract: AST.MethodContract.Cases =>
          if (caseIndex >= 0) {
            val c = contract.cases(caseIndex)
            checkCase(if (c.label.value === "") None() else Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
          } else {
            for (c <- contract.cases) {
              checkCase(if (c.label.value === "") None() else Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
            }
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

  def rewriteObjectVars(logika: Logika, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State,
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
        reporter.error(Some(pos), Logika.kind, st"Missing Modifies clause for ${(ids, ".")}".render)
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
      current = assumeValueInv(logika, smt2, cache, rtCheck, s2, sym, namePos, reporter)
      val tipe = sym.tipe
      if (AST.Util.isSeq(tipe)) {
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

  @pure def normType(t: AST.Typed): AST.Typed = {
    t match {
      case t: AST.Typed.Method if t.tpe.isByName => return t.tpe.ret
      case _ => return t
    }
  }

  def strictPureMethod(th: TypeHierarchy, config: Config, plugins: ISZ[plugin.Plugin], smt2: Smt2, cache: Smt2.Cache,
                       state: State, receiverTypeOpt: Option[AST.Typed], funType: AST.Typed.Fun, owner: ISZ[String],
                       id: String, paramIds: ISZ[AST.Id], body: AST.AssignExp, reporter: Reporter,
                       implicitContextOpt: Option[(String, Position)]): (State, State.ProofFun) = {
    val pf = State.ProofFun(receiverTypeOpt, owner, id, for (id <- paramIds) yield id.value, funType.args, Util.normType(funType.ret))
    if (smt2.strictPureMethods.contains(pf)) {
      return (state, pf)
    } else {
      val posOpt = body.asStmt.posOpt
      val pos = posOpt.get
      val (svs, maxFresh, status): (ISZ[(State, State.Value.Sym)], Z, B) = {
        val context = pf.context :+ pf.id
        val logika: Logika = logikaMethod(th, config, pf.context, pf.id,  pf.receiverTypeOpt,
          ops.ISZOps(paramIds).zip(pf.paramTypes), pf.returnType, posOpt, ISZ(), ISZ(), ISZ(), ISZ(), ISZ(), plugins,
          implicitContextOpt, HashSet.empty)
        var s0 = state(claims = ISZ())
        val (s1, res) = idIntro(posOpt.get, s0, context, "Res", pf.returnType, posOpt)
        val s2 = assumeValueInv(logika, smt2, cache, T, s1, res, pos, reporter)
        smt2.addStrictPureMethodDecl(pf, res, ops.ISZOps(s2.claims).slice(s1.claims.size, s2.claims.size), reporter)
        s0 = s0(nextFresh = s2.nextFresh, status = s2.status)
        for (pair <- ops.ISZOps(paramIds).zip(pf.paramTypes) if pair._1.value =!= "this") {
          val (pid, pt) = pair
          val (s0_1, pv) = idIntro(pos, s0, context, pid.value, pt, pid.attr.posOpt)
          val s0_2 = assumeValueInv(logika, smt2, cache, T, s0_1, pv, pos, reporter)
          s0 = s0_2
        }
        val split: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
        val svs: ISZ[(State, State.Value)] = body match {
          case AST.Stmt.Expr(_: AST.Exp.Result) => ISZ()
          case _ => logika.evalAssignExpValue(split, smt2, cache, pf.returnType, T, s0, body, reporter)
        }
        var sss = ISZ[(State, State.Value.Sym)]()
        var maxFresh: Z = s0.nextFresh
        var status = svs.isEmpty
        for (sv <- svs) {
          val (s, v) = sv
          if (s.status) {
            status = T
          }
          val (s2, sym) = logika.value2Sym(s, v, pos)
          sss = sss :+ ((s2, sym))
          if (maxFresh < s2.nextFresh) {
            maxFresh = s2.nextFresh
          }
        }
        assert(svs.isEmpty || maxFresh >= 0)
        (for (ss <- sss) yield (ss._1(nextFresh = maxFresh), ss._2), maxFresh, status)
      }

      if (status && svs.nonEmpty) {
        smt2.addStrictPureMethod(pos, pf, svs, 0, reporter)
      }

      val s1 = state(status = status, nextFresh = maxFresh)
      if (config.sat && s1.status) {
        val title: String = s"the derived proof function of $id"
        if (!smt2.sat(cache, T, config.logVc, config.logVcDirOpt, title, pos, ISZ(), reporter)) {
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

  def evalExtractPureMethod(logika: Logika, smt2: Smt2, cache: Smt2.Cache, state: State, receiverTypeOpt: Option[AST.Typed],
                            receiverOpt: Option[State.Value.Sym], owner: ISZ[String], id: String, exp: AST.Exp,
                            reporter: Reporter): (State, State.Value) = {
    val posOpt = exp.posOpt
    val tOpt = exp.typedOpt
    val t = tOpt.get
    val vs = VarSubstitutor(owner :+ id, receiverTypeOpt, F, None(), HashSMap.empty, HashSMap.empty, HashSet.empty, HashSet.empty)
    val newExp = vs.transformExp(exp).getOrElse(exp)
    if (vs.hasThis || vs.map.nonEmpty) {
      var paramIds = ISZ[AST.Id]()
      var paramTypes = ISZ[AST.Typed]()
      var s0 = state
      var args = ISZ[State.Value]()
      if (vs.hasThis) {
        receiverOpt match {
          case Some(receiver) =>
            s0 = s0.addClaim(State.Claim.Let.CurrentId(T, receiver, logika.context.methodName, "this", None()))
            args = args :+ receiver
          case _ =>
            val e = AST.Exp.This(AST.TypedAttr(posOpt, receiverTypeOpt))
            val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, cache, T, s0, e, reporter)
            s0 = s1
            args = args :+ arg
        }
      }
      for (pair <- vs.map.values) {
        val (e, paramIdent) = pair
        paramIds = paramIds :+ paramIdent.id
        paramTypes = paramTypes :+ paramIdent.typedOpt.get
        val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, cache, T, s0, e, reporter)
        s0 = s1
        args = args :+ arg
      }
      for (pair <- vs.inputMap.values) {
        val (e, paramIdent) = pair
        paramIds = paramIds :+ paramIdent.id
        paramTypes = paramTypes :+ paramIdent.typedOpt.get
        val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, cache, T, s0, e, reporter)
        s0 = s1
        args = args :+ arg
      }
      vs.resultOpt match {
        case Some((_, ident)) =>
          paramIds = paramIds :+ ident.id
          paramTypes = paramTypes :+ ident.typedOpt.get
          val e = AST.Exp.Result(None(), AST.TypedAttr(posOpt, ident.typedOpt))
          val ISZ((s1, arg)) = logika.evalExp(Split.Disabled, smt2, cache, T, s0, e, reporter)
          s0 = s1
          args = args :+ arg
        case _ =>
      }
      val (s2, pf) = strictPureMethod(logika.th, logika.config, logika.plugins, smt2, cache, s0, receiverTypeOpt,
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
      return logika.evalExp(Split.Disabled, smt2, cache, T, state, newExp, reporter)(0)
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

  def addObjectInv(logika: Logika, smt2: Smt2, cache: Smt2.Cache, name: ISZ[String], state: State, pos: Position,
                   reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    val l = logika(context = logika.context(methodOpt = Some(Context.Method(
      owner = name,
      id = "<init>",
      receiverTypeOpt = None(),
      params = ISZ(),
      retType = AST.Typed.unit,
      reads = ISZ(),
      requires = ISZ(),
      modifies = ISZ(),
      ensures = ISZ(),
      objectVarInMap = HashMap.empty,
      fieldVarInMap = HashMap.empty,
      localInMap = HashMap.empty,
      posOpt = None()
    ))))
    val invs = l.retrieveInvs(name, T)
    if (invs.isEmpty) {
      return (state, ISZ())
    }
    val (owner, id) = invOwnerId(invs, None())
    val inv = l.invs2exp(invs, HashMap.empty).get
    val (s0, v) = evalExtractPureMethod(l, smt2, cache, state, None(), None(), owner, id, inv, reporter)
    val (s1, sym) = l.value2Sym(s0, v, pos)
    return (s1, ISZ(sym))
  }

  def assumeObjectInv(logika: Logika, smt2: Smt2, cache: Smt2.Cache, name: ISZ[String], state: State, pos: Position,
                      reporter: Reporter): State = {
    val (s0, conds) = addObjectInv(logika, smt2, cache, name, state, pos, reporter)
    return s0.addClaims(for (cond <- conds) yield State.Claim.Prop(T, cond))
  }

  def addValueInv(logika: Logika, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, receiver: State.Value.Sym,
                  pos: Position, reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    def addTupleInv(s0: State, t: AST.Typed.Tuple): (State, ISZ[State.Value.Sym]) = {
      var s1 = s0
      var i = 1
      var ss = ISZ[State.Value.Sym]()
      for (arg <- t.args) {
        val (s2, sym) = s1.freshSym(arg, pos)
        val s3 = s2.addClaim(State.Claim.Let.FieldLookup(sym, receiver, s"_$i"))
        val (s4, syms) = Util.addValueInv(logika, smt2, cache, rtCheck, s3, sym, pos, reporter)
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
          z2SubZVal(ti, ti.ast.max, pos), t))
        ss = ss :+ maxCond
      }
      return (s1, ss)
    }
    val t = receiver.tipe
    smt2.addType(t, reporter)
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
    val (s5, cond) = evalExtractPureMethod(logika, smt2, cache, state, Some(receiver.tipe), Some(receiver), owner, id, inv, reporter)
    val (s6, sym) = logika.value2Sym(s5, cond, pos)
    return (s6, ISZ(sym))
  }

  def assumeValueInv(logika: Logika, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, receiver: State.Value.Sym,
                     pos: Position, reporter: Reporter): State = {
    val (s0, conds) = addValueInv(logika, smt2, cache, rtCheck, state, receiver, pos, reporter)
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

  def checkInvs(logika: Logika, posOpt: Option[Position], isAssume: B, title: String, smt2: Smt2, cache: Smt2.Cache,
                rtCheck: B, s0: State, receiverTypeOpt: Option[AST.Typed], receiverOpt: Option[State.Value.Sym], invs: ISZ[Info.Inv],
                substMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
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
      val (s1, v) = evalExtractPureMethod(logika, smt2, cache, s0, receiverTypeOpt, receiverOpt, owner, id, claim, reporter)
      if (!s1.status) {
        return None()
      }
      val (s2, sym) = logika.value2Sym(s1, v, pos)
      if (isAssume) {
        val s3 = logika.evalAssumeH(T, smt2, cache, title, s2, sym, posOpt, reporter)
        return Some(s3)
      } else {
        val s3 = logika.evalAssertH(T, smt2, cache, title, s2, sym, posOpt, reporter)
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
      s4 = logika.evalInv(posOpt, isAssume, title, smt2, cache, rtCheck, s4, inv.ast, substMap, reporter)
    }
    return s4
  }

  def evalAssignReceiver(modifies: ISZ[AST.Exp.Ref], logika: Logika, logikaComp: Logika, smt2: Smt2, cache: Smt2.Cache,
                         rtCheck: B, state: State, receiverOpt: Option[AST.Exp], receiverSymOpt: Option[State.Value.Sym],
                         typeSubstMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
    def isLhs(exp: AST.Exp): B = {
      exp match {
        case exp: AST.Exp.Ident =>
          exp.attr.resOpt.get match {
            case _: AST.ResolvedInfo.LocalVar => return T
            case _: AST.ResolvedInfo.Var => return T
            case _ => return F
          }
        case exp: AST.Exp.Select =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var =>
              if (res.isInObject) {
                return T
              } else {
                return isLhs(exp.receiverOpt.get)
              }
            case _ => return F
          }
        case exp: AST.Exp.Invoke =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Select =>
              exp.receiverOpt match {
                case Some(receiver) => return isLhs(receiver)
                case _ => return T
              }
            case _ => return F
          }
        case _ => return F
      }
    }
    if (modifies.isEmpty || receiverOpt.isEmpty) {
      return state
    }
    val receiver = receiverOpt.get
    val pos = receiver.posOpt.get
    val rsym = receiverSymOpt.get
    val p: (State, State.Value.Sym) = receiver match {
      case _: AST.Exp.This =>
        val (s0, sym) = idIntro(pos, state, logikaComp.context.methodName, "this", receiver.typedOpt.get, None())
        (s0, sym)
      case _ =>
        if (!isLhs(receiver)) {
          return state
        }
        val (s0, sym) = idIntro(pos, state, logikaComp.context.methodName, "this", receiver.typedOpt.get, Some(pos))
        val s1 = logika.assignRec(Split.Disabled, smt2, cache, rtCheck, s0, receiver, sym, reporter)(0)
        val (s2, v) = logika.evalExp(Split.Disabled, smt2, cache, rtCheck, s1, receiver, reporter)(0)
        val (s3, newRs) = logika.value2Sym(s2, v, pos)
        (s3, newRs)
    }
    var (s4, newRsym) = p
    val owner = logikaComp.context.owner
    var modVars = ISZ[String]()
    for (m <- modifies) {
      m.resOpt.get match {
        case res: AST.ResolvedInfo.Var if !res.isInObject => modVars = modVars :+ res.id
        case _ =>
      }
    }
    def eqSpecVars(m: HashSMap[String, Info.SpecVar]): Unit = {
      for (x <- m.values) {
        val id = x.ast.id.value
        val t = x.typedOpt.get.subst(typeSubstMap)
        val (s5, xsym) = s4.freshSym(t, pos)
        val (s6, newXsym) = s5.freshSym(t, pos)
        val (s7, cond) = s6.freshSym(AST.Typed.b, pos)
        s4 = s7.addClaims(ISZ(
          State.Claim.Let.FieldLookup(newXsym, newRsym, id),
          State.Claim.Let.FieldLookup(xsym, rsym, id),
          State.Claim.Let.Binary(cond, newXsym, AST.Exp.BinaryOp.Eq, xsym, t),
          State.Claim.Prop(T, cond)
        ))
      }
    }
    def eqVars(m: HashSMap[String, Info.Var]): Unit = {
      for (x <- m.values) {
        val id = x.ast.id.value
        val t = x.typedOpt.get.subst(typeSubstMap)
        val (s5, xsym) = s4.freshSym(t, pos)
        val (s6, newXsym) = s5.freshSym(t, pos)
        val (s7, cond) = s6.freshSym(AST.Typed.b, pos)
        s4 = s7.addClaims(ISZ(
          State.Claim.Let.FieldLookup(newXsym, newRsym, id),
          State.Claim.Let.FieldLookup(xsym, rsym, id),
          State.Claim.Let.Binary(cond, newXsym, AST.Exp.BinaryOp.Eq, xsym, t),
          State.Claim.Prop(T, cond)
        ))
      }
    }
    logika.th.typeMap.get(owner).get match {
      case info: TypeInfo.Sig =>
        eqSpecVars(info.specVars -- modVars)
      case info: TypeInfo.Adt =>
        eqSpecVars(info.specVars -- modVars)
        eqVars(info.vars -- modVars)
      case _ =>
    }
    return s4
  }

  @pure def toExps(pos: Position, claims: ISZ[State.Claim], th: TypeHierarchy): ISZ[AST.Exp] = {
    @strictpure def isLetNameId(let: State.Claim.Let): B = let match {
      case _: State.Claim.Let.Id => T
      case _: State.Claim.Let.CurrentId => T
      case _: State.Claim.Let.Name => T
      case _: State.Claim.Let.CurrentName => T
      case _ => F
    }

    val posOpt: Option[Position] = Some(pos)
    val letsMap: HashMap[Z, ISZ[State.Claim.Let]] = {
      var m = HashMap.empty[Z, ISZ[State.Claim.Let]]
      for (p <- Util.collectLetClaims(T, claims)._1.entries) {
        val (num, lets) = p
        if (lets.size > 1) {
          var newLets = ISZ[State.Claim.Let]()
          for (let <- lets if !isLetNameId(let)) {
            newLets = newLets :+ let
          }
          assert(newLets.nonEmpty)
          m = m + num ~> newLets
        } else {
          m = m + num ~> lets
        }
      }
      m
    }

    @pure def toBinaryExp(cs: ISZ[State.Claim], dflt: AST.Exp, op: String, tOpt: Option[AST.Typed], res: AST.ResolvedInfo): AST.Exp = {
      if (cs.isEmpty) {
        return dflt
      }
      var r = toExp(cs(0))
      for (i <- 1 to cs.size) {
        r = AST.Exp.Binary(r, op, toExp(cs(i)), AST.ResolvedAttr(posOpt, Some(res), tOpt))
      }
      return r
    }

    @pure def nameResTypeOpts(ids: ISZ[String]): (Option[AST.ResolvedInfo], Option[AST.Typed]) = {
      th.nameMap.get(ids).get match {
        case info: Info.Object => return (Some(AST.ResolvedInfo.Object(ids)),
          Some(AST.Typed.Object(info.owner, info.ast.id.value)))
        case _: Info.Package => return (Some(AST.ResolvedInfo.Package(ids)),
          Some(AST.Typed.Package(ids)))
        case _: Info.Enum => return (Some(AST.ResolvedInfo.Enum(ids)),
          Some(AST.Typed.Enum(ids)))
        case info: Info.EnumElement => return (th.nameMap.get(info.owner).get.asInstanceOf[Info.Enum].elements.get(info.id),
          Some(AST.Typed.Name(ids, ISZ())))
        case info => halt(s"Infeasible: $info")
      }
    }

    @pure def nameToExp(ids: ISZ[String], p: Position): AST.Exp = {
      val pOpt: Option[Position] = Some(p)
      val first = ids(0)
      val firstResTypedOpts = nameResTypeOpts(ISZ(first))
      var r: AST.Exp = AST.Exp.Ident(AST.Id(first, AST.Attr(pOpt)),
        AST.ResolvedAttr(pOpt, firstResTypedOpts._1, firstResTypedOpts._2))
      for (i <- 1 until ids.size) {
        val iResTypedOpts = nameResTypeOpts(for (j <- 0 to i) yield ids(j))
        r = AST.Exp.Select(Some(r), AST.Id(ids(i), AST.Attr(pOpt)), ISZ(),
          AST.ResolvedAttr(pOpt, iResTypedOpts._1, iResTypedOpts._2))
      }
      return r
    }

    @pure def letToExp(let: State.Claim.Let): AST.Exp = {
      let match {
        case let: State.Claim.Let.CurrentId =>
        case let: State.Claim.Let.CurrentName =>
        case let: State.Claim.Let.Id =>
        case let: State.Claim.Let.Name =>
        case let: State.Claim.Let.Unary =>
        case let: State.Claim.Let.Binary =>
        case let: State.Claim.Let.Eq =>
        case let: State.Claim.Let.And =>
        case let: State.Claim.Let.Or =>
        case let: State.Claim.Let.Imply =>
        case let: State.Claim.Let.Ite =>
        case let: State.Claim.Let.TupleLit =>
        case let: State.Claim.Let.AdtLit =>
        case let: State.Claim.Let.SeqLit =>
        case let: State.Claim.Let.Quant =>
        case let: State.Claim.Let.Random =>
        case let: State.Claim.Let.FieldLookup =>
        case let: State.Claim.Let.FieldStore =>
        case let: State.Claim.Let.SeqStore =>
        case let: State.Claim.Let.SeqLookup =>
        case let: State.Claim.Let.SeqInBound =>
        case let: State.Claim.Let.TypeTest =>
        case let: State.Claim.Let.ProofFunApply =>
        case let: State.Claim.Let.Apply =>
        case let: State.Claim.Let.IApply =>
      }
      halt("TODO")
    }

    @pure def valueToExp(value: State.Value): AST.Exp = {
      @strictpure def subZPrefix(t: AST.Typed.Name): String = ops.StringOps(t.ids(t.ids.size - 1)).firstToLower

      value match {
        case value: State.Value.Sym =>
          letsMap.get(value.num) match {
            case Some(lets) if lets.size === 1 => letToExp(lets(0))
            case _ => return AST.Exp.Sym(value.num, AST.TypedAttr(Some(value.pos), Some(value.tipe)))
          }
        case value: State.Value.B => return AST.Exp.LitB(value.value, AST.Attr(Some(value.pos)))
        case value: State.Value.Z => return AST.Exp.LitZ(value.value, AST.Attr(Some(value.pos)))
        case value: State.Value.R => return AST.Exp.LitR(value.value, AST.Attr(Some(value.pos)))
        case value: State.Value.C => return AST.Exp.LitC(value.value, AST.Attr(Some(value.pos)))
        case value: State.Value.F32 => return AST.Exp.LitF32(value.value, AST.Attr(Some(value.pos)))
        case value: State.Value.F64 => return AST.Exp.LitF64(value.value, AST.Attr(Some(value.pos)))
        case value: State.Value.String => return AST.Exp.LitString(value.value, AST.Attr(Some(value.pos)))
        case value: State.Value.Enum => return nameToExp(value.owner :+ value.id, value.pos)
        case value: State.Value.S8 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S8.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.S16 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S16.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.S32 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S32.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.S64 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S64.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.U8 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U8.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.U16 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U16.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.U32 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U32.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.U64 =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U64.toZ(value.value).string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.Range =>
          val vPosOpt: Option[Position] = Some(value.pos)
          return AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(value.value.string, AST.Attr(vPosOpt))), ISZ(),
            AST.TypedAttr(vPosOpt, Some(value.tipe)))
        case value: State.Value.Unit => halt(s"Infeasible: $value")
      }
    }

    @pure def toExp(claim: State.Claim): AST.Exp = {
      claim match {
        case claim: State.Claim.And =>
          return toBinaryExp(claim.claims, AST.Exp.LitB(T, AST.Attr(posOpt)), AST.Exp.BinaryOp.And,
            AST.Typed.bOpt, AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryAnd))
        case claim: State.Claim.Or =>
          return toBinaryExp(claim.claims, AST.Exp.LitB(T, AST.Attr(posOpt)), AST.Exp.BinaryOp.Or,
            AST.Typed.bOpt, AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryOr))
        case claim: State.Claim.Imply =>
          assert(claim.claims.size > 1)
          return toBinaryExp(claim.claims, AST.Exp.LitB(T, AST.Attr(posOpt)), AST.Exp.BinaryOp.Imply,
            AST.Typed.bOpt, AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryOr))
        case claim: State.Claim.Prop =>
          return if (claim.isPos) valueToExp(claim.value)
          else AST.Exp.Unary(AST.Exp.UnaryOp.Not,
            valueToExp(claim.value), AST.ResolvedAttr(posOpt,
              Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.UnaryNot)), AST.Typed.bOpt)
          )
        case claim: State.Claim.If =>
          return AST.Exp.If(valueToExp(claim.cond), toExp(State.Claim.And(claim.tClaims)), toExp(State.Claim.And(claim.fClaims)),
            AST.TypedAttr(posOpt, AST.Typed.bOpt))
        case claim: State.Claim.Let => return letToExp(claim)
        case claim => halt(s"Infeasible: $claim")
      }
    }

    var r = ISZ[AST.Exp]()
    for (claim <- claims) {
      claim match {
        case claim: State.Claim.And => r = r :+ toExp(claim)
        case claim: State.Claim.Or => r = r :+ toExp(claim)
        case claim: State.Claim.Imply => r = r :+ toExp(claim)
        case claim: State.Claim.Prop => r = r :+ toExp(claim)
        case claim: State.Claim.If => r = r :+ toExp(claim)
        case claim: State.Claim.Let.CurrentId => r = r :+ toExp(claim)
        case claim: State.Claim.Let.CurrentName => r = r :+ toExp(claim)
        case claim: State.Claim.Let.Id => r = r :+ toExp(claim)
        case claim: State.Claim.Let.Name => r = r :+ toExp(claim)
        case _: State.Claim.Let =>
        case _: State.Claim.Label =>
      }
    }
    return r
  }

}