// #Sireum
/*
 Copyright (c) 2017-2024, Robby, Kansas State University
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
import org.sireum.logika.options.OptionsUtil

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

  @record class UnsupportedFeatureDetector(val posOpt: Option[Position], val id: String, val reporter: message.Reporter) extends AST.MTransformer {
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
              val subst = Substitutor(substMap, arg.context, fParamMap, reporter.empty)
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
        case ident: AST.Exp.Ident =>
          return AST.MTransformer.PreResult(T, MSome(o(ident = ident)))
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
            case res: AST.ResolvedInfo.LocalVar if res.context == context =>
              return introInputIdent(o, res, exp.id, exp.typedOpt)
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

  @datatype class CurrentIdCollector(val context: ISZ[String]) extends StateTransformer.PrePost[Set[String]] {
    override def preStateClaimLetCurrentId(ctx: Set[String],
                                           o: State.Claim.Let.CurrentId): StateTransformer.PreResult[Set[String], State.Claim.Let] = {
      return if (o.context == context) StateTransformer.PreResult(ctx + o.id, T, None())
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

  @datatype class CurrentIdRewriter(val map: HashMap[(ISZ[String], String), (ISZ[Position], Z)], val inScope: B)
    extends StateTransformer.PrePost[B] {

    override def preStateClaimLetCurrentId(ctx: B,
                                           o: State.Claim.Let.CurrentId): StateTransformer.PreResult[B, State.Claim.Let] = {
      map.get((o.context, o.id)) match {
        case Some((poss, num)) =>
          return StateTransformer.PreResult(ctx, T, Some(State.Claim.Let.Id(o.sym, inScope, o.context, o.id, num, poss)))
        case _ =>
          return StateTransformer.PreResult(ctx, T, None())
      }
    }
  }

  @datatype class CurrentNameRewriter(val map: HashMap[ISZ[String], (ISZ[Position], Z)])
    extends StateTransformer.PrePost[B] {
    override def preStateClaimLetCurrentName(ctx: B,
                                             o: State.Claim.Let.CurrentName): StateTransformer.PreResult[B, State.Claim.Let] = {
      map.get(o.ids) match {
        case Some((poss, num)) => return StateTransformer.PreResult(ctx,
          T, Some(State.Claim.Let.Name(o.sym, o.ids, num, poss)))
        case _ => return StateTransformer.PreResult(ctx, T, None())
      }
    }
  }

  @record class SymAddRewriter(val min: Z, val add: Z, val plugins: ISZ[plugin.ClaimPlugin]) extends MStateTransformer {

    override def postStateValueSym(o: State.Value.Sym): MOption[State.Value] = {
      return if (o.num < min) MNone() else MSome(o(num = o.num + add))
    }

    override def transformStateClaimData(o: State.Claim.Data): MOption[State.Claim.Data] = {
      if (plugins.nonEmpty) {
        for (p <- plugins if p.canHandleSymRewrite(o)) {
          return p.handleSymRewrite(this, o)
        }
      }
      return MNone()
    }
  }

  @record class LetEqNumMapCollector(var letMap: HashMap[Z, HashSSet[State.Claim.Let]],
                                     var eqMap: HashMap[Z, HashSSet[State.Claim.Eq]]) extends MStateTransformer {
    override def preStateClaim(o: State.Claim): MStateTransformer.PreResult[State.Claim] = {
      o match {
        case o: State.Claim.Eq =>
          o.v2 match {
            case v2: State.Value.Sym => eqMap = eqMap + v2.num ~> (eqMap.get(v2.num).getOrElse(HashSSet.empty) + o)
            case _ =>
          }
        case o: State.Claim.Let =>
          val key = o.sym.num
          letMap = letMap + key ~> (letMap.get(key).getOrElse(HashSSet.empty) + o)
        case _ =>
      }
      return MStateTransformer.PreResultStateClaimProp
    }
  }

  @record class NonLocalIdCollector(val context: ISZ[String], var nonLocals: HashSSet[State.Claim.Let.Id]) extends MStateTransformer {
    override def postStateClaimLetId(o: State.Claim.Let.Id): MOption[State.Claim.Let] = {
      if (o.context != context) {
        nonLocals = nonLocals + o
      }
      return MNone()
    }
  }

  object ClaimsToExps {
    type AtPossKey = (ISZ[String], String, AST.Typed)
    type AtKey = (ISZ[String], String, AST.Typed, Z)
    type AtMap = HashMap[AtKey, (ISZ[Position], Z, State.Value.Sym)]
  }

  @record class ClaimsToExps(val plugins: ISZ[plugin.ClaimPlugin],
                             val pos: Position,
                             val context: ISZ[String],
                             val th: TypeHierarchy,
                             val includeFreshLines: B,
                             val atRewrite: B,
                             val letMap: HashMap[Z, HashSSet[State.Claim.Let]],
                             val eqMap: HashMap[Z, HashSSet[State.Claim.Eq]],
                             var atPossMap: HashMap[ClaimsToExps.AtPossKey, HashMap[ISZ[Position], HashMap[Z, (Z, State.Value.Sym)]]]) {

    val posOpt: Option[Position] = Some(pos)
    val mulSymDefs: HashSet[Z] = {
      var r = HashSet.empty[Z]
      for (p <- letMap.entries) {
        val (key, lets) = p
        if (lets.size > 1) {
          var foundIdOrName = F
          for (l <- lets.elements if !foundIdOrName) {
            l match {
              case _: State.Claim.Let.Id => foundIdOrName = T
              case _: State.Claim.Let.Name => foundIdOrName = T
              case _ =>
            }
          }
          if (!foundIdOrName) {
            r = r + key
          }
        }
      }
      r
    }

    def atMap: ClaimsToExps.AtMap = {
      var r: ClaimsToExps.AtMap = HashMap.empty
      for (p <- atPossMap.entries) {
        val ((ctx, id, t), m) = p
        for (p2 <- m.entries) {
          val (poss, m) = p2
          for (p3 <- m.entries) {
            val (num, (n, sym)) = p3
            val key = (ctx, id, t, n)
            if (r.get(key).isEmpty) {
              r = r + key ~> ((poss, num, sym))
            }
          }
        }
      }
      return r
    }

    @pure def ignore(claim: State.Claim): B = {
      claim match {
        case _: State.Claim.And => return F
        case _: State.Claim.Or => return F
        case _: State.Claim.Imply => return F
        case _: State.Claim.Prop => return F
        case _: State.Claim.If => return F
        case _: State.Claim.Eq => return F
        case _: State.Claim.Let.CurrentId => return F
        case _: State.Claim.Let.CurrentName => return F
        case _: State.Claim.Let.Id => return F
        case _: State.Claim.Let.Name => return F
        case _: State.Claim.Custom => return F
        case _: State.Claim.Old => return F
        case _: State.Claim.Input => return F
        case _ => return T
      }
    }

    @pure def esToBinaryExp(es: ISZ[AST.Exp], dflt: AST.Exp, op: String, tOpt: Option[AST.Typed], res: AST.ResolvedInfo): AST.Exp = {
      if (es.isEmpty) {
        return dflt
      }
      var r = es(0)
      for (i <- 1 until es.size) {
        r = AST.Exp.Binary(r, op, es(i), AST.ResolvedAttr(None(), Some(res), tOpt), None())
      }
      return r
    }

    @pure def rcvOptIdent(v: State.Value, symPosOpt: Option[Position]): Option[(Option[AST.Exp], AST.Exp.Ident)] = {
      valueToExp(v) match {
        case Some(o) =>
          o match {
            case o: AST.Exp.Ident => return Some((None(), o))
            case o: AST.Exp.Select => return Some((o.receiverOpt, AST.Exp.Ident(o.id, o.attr)))
            case o => return Some((Some(o), AST.Exp.Ident(AST.Id("apply", AST.Attr(symPosOpt)), AST.ResolvedAttr(
              symPosOpt, TypeChecker.applyResOpt, o.typedOpt))))
          }
        case _ => return None()
      }
    }

    @pure def defsToEqs(cs: ISZ[State.Claim]): ISZ[State.Claim] = {
      var r = ISZ[State.Claim]()
      for (c <- cs) {
        c match {
          case c: State.Claim.Let.Def => r = r :+ State.Claim.Eq(c.sym, c.value)
          case _ =>
            if (!ignore(c)) {
              r = r :+ c
            }
        }
      }
      return r
    }

    @pure def equate(t: AST.Typed, e1: AST.Exp, e2: AST.Exp): AST.Exp = {
      return if (th.isGroundType(t)) AST.Exp.Binary(e1, AST.Exp.BinaryOp.Eq, e2, AST.ResolvedAttr(posOpt, eqResOpt, Some(t)), posOpt)
      else AST.Exp.Binary(e1, AST.Exp.BinaryOp.EquivUni, e2, AST.ResolvedAttr(posOpt, equivResOpt, Some(t)), posOpt)
    }

    @pure def inequate(t: AST.Typed, e1: AST.Exp, e2: AST.Exp): AST.Exp = {
      return if (th.isGroundType(t)) AST.Exp.Binary(e1, AST.Exp.BinaryOp.Ne, e2, AST.ResolvedAttr(posOpt, neResOpt, Some(t)), posOpt)
      else AST.Exp.Binary(e1, AST.Exp.BinaryOp.InequivUni, e2, AST.ResolvedAttr(posOpt, inequivResOpt, Some(t)), posOpt)
    }

    @pure def equateOpt(t: AST.Typed, e1: AST.Exp, e2: AST.Exp): Option[AST.Exp] = {
      return if (e1 == e2) None() else Some(equate(t, e1, e2))
    }

    @pure def simplify(cs: ISZ[AST.Exp]): ISZ[AST.Exp] = {
      var rs = ISZ[AST.Exp]()
      var ipMap = HashSMap.empty[AST.Exp, HashMap[AST.Exp, ISZ[AST.Exp]]]
      var inpMap = HashSMap.empty[AST.Exp, HashMap[AST.Exp, ISZ[AST.Exp]]]
      for (exp <- cs) {
        exp match {
          case exp: AST.Exp.Binary if exp.attr.resOpt == implyResOpt || exp.attr.resOpt == condImplyResOpt =>
            exp.left match {
              case left: AST.Exp.Unary if left.attr.resOpt == notResOpt =>
                inpMap = {
                  val key = th.normalizeExp(left.exp)
                  val m = inpMap.get(key).getOrElse(HashMap.empty)
                  val key2 = th.normalizeExp(exp.right)
                  inpMap + key ~> (m + key2 ~> (m.get(key2).getOrElse(ISZ()) :+ exp))
                }
                ipMap.get(th.normalizeExp(left.exp)).getOrElse(HashMap.empty).get(th.normalizeExp(exp.right)) match {
                  case Some(es) =>
                    rs = rs -- es
                    rs = rs :+ exp.right
                  case _ =>
                    rs = rs :+ exp
                }
              case left =>
                ipMap = {
                  val key = th.normalizeExp(left)
                  val m = ipMap.get(key).getOrElse(HashMap.empty)
                  val key2 = th.normalizeExp(exp.right)
                  ipMap + key ~> (m + key2 ~> (m.get(key2).getOrElse(ISZ()) :+ exp))
                }
                inpMap.get(th.normalizeExp(left)).getOrElse(HashMap.empty).get(th.normalizeExp(exp.right)) match {
                  case Some(es) =>
                    rs = rs -- es
                    rs = rs :+ exp.right
                  case _ =>
                    rs = rs :+ exp
                }
            }
          case _ => rs = rs :+ exp
        }
      }
      var changed = atRewrite
      var r = rs
      while (changed) {
        changed = F
        var atSubstMap = HashMap.empty[AST.Exp, AST.Exp]
        for (e <- r) {
          e match {
            case e: AST.Exp.Binary if isEquivResOpt(th, e.attr.resOpt, e.right.typedOpt.get) =>
              (e.left, e.right) match {
                case (left: AST.Exp.At, right) if left != right =>
                  atSubstMap = atSubstMap + left ~> right
                case (left, right: AST.Exp.At) if left != right =>
                  atSubstMap = atSubstMap + right ~> left
                case (_, _) =>
              }
            case _ =>
          }
        }
        if (atSubstMap.nonEmpty) {
          val es = AST.Util.ExpSubstitutor(atSubstMap)
          var r2 = ISZ[AST.Exp]()
          for (e <- r) {
            es.transformExp(e) match {
              case MSome(e2: AST.Exp.Binary) if isEquivLeftRight(e2) =>
                r2 = r2 :+ e
              case MSome(e2) =>
                r2 = r2 :+ e2
                changed = T
              case _ =>
                r2 = r2 :+ e
            }
          }
          r = r2
        }
      }
      return r
    }

    @pure def rewriteOld(cs: ISZ[AST.Exp]): ISZ[AST.Exp] = {
      if (!atRewrite) {
        return cs
      }
      def rewriteOldH(old: AST.Exp, e: AST.Exp): ISZ[AST.Exp] = {
        val map = HashMap.empty[AST.Exp, AST.Exp] + e ~> old
        val es = AST.Util.ExpSubstitutor(map)
        var r = ISZ[AST.Exp]()
        for (c <- cs) {
          c match {
            case AST.Exp.Binary(_: AST.Exp.Old, _, _) => r = r :+ c
            case _ =>
              es.transformExp(c) match {
                case MSome(c2) =>
                  //r = r :+ c
                  r = r :+ c2
                case _ => r = r :+ c
              }
          }
        }
        return r
      }
      for (i <- cs.size - 1 to 1 by -1) {
        cs(i) match {
          case AST.Exp.Binary(old: AST.Exp.Old, _, e) =>
            return rewriteOldH(old, e)
          case _ =>
        }
      }
      return cs
    }

    def computeAtNum(key: ClaimsToExps.AtPossKey, poss: ISZ[Position], num: Z, sym: State.Value.Sym): Z = {
      val m = atPossMap.get(key).getOrElse(HashMap.empty)
      val m2: HashMap[Z, (Z, State.Value.Sym)] = m.get(poss) match {
        case Some(m3) => m3
        case _ => HashMap.empty[Z, (Z, State.Value.Sym)]
      }
      m2.get(num) match {
        case Some((v, _)) => return v
        case _ =>
          var n: Z = 0
          for (m2 <- m.values) {
            n = n + m2.size
          }
          atPossMap = atPossMap + key ~> (m + poss ~> (m2 + num ~> (n, sym)))
          return n
      }
    }

    def letToExp(let: State.Claim.Let): Option[AST.Exp] = {
      val sym = let.sym
      val symPos = sym.pos
      val symPosOpt = Option.some(symPos)

      def letToExpH(): Option[AST.Exp] = {
        let match {
          case let: State.Claim.Let.CurrentId =>
            if (let.id == "Res" && context == let.context) {
              return Some(AST.Exp.Result(None(), AST.TypedAttr(symPosOpt, Some(sym.tipe))))
            } else {
              return Some(AST.Exp.Ident(AST.Id(let.id, AST.Attr(symPosOpt)), AST.ResolvedAttr(
                symPosOpt,
                Some(AST.ResolvedInfo.LocalVar(let.context, AST.ResolvedInfo.LocalVar.Scope.Current, F, F, let.id)),
                Some(sym.tipe))))
            }
          case let: State.Claim.Let.CurrentName =>
            return Some(th.nameToExp(let.ids, symPos).asExp)
          case let: State.Claim.Let.Id =>
            val linesFresh: ISZ[AST.Exp.LitZ] = if (includeFreshLines) {
              (for (pos <- let.poss) yield AST.Exp.LitZ(pos.beginLine, AST.Attr(Some(pos)))) :+ AST.Exp.LitZ(let.num, AST.Attr(symPosOpt))
            } else {
              ISZ()
            }
            val attr = AST.Attr(symPosOpt)
            if (let.context == context || let.context.isEmpty) {
              val key: ClaimsToExps.AtPossKey = (ISZ[String](), st"${(let.context :+ let.id, ".")}".render, sym.tipe)
              val n: Z = computeAtNum(key, let.poss, let.num, let.sym)
              if (let.inScope) {
                return Some(AST.Exp.At(None(), AST.Exp.Ident(AST.Id(let.id, attr), AST.ResolvedAttr(symPosOpt,
                  Some(AST.ResolvedInfo.LocalVar(let.context, AST.ResolvedInfo.LocalVar.Scope.Current, F, F, let.id)),
                  Some(sym.tipe))), AST.Exp.LitZ(n, attr), linesFresh, attr))
              } else {
                return Some(AST.Exp.At(Some(AST.Util.typedToType(sym.tipe, pos)),
                  AST.Exp.LitString(key._2, AST.Attr(symPosOpt)),
                  AST.Exp.LitZ(n, attr), linesFresh, attr))
              }
            } else {
              val key: ClaimsToExps.AtPossKey = (ISZ[String](), st"${(let.context :+ let.id, ".")}".render, sym.tipe)
              val n = computeAtNum(key, let.poss, let.num, let.sym)
              return Some(AST.Exp.At(Some(AST.Util.typedToType(sym.tipe, pos)),
                AST.Exp.LitString(key._2, AST.Attr(symPosOpt)),
                AST.Exp.LitZ(n, attr), linesFresh, attr))
            }
          case let: State.Claim.Let.Name =>
            val key: ClaimsToExps.AtPossKey = (let.ids, "", sym.tipe)
            val n = computeAtNum(key, let.poss, let.num, let.sym)
            val linesFresh: ISZ[AST.Exp.LitZ] = if (includeFreshLines) {
              (for (pos <- let.poss) yield AST.Exp.LitZ(pos.beginLine, AST.Attr(Some(pos)))) :+ AST.Exp.LitZ(let.num, AST.Attr(symPosOpt))
            } else {
              ISZ()
            }
            val attr = AST.Attr(symPosOpt)
            return Some(AST.Exp.At(None(), th.nameToExp(let.ids, symPos).asExp, AST.Exp.LitZ(n, attr), linesFresh, attr))
          case let: State.Claim.Let.Unary =>
            val (op, kind): (AST.Exp.UnaryOp.Type, AST.ResolvedInfo.BuiltIn.Kind.Type) = let.op match {
              case string"+" => (AST.Exp.UnaryOp.Plus, AST.ResolvedInfo.BuiltIn.Kind.UnaryPlus)
              case string"-" => (AST.Exp.UnaryOp.Minus, AST.ResolvedInfo.BuiltIn.Kind.UnaryMinus)
              case string"~" => (AST.Exp.UnaryOp.Complement, AST.ResolvedInfo.BuiltIn.Kind.UnaryComplement)
              case string"!" => (AST.Exp.UnaryOp.Not, AST.ResolvedInfo.BuiltIn.Kind.UnaryNot)
              case _ => halt(s"Infeasible: ${let.op}")
            }
            valueToExp(let.value) match {
              case Some(e) =>
                return Some(AST.Exp.Unary(op, e, AST.ResolvedAttr(symPosOpt, Some(AST.ResolvedInfo.BuiltIn(kind)),
                  Some(sym.tipe)), symPosOpt))
              case _ =>
                return None()
            }
          case let: State.Claim.Let.Binary =>
            @pure def isS(t: AST.Typed): B = {
              t match {
                case t: AST.Typed.Name => return (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName)
                case _ => return F
              }
            }

            @pure def sOp(op: String): Option[AST.Exp] = {
              (valueToExp(let.left), valueToExp(let.right)) match {
                case (Some(l), Some(r)) =>
                  var left = l
                  var right = r
                  val sType: AST.Typed.Name = if (op == AST.Exp.BinaryOp.Prepend) {
                    left match {
                      case l: AST.Exp.Tuple if l.args.size >= 2 => left = AST.Exp.Tuple(ISZ(left), l.attr)
                      case _ =>
                    }
                    let.right.tipe.asInstanceOf[AST.Typed.Name]
                  } else if (op == AST.Exp.BinaryOp.Append) {
                    right match {
                      case r: AST.Exp.Tuple if r.args.size >= 2 => right = AST.Exp.Tuple(ISZ(right), r.attr)
                      case _ =>
                    }
                    let.left.tipe.asInstanceOf[AST.Typed.Name]
                  } else {
                    let.left.tipe.asInstanceOf[AST.Typed.Name]
                  }
                  val info = th.typeMap.get(sType.ids).get.asInstanceOf[TypeInfo.Sig].methods.get(op).get
                  return Some(AST.Exp.Binary(left, op, right, AST.ResolvedAttr(symPosOpt, info.resOpt, Some(sym.tipe)), symPosOpt))
                case (_, _) => return None()
              }
            }

            val (op, kind): (String, AST.ResolvedInfo.BuiltIn.Kind.Type) = let.op match {
              case AST.Exp.BinaryOp.Add => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryAdd)
              case AST.Exp.BinaryOp.Sub => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinarySub)
              case AST.Exp.BinaryOp.Mul => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryMul)
              case AST.Exp.BinaryOp.Div => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryDiv)
              case AST.Exp.BinaryOp.Rem => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryRem)
              case AST.Exp.BinaryOp.CondAnd => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd)
              case AST.Exp.BinaryOp.CondOr => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr)
              case AST.Exp.BinaryOp.CondImply => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply)
              case "-->:" => (AST.Exp.BinaryOp.CondImply, AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply)
              case AST.Exp.BinaryOp.And => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryAnd)
              case AST.Exp.BinaryOp.Or => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryOr)
              case AST.Exp.BinaryOp.Xor => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryXor)
              case AST.Exp.BinaryOp.Imply => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryImply)
              case "->:" => (AST.Exp.BinaryOp.Imply, AST.ResolvedInfo.BuiltIn.Kind.BinaryImply)
              case AST.Exp.BinaryOp.Eq => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryEq)
              case AST.Exp.BinaryOp.Equiv => (AST.Exp.BinaryOp.EquivUni, AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv)
              case AST.Exp.BinaryOp.EquivUni => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv)
              case AST.Exp.BinaryOp.FpEq => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryFpEq)
              case AST.Exp.BinaryOp.Ne => (AST.Exp.BinaryOp.Ne, AST.ResolvedInfo.BuiltIn.Kind.BinaryNe)
              case AST.Exp.BinaryOp.Inequiv => (AST.Exp.BinaryOp.InequivUni, AST.ResolvedInfo.BuiltIn.Kind.BinaryInequiv)
              case AST.Exp.BinaryOp.InequivUni => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryInequiv)
              case AST.Exp.BinaryOp.FpNe => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryFpNe)
              case AST.Exp.BinaryOp.Lt => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryLt)
              case AST.Exp.BinaryOp.Le => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryLe)
              case AST.Exp.BinaryOp.Gt => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryGt)
              case AST.Exp.BinaryOp.Ge => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryGe)
              case AST.Exp.BinaryOp.Shl => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryShl)
              case AST.Exp.BinaryOp.Shr => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryShr)
              case AST.Exp.BinaryOp.Ushr => (let.op, AST.ResolvedInfo.BuiltIn.Kind.BinaryUshr)
              case AST.Exp.BinaryOp.Append if isS(let.left.tipe) => return sOp(let.op)
              case AST.Exp.BinaryOp.AppendAll if isS(let.left.tipe) => return sOp(let.op)
              case AST.Exp.BinaryOp.Prepend if isS(let.right.tipe) => return sOp(let.op)
              case AST.Exp.BinaryOp.RemoveAll if isS(let.left.tipe) => return sOp(let.op)
              case _ => halt(s"Infeasible: ${let.op}")
            }
            val leftOpt = valueToExp(let.left)
            val rightOpt = valueToExp(let.right)
            (leftOpt, rightOpt) match {
              case (Some(left), Some(right)) =>
                kind match {
                  case AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv => return Some(equate(let.left.tipe, left, right))
                  case AST.ResolvedInfo.BuiltIn.Kind.BinaryInequiv => return Some(inequate(let.left.tipe, left, right))
                  case _ =>
                }
                return Some(AST.Exp.Binary(left, op, right, AST.ResolvedAttr(symPosOpt,
                  Some(AST.ResolvedInfo.BuiltIn(kind)), Some(sym.tipe)), symPosOpt))
              case (_, _) => return None()
            }
          case let: State.Claim.Let.Def =>
            return valueToExp(let.value)
          case let: State.Claim.Let.And =>
            var es = ISZ[AST.Exp]()
            for (v <- let.args) {
              valueToExp(v) match {
                case Some(e) => es = es :+ e
                case _ =>
              }
            }
            return Some(AST.Util.bigAnd(es, posOpt))
          case let: State.Claim.Let.Or =>
            var es = ISZ[AST.Exp]()
            for (v <- let.args) {
              valueToExp(v) match {
                case Some(e) => es = es :+ e
                case _ => return None()
              }
            }
            return Some(AST.Util.bigOr(es, posOpt))
          case let: State.Claim.Let.Imply =>
            var es = ISZ[AST.Exp]()
            for (i <- 0 until let.args.size - 1) {
              valueToExp(let.args(i)) match {
                case Some(e) => es = es :+ e
                case _ =>
              }
            }
            valueToExp(let.args(let.args.size - 1)) match {
              case Some(e) =>
                if (es.isEmpty) {
                  return Some(e)
                }
                es = es :+ e
              case _ => return None()
            }
            return Some(AST.Util.bigImply(F, es, posOpt))
          case let: State.Claim.Let.Ite =>
            (valueToExp(let.cond), valueToExp(let.left), valueToExp(let.right)) match {
              case (Some(cond), Some(left), Some(right)) =>
                return Some(AST.Util.ite(cond, left, right, symPosOpt, Some(sym.tipe)))
              case (_, _, _) => return None()
            }
          case let: State.Claim.Let.TupleLit =>
            var es = ISZ[AST.Exp]()
            for (arg <- let.args) {
              valueToExp(arg) match {
                case Some(e) => es = es :+ e
                case _ => return None()
              }
            }
            return Some(AST.Exp.Tuple(es, AST.TypedAttr(symPosOpt, Some(sym.tipe))))
          case let: State.Claim.Let.AdtLit =>
            val info = th.typeMap.get(let.tipe.ids).get.asInstanceOf[TypeInfo.Adt]
            val ownerName = ops.ISZOps(let.tipe.ids).dropRight(1)
            var es = ISZ[AST.Exp]()
            for (arg <- let.args) {
              valueToExp(arg) match {
                case Some(e) => es = es :+ e
                case _ => return None()
              }
            }
            val nameExp = th.nameToExp(let.tipe.ids, symPos)
            return Some(AST.Exp.Invoke(
              if (ownerName.isEmpty || ownerName == AST.Typed.sireumName) None()
              else Some(th.nameToExp(ownerName, symPos).asExp),
              AST.Exp.Ident(AST.Id(let.tipe.ids(let.tipe.ids.size - 1), AST.Attr(symPosOpt)), AST.ResolvedAttr(
                symPosOpt,
                nameExp.resOpt,
                nameExp.typedOpt
              )),
              for (targ <- let.tipe.args) yield AST.Util.typedToType(targ, pos),
              es,
              AST.ResolvedAttr(
                symPosOpt,
                info.constructorResOpt,
                Some(sym.tipe)
              )
            ))
          case let: State.Claim.Let.SeqLit =>
            var es = ISZ[AST.Exp]()
            for (arg <- let.args) {
              valueToExp(arg.value) match {
                case Some(e) => es = es :+ e
                case _ => return None()
              }
            }
            val t = sym.tipe.asInstanceOf[AST.Typed.Name]
            val (name, targs): (ISZ[String], ISZ[AST.Type]) =
              if (t.args(0) == AST.Typed.z) {
                if (t.ids == AST.Typed.msName) {
                  if (t.args(1) == AST.Typed.z) (AST.Typed.zsName, ISZ())
                  else (AST.Typed.mszName, ISZ(AST.Util.typedToType(t.args(1), pos)))
                } else {
                  (AST.Typed.iszName, ISZ(AST.Util.typedToType(t.args(1), pos)))
                }
              } else {
                (t.ids, ISZ(AST.Util.typedToType(t.args(0), pos), AST.Util.typedToType(t.args(1), pos)))
              }
            val nameExp = th.nameToExp(name, symPos)
            val ident = AST.Exp.Ident(AST.Id(name(name.size - 1), AST.Attr(symPosOpt)),
              AST.ResolvedAttr(symPosOpt, nameExp.resOpt, nameExp.typedOpt))
            return Some(AST.Exp.Invoke(None(), ident, targs, es, AST.ResolvedAttr(symPosOpt,
              TypeChecker.sConstructorTypedResOpt(name, let.args.size)._2, Some(t))))
          case let: State.Claim.Let.Quant =>
            @pure def isInBoundResOpt(resOpt: Option[AST.ResolvedInfo]): B = {
              if (resOpt.isEmpty) {
                return F
              }
              resOpt.get match {
                case res: AST.ResolvedInfo.Method =>
                  return res.id == "isInBound" && (res.owner == AST.Typed.isName || res.owner == AST.Typed.msName)
                case _ =>
              }
              return F
            }

            @pure def isQuantParamIndex(fcontext: ISZ[String], idOpt: Option[AST.Id], arg: AST.Exp): B = {
              if (idOpt.isEmpty) {
                return F
              }
              arg match {
                case arg: AST.Exp.Ident =>
                  arg.attr.resOpt match {
                    case Some(res: AST.ResolvedInfo.LocalVar) =>
                      return res.id == idOpt.get.value && res.context == fcontext
                    case _ =>
                  }
                case _ =>
              }
              return F
            }

            @pure def isQuantRange(fcontext: ISZ[String], idOpt: Option[AST.Id], range: AST.Exp.Binary): (B, B) = {
              if (idOpt.isEmpty) {
                return (F, F)
              }
              val id = idOpt.get.value
              if (range.attr.resOpt != andResOpt) {
                return (F, F)
              }
              (range.left, range.right) match {
                case (left: AST.Exp.Binary, right: AST.Exp.Binary) if left.attr.resOpt == leResOpt =>
                  (left.right, right.left) match {
                    case (lr: AST.Exp.Ident, rl: AST.Exp.Ident) =>
                      (lr.resOpt, rl.resOpt) match {
                        case (Some(lrRes: AST.ResolvedInfo.LocalVar), Some(rlRes: AST.ResolvedInfo.LocalVar)) =>
                          if (lrRes.id == id && rlRes.id == id && lrRes.context == fcontext && rlRes.context == fcontext) {
                            // skip
                          } else {
                            return (F, F)
                          }
                        case _ => return (F, F)
                      }
                    case _ =>
                  }
                  if (right.attr.resOpt == leResOpt) {
                    return (T, T)
                  } else if (right.attr.resOpt == ltResOpt) {
                    return (T, F)
                  }
                case _ =>
              }
              return (F, F)
            }

            @pure def paramIdx(idOpt1: Option[AST.Id], idOpt2: Option[AST.Id]): B = {
              (idOpt1, idOpt2) match {
                case (Some(id1), Some(id2)) => return id1.value == s"${id2.value}${Logika.idxSuffix}"
                case _ =>
              }
              return F
            }

            @pure def isIdent(fcontext: ISZ[String], id: AST.Id, e: AST.Exp): B = {
              e match {
                case e: AST.Exp.Ident =>
                  e.resOpt match {
                    case Some(res: AST.ResolvedInfo.LocalVar) => return res.id == id.value && res.context == fcontext
                    case _ =>
                  }
                case _ =>
              }
              return F
            }

            val exp: AST.Exp = toExp(State.Claim.And(let.claims)) match {
              case Some(e) => e
              case _ => return None()
            }
            var params = ISZ[AST.Exp.Fun.Param]()
            var fcontext = ISZ[String]()
            val attr = AST.Attr(symPosOpt)
            var argTypes = ISZ[AST.Typed]()
            for (x <- let.vars) {
              fcontext = x.context
              argTypes = argTypes :+ x.tipe
              val t = AST.Util.typedToType(x.tipe, pos)
              params = params :+ AST.Exp.Fun.Param(Some(AST.Id(x.id, attr)), Some(t), Some(x.tipe))
            }
            exp match {
              case exp: AST.Exp.Binary if (let.isAll && (exp.attr.resOpt == implyResOpt ||
                exp.attr.resOpt == condImplyResOpt)) || (!let.isAll && (exp.attr.resOpt == andResOpt ||
                exp.attr.resOpt == condAndResOpt)) =>
                exp.left match {
                  case left: AST.Exp.Invoke if left.receiverOpt.nonEmpty && isInBoundResOpt(left.ident.attr.resOpt) =>
                    val seq = left.receiverOpt.get
                    val t = seq.typedOpt.get.asInstanceOf[AST.Typed.Name]
                    if (params.size == 2 && paramIdx(params(0).idOpt, params(1).idOpt) &&
                      isQuantParamIndex(fcontext, params(0).idOpt, left.args(0))) {
                      exp.right match {
                        case right: AST.Exp.Binary if (let.isAll && right.attr.resOpt == implyResOpt) ||
                          (!let.isAll && right.attr.resOpt == andResOpt) =>
                          right.left match {
                            case rl: AST.Exp.Binary if isIdent(fcontext, params(1).idOpt.get, rl.right) &&
                              rl.attr.resOpt == eqResOpt || rl.attr.resOpt == equivResOpt =>
                              rl.left match {
                                case rll: AST.Exp.Invoke if rll.args.size == 1 &&
                                  isIdent(fcontext, params(0).idOpt.get, rll.args(0)) =>
                                  if (left.receiverOpt == Some[AST.Exp](rll.ident)) {
                                    val fun = AST.Exp.Fun(fcontext, ISZ(params(1)(tipeOpt = None())),
                                      AST.Stmt.Expr(right.right, AST.TypedAttr(symPosOpt, AST.Typed.bOpt)),
                                      AST.TypedAttr(symPosOpt, Some(AST.Typed.Fun(AST.Purity.Pure, F, ISZ(argTypes(1)), AST.Typed.b))))
                                    return Some(AST.Exp.QuantEach(let.isAll, rll.ident, fun, AST.ResolvedAttr(symPosOpt,
                                      Some(AST.ResolvedInfo.LocalVar(fcontext, AST.ResolvedInfo.LocalVar.Scope.Current,
                                        F, T, params(1).idOpt.get.value)),
                                      AST.Typed.bOpt)))
                                  }
                                case _ =>
                              }
                            case _ =>
                          }
                        case _ =>
                      }
                    } else if (params.size == 1 && isQuantParamIndex(fcontext, params(0).idOpt, left.args(0))) {
                      val (resOpt, typedOpt): (Option[AST.ResolvedInfo], Option[AST.Typed]) = {
                        val info = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Sig].methods.get("indices").get
                        (info.resOpt, info.typedOpt)
                      }
                      val fun = AST.Exp.Fun(fcontext, ISZ(params(0)(tipeOpt = None())), AST.Stmt.Expr(exp.right,
                        AST.TypedAttr(symPosOpt, AST.Typed.bOpt)), AST.TypedAttr(symPosOpt,
                        Some(AST.Typed.Fun(AST.Purity.Pure, F, argTypes, AST.Typed.b))))
                      return Some(AST.Exp.QuantEach(let.isAll, AST.Exp.Select(left.receiverOpt, AST.Id("indices", attr),
                        ISZ(), AST.ResolvedAttr(symPosOpt, resOpt, typedOpt)), fun, AST.ResolvedAttr(symPosOpt,
                        Some(AST.ResolvedInfo.LocalVar(fcontext, AST.ResolvedInfo.LocalVar.Scope.Current, F, T,
                          params(0).idOpt.get.value)),
                        AST.Typed.bOpt)))
                    }
                  case left: AST.Exp.Binary if params.size == 1 =>
                    val (ok, isExact) = isQuantRange(fcontext, params(0).idOpt, left)
                    if (ok) {
                      val lo = left.left.asInstanceOf[AST.Exp.Binary].left
                      val hi = left.right.asInstanceOf[AST.Exp.Binary].right
                      val fun = AST.Exp.Fun(fcontext, ISZ(params(0)(tipeOpt = None())), AST.Stmt.Expr(exp.right,
                        AST.TypedAttr(symPosOpt, AST.Typed.bOpt)), AST.TypedAttr(symPosOpt,
                        Some(AST.Typed.Fun(AST.Purity.Pure, F, argTypes, AST.Typed.b))))
                      return Some(AST.Exp.QuantRange(let.isAll, lo, hi, isExact, fun, AST.ResolvedAttr(symPosOpt,
                        Some(AST.ResolvedInfo.LocalVar(fcontext, AST.ResolvedInfo.LocalVar.Scope.Current, F, T,
                          params(0).idOpt.get.value)),
                        AST.Typed.bOpt)))
                    }
                  case _ =>
                }
              case _ =>
            }
            val fun = AST.Exp.Fun(fcontext, params, AST.Stmt.Expr(exp, AST.TypedAttr(symPosOpt, AST.Typed.bOpt)),
              AST.TypedAttr(symPosOpt, Some(AST.Typed.Fun(AST.Purity.Pure, F, argTypes, AST.Typed.b))))
            return Some(AST.Exp.QuantType(let.isAll, fun, attr))
          case let: State.Claim.Let.FieldLookup =>
            valueToExp(let.adt) match {
              case Some(o) =>
                let.adt.tipe match {
                  case t: AST.Typed.Name =>
                    th.typeMap.get(t.ids).get match {
                      case ti: TypeInfo.Adt =>
                        ti.vars.get(let.id) match {
                          case Some(info) =>
                            return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                              AST.ResolvedAttr(symPosOpt, Some(AST.ResolvedInfo.Var(info.isInObject, info.ast.isSpec,
                                info.ast.isVal, info.owner, let.id)), Some(sym.tipe))))
                          case _ =>
                            val info = ti.specVars.get(let.id).get
                            return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                              AST.ResolvedAttr(symPosOpt, Some(AST.ResolvedInfo.Var(info.isInObject, T, info.ast.isVal,
                                info.owner, let.id)), Some(sym.tipe))))
                        }
                      case ti: TypeInfo.Sig =>
                        ti.specVars.get(let.id) match {
                          case Some(info) =>
                            return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                              AST.ResolvedAttr(symPosOpt, Some(AST.ResolvedInfo.Var(info.isInObject, T, info.ast.isVal,
                                info.owner, let.id)), Some(sym.tipe))))
                          case _ =>
                        }
                        val info = ti.methods.get(let.id).get
                        val tOpt: Option[AST.Typed.Fun] = info.typedOpt match {
                          case Some(_: AST.Typed.Method) => Some(AST.Typed.Fun(AST.Purity.Pure, T, ISZ(), sym.tipe))
                          case Some(t) => halt(s"Infeasible: $t")
                          case _ => None()
                        }
                        return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                          AST.ResolvedAttr(symPosOpt, Some(AST.ResolvedInfo.Method(info.isInObject, AST.MethodMode.Method, ISZ(),
                            info.owner, let.id, ISZ(), tOpt, ISZ(), ISZ())), Some(sym.tipe))))
                      case info: TypeInfo.SubZ =>
                        assert(let.id == "toZ")
                        return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                          AST.ResolvedAttr(symPosOpt, TypeChecker.extResOpt(F, info.name, let.id, ISZ(),
                            AST.Typed.Fun(AST.Purity.Pure, T, ISZ(), AST.Typed.z)),
                            Some(sym.tipe))))
                      case info: TypeInfo.Enum =>
                        assert(let.id == "ordinal" || let.id == "name")
                        return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                          AST.ResolvedAttr(symPosOpt, TypeChecker.extResOpt(F, info.name, let.id, ISZ(),
                            AST.Typed.Fun(AST.Purity.Pure, T, ISZ(), AST.Typed.z)),
                            Some(sym.tipe))))
                      case ti => halt(s"Infeasible: $ti")
                    }
                  case t: AST.Typed.Tuple =>
                    val n = org.sireum.Z(ops.StringOps(let.id).substring(1, let.id.size)).get
                    o match {
                      case o: AST.Exp.Tuple =>
                        return Some(o.args(n - 1))
                      case _ =>
                        return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                          AST.ResolvedAttr(symPosOpt, Some(AST.ResolvedInfo.Tuple(t.args.size, n)), Some(sym.tipe))))
                    }
                  case t: AST.Typed.TypeVar if t.isIndex =>
                    assert(let.id == "toZ")
                    return Some(AST.Exp.Select(Some(o), AST.Id(let.id, AST.Attr(symPosOpt)), ISZ(),
                      AST.ResolvedAttr(symPosOpt, TypeChecker.extResOpt(F, ISZ(t.id), let.id, ISZ(),
                        AST.Typed.Fun(AST.Purity.Pure, T, ISZ(), AST.Typed.z)),
                        Some(sym.tipe))))
                  case t => halt(s"Infeasible: $t")
                }
              case _ => return None()
            }
          case let: State.Claim.Let.SeqStore =>
            (rcvOptIdent(let.seq, symPosOpt), valueToExp(let.index), valueToExp(let.element)) match {
              case (Some((rcvOpt, ident)), Some(index), Some(element)) =>
                val (_, resOpt) = TypeChecker.sStoreTypedResOpt(let.seq.tipe.asInstanceOf[AST.Typed.Name], 1)
                return Some(AST.Exp.Invoke(rcvOpt, ident, ISZ(), ISZ(AST.Exp.Binary(index,
                  AST.Exp.BinaryOp.MapsTo, element, AST.ResolvedAttr(symPosOpt,
                    Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryMapsTo)), Some(AST.Typed.Tuple(ISZ(
                      let.index.tipe, let.element.tipe)))), symPosOpt)),
                  AST.ResolvedAttr(symPosOpt, resOpt, Some(sym.tipe))))
              case (_, _, _) => return None()
            }
          case let: State.Claim.Let.SeqLookup =>
            (rcvOptIdent(let.seq, symPosOpt), valueToExp(let.index)) match {
              case (Some((rcvOpt, ident)), Some(index)) =>
                val (_, resOpt) = TypeChecker.sSelectTypedResOpt(let.seq.tipe.asInstanceOf[AST.Typed.Name], F)
                return Some(AST.Exp.Invoke(rcvOpt, ident, ISZ(), ISZ(index), AST.ResolvedAttr(symPosOpt, resOpt,
                  Some(sym.tipe))))
              case (_, _) =>
                return None()
            }
          case let: State.Claim.Let.SeqInBound =>
            (valueToExp(let.seq), valueToExp(let.index)) match {
              case (Some(o), Some(index)) =>
                val info = th.typeMap.get(let.seq.tipe.asInstanceOf[AST.Typed.Name].ids).get.asInstanceOf[TypeInfo.Sig].methods.get("isInBound").get
                val ident = AST.Exp.Ident(AST.Id("isInBound", AST.Attr(symPosOpt)), AST.ResolvedAttr(symPosOpt, info.resOpt, info.typedOpt))
                return Some(AST.Exp.Invoke(Some(o), ident, ISZ(), ISZ(index),
                  AST.ResolvedAttr(symPosOpt, info.resOpt, Some(sym.tipe))))
              case _ => return None()
            }
          case let: State.Claim.Let.TypeTest =>
            valueToExp(let.value) match {
              case Some(e) =>
                return Some(AST.Exp.Select(Some(e), AST.Id("isInstanceOf", AST.Attr(symPosOpt)),
                  ISZ(AST.Util.typedToType(let.tipe, pos)), AST.ResolvedAttr(symPosOpt, lang.tipe.TypeChecker.isInstanceOfResOpt,
                    AST.Typed.bOpt)))
              case _ => return None()
            }
          case let: State.Claim.Let.ProofFunApply =>
            if (let.pf.receiverTypeOpt.nonEmpty) {
              val rcv = let.args(0)
              valueToExp(rcv) match {
                case Some(o) =>
                  var es = ISZ[AST.Exp]()
                  for (i <- 1 until let.args.size) {
                    valueToExp(let.args(i)) match {
                      case Some(e) => es = es :+ e
                      case _ => return None()
                    }
                  }
                  val (resOpt, typedOpt): (Option[AST.ResolvedInfo], Option[AST.Typed]) =
                    th.typeMap.get(rcv.tipe.asInstanceOf[AST.Typed.Name].ids).get match {
                      case info: TypeInfo.Sig =>
                        info.methods.get(let.pf.id) match {
                          case Some(minfo) => (minfo.resOpt, minfo.typedOpt)
                          case _ =>
                            info.specMethods.get(let.pf.id) match {
                              case Some(minfo) => (minfo.resOpt, minfo.typedOpt)
                              case _ => (None(), None())
                            }
                        }
                      case info: TypeInfo.Adt =>
                        info.methods.get(let.pf.id) match {
                          case Some(minfo) => (minfo.resOpt, minfo.typedOpt)
                          case _ =>
                            info.specMethods.get(let.pf.id) match {
                              case Some(minfo) => (minfo.resOpt, minfo.typedOpt)
                              case _ => (None(), None())
                            }
                        }
                      case _ => halt("Infeasible")
                    }
                  if (resOpt.isEmpty) {
                    return None()
                  }
                  if (let.pf.isByName) {
                    return Some(AST.Exp.Select(Some(o), AST.Id(let.pf.id, AST.Attr(symPosOpt)), ISZ(), AST.ResolvedAttr(symPosOpt, resOpt,
                      Some(sym.tipe))))
                  } else {
                    return Some(AST.Exp.Invoke(Some(o), AST.Exp.Ident(AST.Id(let.pf.id, AST.Attr(symPosOpt)),
                      AST.ResolvedAttr(symPosOpt, resOpt, typedOpt)), ISZ(), es, AST.ResolvedAttr(symPosOpt, resOpt,
                      Some(sym.tipe))))
                  }
                case _ => return None()
              }
            } else {
              var es = ISZ[AST.Exp]()
              for (arg <- let.args) {
                valueToExp(arg) match {
                  case Some(e) => es = es :+ e
                  case _ => return None()
                }
              }
              val nameExp: ISZ[String] = th.typeMap.get(let.pf.context) match {
                case Some(info: TypeInfo.Enum) => info.owner
                case _ => let.pf.context
              }
              val name = let.pf.context :+ let.pf.id
              val rcvOpt: Option[AST.Exp] = if (let.pf.context.nonEmpty) Some(th.nameToExp(nameExp, symPos).asExp) else None()
              val (resOpt, typedOpt): (Option[AST.ResolvedInfo], Option[AST.Typed]) = th.nameMap.get(name) match {
                case Some(info: Info.Method) => (info.resOpt, info.typedOpt)
                case Some(info: Info.SpecMethod) => (info.resOpt, info.typedOpt)
                case Some(info: Info.ExtMethod) => (info.resOpt, info.typedOpt)
                case _ =>
                  th.typeMap.get(let.pf.context) match {
                    case Some(_: TypeInfo.SubZ) =>
                      let.pf.id.native match {
                        case "randomSeed" =>
                          val paramNames = ISZ[String]("seed")
                          val f = AST.Typed.Fun(AST.Purity.Pure, F, ISZ(AST.Typed.z), sym.tipe)
                          (TypeChecker.extResOpt(T, let.pf.context, let.pf.id, paramNames, f),
                            Some(AST.Typed.Method(T, AST.MethodMode.Ext, ISZ(), let.pf.context, let.pf.id, paramNames, f)))
                        case "randomSeedBetween" =>
                          val paramNames = ISZ[String]("seed", "min", "max")
                          val f = AST.Typed.Fun(AST.Purity.Pure, F, ISZ(AST.Typed.z, sym.tipe, sym.tipe), sym.tipe)
                          (TypeChecker.extResOpt(T, let.pf.context, let.pf.id, paramNames, f),
                            Some(AST.Typed.Method(T, AST.MethodMode.Ext, ISZ(), let.pf.context, let.pf.id, paramNames, f)))
                        case _ => halt(s"Unexpected: $let")
                      }
                    case _ => (None(), None())
                  }
              }
              if (resOpt.isEmpty) {
                return None()
              }
              if (let.pf.isByName) {
                return Some(AST.Exp.Select(rcvOpt, AST.Id(let.pf.id, AST.Attr(symPosOpt)), ISZ(), AST.ResolvedAttr(symPosOpt, resOpt,
                  Some(sym.tipe))))
              } else {
                return Some(AST.Exp.Invoke(rcvOpt, AST.Exp.Ident(AST.Id(let.pf.id, AST.Attr(symPosOpt)),
                  AST.ResolvedAttr(symPosOpt, resOpt, typedOpt)), ISZ(), es, AST.ResolvedAttr(symPosOpt, resOpt,
                  Some(sym.tipe))))
              }
            }
          case let: State.Claim.Let.Apply =>
            var es = ISZ[AST.Exp]()
            for (arg <- let.args) {
              valueToExp(arg) match {
                case Some(e) => es = es :+ e
                case _ => return None()
              }
            }
            assert(let.isLocal && let.context == context, s"${let.isLocal}: ${let.context} == ${context}")
            val ident = AST.Exp.Ident(AST.Id(let.id, AST.Attr(symPosOpt)), AST.ResolvedAttr(symPosOpt,
              Some(AST.ResolvedInfo.LocalVar(let.context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, let.id)),
              Some(let.tipe)))
            return Some(AST.Exp.Invoke(None(), ident, ISZ(), es, AST.ResolvedAttr(symPosOpt, ident.resOpt,
              Some(sym.tipe))))
          case let: State.Claim.Let.FieldStore =>
            (rcvOptIdent(let.adt, symPosOpt), valueToExp(let.value)) match {
              case (Some((rcvOpt, ident)), Some(e)) =>
                val t = let.adt.tipe.asInstanceOf[AST.Typed.Name]
                th.typeMap.get(t.ids).get match {
                  case _: TypeInfo.Adt =>
                    val (_, resOpt, _, paramNames) = TypeChecker.adtCopyTypedResOpt(F, th, symPosOpt, t, ISZ(let.id), message.Reporter.create)
                    val index = ops.ISZOps(paramNames).indexOf(let.id)
                    val r = AST.Exp.InvokeNamed(rcvOpt, ident, ISZ(), ISZ(AST.NamedArg(AST.Id(let.id, AST.Attr(symPosOpt)),
                      e, index)), AST.ResolvedAttr(symPosOpt, resOpt, Some(sym.tipe)))
                    return Some(r)
                  case _: TypeInfo.Sig =>
                    val (_, resOpt, _, paramNames) = TypeChecker.adtCopyTypedResOpt(F, th, symPosOpt, t, ISZ(let.id), message.Reporter.create)
                    val index = ops.ISZOps(paramNames).indexOf(let.id)
                    val r = AST.Exp.InvokeNamed(rcvOpt, ident, ISZ(), ISZ(AST.NamedArg(AST.Id(let.id, AST.Attr(symPosOpt)),
                      e, index)), AST.ResolvedAttr(symPosOpt, resOpt, Some(sym.tipe)))
                    return Some(r)
                  case info => halt(s"Infeasible: $info")
                }
              case _ =>
            }
            return None()
          case let: State.Claim.Let.Random =>
            return if (let.hidden) None() else Some(symAt(".random", let.sym))
        }
      }

      val rOpt = letToExpH()
      rOpt match {
        case Some(e) => e match {
          case e: AST.Exp.Select => e.resOpt match {
            case Some(res: AST.ResolvedInfo.Method) if res.tpeOpt.get.isByName =>
              e(attr = e.attr(typedOpt = Some(res.tpeOpt.get.ret)))
            case _ =>
          }
          case _ =>
        }
        case _ =>
      }
      return rOpt
    }

    def valueToExp(value: State.Value): Option[AST.Exp] = {
      @pure def subZPrefix(t: AST.Typed.Name): String = {
        return ops.StringOps(t.ids(t.ids.size - 1)).firstToLower
      }

      val attr = AST.Attr(Some(value.pos))
      value match {
        case value: State.Value.Sym =>
          if (!mulSymDefs.contains(value.num)) {
            letMap.get(value.num) match {
              case Some(lets) =>
                if (lets.size == 1) {
                  return letToExp(lets.elements(0))
                } else {
                  for (let <- lets.elements) {
                    let match {
                      case _: State.Claim.Let.Id =>
                        letToExp(let) match {
                          case Some(e) => return Some(e)
                          case _ =>
                        }
                      case _: State.Claim.Let.Name =>
                        letToExp(let) match {
                          case Some(e) => return Some(e)
                          case _ =>
                        }
                      case _ =>
                    }
                  }
                }
              case _ =>
            }
          }
          return Some(symAt(".temp", value))
        case value: State.Value.B => return Some(AST.Exp.LitB(value.value, attr))
        case value: State.Value.Z => return Some(AST.Exp.LitZ(value.value, attr))
        case value: State.Value.R => return Some(AST.Exp.LitR(value.value, attr))
        case value: State.Value.C => return Some(AST.Exp.LitC(value.value, attr))
        case value: State.Value.F32 => return Some(AST.Exp.LitF32(value.value, attr))
        case value: State.Value.F64 => return Some(AST.Exp.LitF64(value.value, attr))
        case value: State.Value.String => return Some(AST.Exp.LitString(value.value, attr))
        case value: State.Value.Enum => return Some(th.nameToExp(value.owner :+ value.id, value.pos).asExp)
        case value: State.Value.S8 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S8.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.S16 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S16.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.S32 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S32.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.S64 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.S64.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.U8 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U8.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.U16 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U16.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.U32 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U32.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.U64 =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(conversions.U64.toZ(value.value).string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.Range =>
          return Some(AST.Exp.StringInterpolate(subZPrefix(value.tipe),
            ISZ(AST.Exp.LitString(value.value.string, attr)), ISZ(),
            AST.TypedAttr(attr.posOpt, Some(value.tipe))))
        case value: State.Value.Unit => halt(s"Infeasible: $value")
      }
    }

    def symAt(id: String, sym: State.Value.Sym): AST.Exp.At = {
      val attr = AST.Attr(Some(sym.pos))
      val key: ClaimsToExps.AtPossKey = (ISZ[String](), id, sym.tipe)
      val n = computeAtNum(key, ISZ(sym.pos), 0, sym)
      val linesFresh: ISZ[AST.Exp.LitZ] =
        if (includeFreshLines) ISZ(AST.Exp.LitZ(sym.pos.beginLine, attr), AST.Exp.LitZ(sym.num, attr))
        else ISZ()
      return AST.Exp.At(Some(AST.Util.typedToType(sym.tipe, pos)), AST.Exp.LitString(id, attr),
        AST.Exp.LitZ(n, attr), linesFresh, attr)
    }

    def toExp(claim: State.Claim): Option[AST.Exp] = {
      def toOldOrInput(isOld: B, isLocal: B, isSpec: B, owner: ISZ[String], id: String, value: State.Value, pos: Position): Option[AST.Exp] = {
        val posOpt = Option.some(pos)
        val tOpt = Option.some(value.tipe)
        val exp: AST.Exp = if (isLocal) {
          if (id == "this") {
            AST.Exp.This(owner, AST.TypedAttr(posOpt, tOpt))
          } else {
            AST.Exp.Ident(AST.Id(id, AST.Attr(posOpt)), AST.ResolvedAttr(posOpt,
              Some(AST.ResolvedInfo.LocalVar(owner, AST.ResolvedInfo.LocalVar.Scope.Current, isSpec, F, id)), tOpt))
          }
        } else {
          th.nameToExp(owner :+ id, pos).asExp
        }
        val r: Option[AST.Exp] = valueToExp(value) match {
          case Some(valueExp) => Some(equate(value.tipe,
            if (isOld) AST.Exp.Old(exp, AST.Attr(exp.posOpt)) else AST.Exp.Input(exp, AST.Attr(exp.posOpt)), valueExp))
          case _ => None()
        }
        return r
      }
      if (plugins.nonEmpty) {
        for (p <- plugins if p.canHandleExp(claim)) {
          return p.handleExp(this, claim)
        }
      }
      claim match {
        case claim: State.Claim.And =>
          var es = ISZ[AST.Exp]()
          for (c <- defsToEqs(claim.claims)) {
            toExp(c) match {
              case Some(e: AST.Exp.Binary) if isEquivLeftRight(e) =>
              case Some(e) => es = es :+ e
              case _ =>
            }
          }
          return Some(AST.Util.bigAnd(es, posOpt))
        case claim: State.Claim.Or =>
          var es = ISZ[AST.Exp]()
          for (c <- defsToEqs(claim.claims)) {
            toExp(c) match {
              case Some(e) => es = es :+ e
              case _ => return None()
            }
          }
          return Some(AST.Util.bigOr(es, posOpt))
        case claim: State.Claim.Imply =>
          var es = ISZ[AST.Exp]()
          val cs = defsToEqs(claim.claims)
          for (i <- 0 until cs.size - 1) {
            toExp(cs(i)) match {
              case Some(e) => es = es :+ e
              case _ =>
            }
          }
          if (es.isEmpty) {
            return None()
          }
          toExp(cs(cs.size - 1)) match {
            case Some(e) => es = es :+ e
            case _ => return None()
          }
          return Some(AST.Util.bigImply(claim.isCond, es, posOpt))
        case claim: State.Claim.Prop =>
          valueToExp(claim.value) match {
            case Some(e) =>
              return Some(
                if (claim.isPos) e
                else AST.Exp.Unary(AST.Exp.UnaryOp.Not, e, AST.ResolvedAttr(posOpt,
                  Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.UnaryNot)), AST.Typed.bOpt), posOpt))
            case _ =>
              return None()
          }
        case claim: State.Claim.If =>
          val condOpt = valueToExp(claim.cond)
          val leftOpt = toExp(State.Claim.And(claim.tClaims))
          val rightOpt = toExp(State.Claim.And(claim.fClaims))
          (condOpt, leftOpt, rightOpt) match {
            case (Some(cond), Some(left), Some(right)) => return Some(AST.Util.ite(cond, left, right, posOpt, AST.Typed.bOpt))
            case (_, _, _) => return None()
          }
        case claim: State.Claim.Let.CurrentId =>
          (letToExp(claim), valueToExp(claim.sym)) match {
            case (Some(e1), Some(e2)) => return equateOpt(claim.sym.tipe, e1, e2)
            case _ => return None()
          }
        case claim: State.Claim.Let.CurrentName =>
          (letToExp(claim), valueToExp(claim.sym)) match {
            case (Some(e1), Some(e2)) => return equateOpt(claim.sym.tipe, e1, e2)
            case _ => return None()
          }
        case claim: State.Claim.Let.Id =>
          (letToExp(claim), valueToExp(claim.sym)) match {
            case (Some(e1), Some(e2)) => return equateOpt(claim.sym.tipe, e1, e2)
            case _ => return None()
          }
        case claim: State.Claim.Let.Name =>
          (letToExp(claim), valueToExp(claim.sym)) match {
            case (Some(e1), Some(e2)) => return equateOpt(claim.sym.tipe, e1, e2)
            case _ => return None()
          }
        case claim: State.Claim.Eq =>
          letMap.get(claim.v1.num) match {
            case Some(lets) if lets.size > 1 &&
              ops.ISZOps(lets.elements).forall((let: State.Claim.Let) => let.isInstanceOf[State.Claim.Let.Def]) =>
              eqMap.get(claim.v1.num) match {
                case Some(eqs) if eqs.size == 1 =>
                  val v1 = eqs.elements(0).v1
                  (valueToExp(v1), valueToExp(claim.v2)) match {
                    case (Some(e1), Some(e2)) => return equateOpt(v1.tipe, e1, e2)
                    case (_, _) => return None()
                  }
                case _ =>
              }
            case _ =>
          }
          (valueToExp(claim.v1), valueToExp(claim.v2)) match {
            case (Some(e1), Some(e2)) =>
              return equateOpt(claim.v1.tipe, e1, e2)
            case _ => return None()
          }
        case claim: State.Claim.Let => return letToExp(claim)
        case claim: State.Claim.Old => return toOldOrInput(T, claim.isLocal, claim.isSpec, claim.owner, claim.id,
          claim.value, claim.pos)
        case claim: State.Claim.Input => return toOldOrInput(F, claim.isLocal, claim.isSpec, claim.owner, claim.id,
          claim.value, claim.pos)
        case _: State.Claim.Label => return None()
        case _: State.Claim.Custom => return None()
        case claim => halt(s"Infeasible: $claim")
      }
    }

    @pure def translate(claims: ISZ[State.Claim]): ISZ[AST.Exp] = {
      var r = ISZ[AST.Exp]()

      for (i <- 0 until claims.size if !ignore(claims(i))) {
        toExp(claims(i)) match {
          case Some(AST.Util.trueLit) =>
          case Some(exp: AST.Exp.Binary) if isEquivLeftRight(exp) =>
          case Some(exp) =>
            r = r :+ exp
          case _ =>
        }
      }

      return rewriteOld(simplify(r))
    }
  }

  @record class LocalSaver(val depth: Z, val ctx: ISZ[String], var localMap: LocalSaveMap) extends MStateTransformer {
    override def preStateClaimLetCurrentId(o: State.Claim.Let.CurrentId): MStateTransformer.PreResult[State.Claim.Let] = {
      if (o.context == ctx) {
        val id = State.Claim.Let.Id(o.sym, F, o.context, o.id, depth, ISZ())
        localMap = localMap + id ~> o
        return MStateTransformer.PreResult(F, MSome(id))
      }
      return MStateTransformer.PreResultStateClaimLetCurrentId
    }
  }

  @datatype class PrePostLocalRestorer(val localMap: LocalSaveMap) extends StateTransformer.PrePost[B] {
    override def preStateClaimLetId(ctx: B, o: State.Claim.Let.Id): StateTransformer.PreResult[B, State.Claim.Let] = {
      localMap.get(o) match {
        case Some(id) => return StateTransformer.PreResult(ctx, F, Some(id))
        case _ => return StateTransformer.PreResult(ctx, F, None())
      }
    }
  }

  @record class AtSymRewriter(val logika: Logika,
                              val atMap: ClaimsToExps.AtMap,
                              var state: State,
                              val reporter: Reporter) extends AST.MTransformer {
    override def postExpAt(o: AST.Exp.At): MOption[AST.Exp] = {
      val (s1, sym) = logika.evalAtH(state, atMap, o, reporter)
      state = s1
      return MSome(AST.Exp.Sym(sym.asInstanceOf[State.Value.Sym].num, AST.TypedAttr(o.posOpt, o.typedOpt)))
    }
  }

  type LocalSaveMap = HashMap[State.Claim.Let.Id, State.Claim.Let.CurrentId]

  val builtInTypeNames: HashSet[ISZ[String]] = HashSet ++ ISZ(
    AST.Typed.bName, AST.Typed.zName, AST.Typed.cName, AST.Typed.stringName, AST.Typed.f32Name, AST.Typed.f64Name,
    AST.Typed.rName, AST.Typed.stName, AST.Typed.isName, AST.Typed.msName
  )

  val condImplyResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply))
  val condAndResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd))
  val andResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryAnd))
  val implyResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryImply))
  val leResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryLe))
  val ltResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryLt))
  val eqResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryEq))
  val neResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryNe))
  val equivResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv))
  val inequivResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryInequiv))
  val notResOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.UnaryNot))

  @strictpure def emptyLocalSaveMap: LocalSaveMap = HashMap.empty

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

  def value2ST(smt2: Smt2, lets: HashMap[Z, ISZ[State.Claim.Let]],
               declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): (Config, State.Value, Reporter) => ST = {
    if (lets.isEmpty) {
      return smt2.v2ST _
    }
    var cache = HashMap.empty[Z, ST]

    def sv2ST(config: Config, v: State.Value, reporter: Reporter): ST = {
      v match {
        case v: State.Value.Sym =>
          cache.get(v.num) match {
            case Some(r) => return r
            case _ =>
              val r: ST = lets.get(v.num) match {
                case Some(ls) if ls.size == 1 && !ls(0).isInstanceOf[State.Claim.Let.Random] =>
                  smt2.l2RhsST(config, ls(0), sv2ST _, lets, declIds, reporter)
                case _ => smt2.v2ST(config, v, reporter)
              }
              cache = cache + v.num ~> r
              return r
          }
        case _ => return smt2.v2ST(config, v, reporter)
      }
    }

    return sv2ST _
  }

  def logikaMethod(nameExePathMap: HashMap[String, String], maxCores: Z, fileOptions: LibUtil.FileOptionMap,
                   th: TypeHierarchy, config: Config, isHelper: B, hasInline: B, owner: ISZ[String], id: String,
                   receiverTypeOpt: Option[AST.Typed], params: ISZ[(AST.Id, AST.Typed)], retType: AST.Typed,
                   posOpt: Option[Position], reads: ISZ[AST.Exp.Ref], requires: ISZ[AST.Exp],
                   modifies: ISZ[AST.Exp.Ref], ensures: ISZ[AST.Exp], caseLabels: ISZ[AST.Exp.LitString],
                   plugins: ISZ[plugin.Plugin], implicitContext: Option[(String, Position)],
                   compMethods: ISZ[ISZ[String]]): Logika = {
    val mctx = Context.Method(isHelper, hasInline, owner, id, receiverTypeOpt, params, retType, reads, requires,
      modifies, ensures, HashMap.empty, HashMap.empty, HashMap.empty, posOpt, HashMap.empty)
    val ctx = Context.empty(nameExePathMap, maxCores, fileOptions)(methodOpt = Some(mctx),
      caseLabels = caseLabels, implicitCheckTitlePosOpt = implicitContext, compMethods = compMethods)
    return Logika(th, config, ctx, plugins)
  }

  def checkInv(isPre: B, state: State, logika: Logika, smt2: Smt2, cache: Logika.Cache, invs: ISZ[lang.symbol.Info.Inv],
               posOpt: Option[Position], substMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
    val methodName: String =
      if (logika.context.methodName.size == 1) logika.context.methodName(0)
      else if (logika.context.methodOpt.get.receiverTypeOpt.isEmpty) st"${(logika.context.methodName, ".")}".render
      else st"${(ops.ISZOps(logika.context.methodName).dropRight(1), ".")}#${logika.context.methodName(0)}".render
    val title: String = if (isPre) s"Method $methodName pre-invariant" else s"Method $methodName post-invariant"
    return checkInvs(logika, posOpt, isPre, title, smt2, cache, T, state, logika.context.receiverTypeOpt, None(), invs,
      substMap, reporter)
  }

  def checkMethodPre(logika: Logika, smt2: Smt2, cache: Logika.Cache, reporter: Reporter, state: State,
                     methodPosOpt: Option[Position], invs: ISZ[Info.Inv], requires: ISZ[AST.Exp]): State = {
    var s = state
    s = checkInv(T, s, logika, smt2, cache, invs, methodPosOpt, TypeChecker.emptySubstMap, reporter)
    for (r <- requires if s.ok) {
      var cacheHit = F
      if (logika.config.transitionCache) {
        cache.getTransitionAndUpdateSmt2(logika.th, logika.config, Logika.Cache.Transition.Exp(r), logika.context.methodName, s, smt2) match {
          case Some((ISZ(nextState), cached)) =>
            cacheHit = T
            reporter.coverage(F, cached, r.posOpt.get)
            s = nextState
          case _ =>
        }
      }
      if (!cacheHit) {
        val s0 = s
        s = logika.evalAssume(smt2, cache, T, "Precondition", s, r, r.posOpt, reporter)._1
        if (logika.config.transitionCache && s.ok) {
          val cached = cache.setTransition(logika.th, logika.config, Logika.Cache.Transition.Exp(r), logika.context.methodName, s0, ISZ(s), smt2)
          reporter.coverage(T, cached, r.posOpt.get)
        } else {
          reporter.coverage(F, Logika.zeroU64, r.posOpt.get)
        }
      }
    }
    return s
  }

  def checkMethodPost(logika: Logika, smt2: Smt2, cache: Logika.Cache, reporter: Reporter, states: ISZ[State],
                      methodPosOpt: Option[Position], invs: ISZ[Info.Inv], ensures: ISZ[AST.Exp], logPc: B, logRawPc: B,
                      postPosOpt: Option[Position]): ISZ[State] = {
    var rwLocals = ISZ[AST.ResolvedInfo]()
    logika.context.methodOpt match {
      case Some(m) =>
        val context = m.owner :+ m.id
        for (p <- m.params) {
          rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, p._1.value)
        }
      case _ =>
    }
    var r = ISZ[State]()
    for (state <- states) {
      if (!state.ok) {
        r = r :+ state
      } else {
        var s = state
        s = checkInv(F, s, logika, smt2, cache, invs, methodPosOpt, TypeChecker.emptySubstMap, reporter)
        for (e <- ensures if s.ok) {
          var cacheHit = F
          if (logika.config.transitionCache) {
            cache.getTransitionAndUpdateSmt2(logika.th, logika.config, Logika.Cache.Transition.Exp(e), logika.context.methodName, s, smt2) match {
              case Some((ISZ(nextState), cached)) =>
                cacheHit = T
                reporter.coverage(F, cached, e.posOpt.get)
                s = nextState
              case _ =>
            }
          }
          if (!cacheHit) {
            val s0 = s
            s = logika.evalAssert(smt2, cache, T, "Postcondition", s, e, e.posOpt, rwLocals, reporter)._1
            if (logika.config.transitionCache && s.ok) {
              val cached = cache.setTransition(logika.th, logika.config, Logika.Cache.Transition.Exp(e), logika.context.methodName, s0, ISZ(s), smt2)
              reporter.coverage(T, cached, e.posOpt.get)
            } else {
              reporter.coverage(F, Logika.zeroU64, e.posOpt.get)
            }
          }
        }
        if (postPosOpt.nonEmpty && s.ok) {
          logika.logPc(s(status = State.Status.End), reporter, postPosOpt)
        }
        r = r :+ s
      }
    }
    return r
  }

  def updateInVarMaps(l: Logika, isHelper: B, smt2: Smt2, cache: Logika.Cache, state: State, reporter: Reporter): (Logika, State) = {
    var s0 = state
    val mctx = l.context.methodOpt.get
    var objectVarInMap = mctx.objectVarInMap
    var objectNames = HashSMap.empty[ISZ[String], Position]
    for (p <- (mctx.readObjectVarMap(TypeChecker.emptySubstMap) ++
      mctx.modObjectVarMap(TypeChecker.emptySubstMap).entries).entries) {
      val (ids, (t, posOpt)) = p
      val pos = posOpt.get
      val (owner, isSpec): (ISZ[String], B) = l.th.nameMap.get(ids).get match {
        case info: Info.Var => (info.owner, F)
        case info: Info.SpecVar => (info.owner, T)
        case info => halt(s"Unexpected: $info")
      }
      objectNames = objectNames + owner ~> pos
      val (s1, sym) = nameIntro(posOpt.get, s0, ids, t, posOpt)
      s0 = s1.addClaim(State.Claim.Input(F, isSpec, owner, ids(ids.size - 1), sym, sym.pos))
      if (!isHelper) {
        s0 = assumeValueInv(l, smt2, cache, T, s0, sym, pos, reporter)
      }
      objectVarInMap = objectVarInMap + ids ~> sym
    }
    if (!isHelper) {
      for (p <- objectNames.entries) {
        val (objectName, pos) = p
        s0 = assumeObjectInv(l, smt2, cache, objectName, s0, pos, reporter)
      }
    }
    var fieldVarInMap = mctx.fieldVarInMap
    var localInMap = mctx.localInMap
    var thisAdded = F
    mctx.receiverTypeOpt match {
      case Some(receiverType) =>
        val (s1, thiz) = idIntro(mctx.posOpt.get, s0, mctx.name, "this", receiverType, mctx.posOpt)
        localInMap = localInMap + "this" ~> thiz
        s0 = if (!l.th.isModifiable(receiverType)) s1 else s1.addClaim(State.Claim.Input(T, F, mctx.name, "this", thiz, thiz.pos))
        thisAdded = T
        for (p <- mctx.fieldVarMap(TypeChecker.emptySubstMap).entries) {
          val (id, (t, posOpt)) = p
          val (s2, sym) = s0.freshSym(t, posOpt.get)
          s0 = s2.addClaim(State.Claim.Let.FieldLookup(sym, thiz, id))
          fieldVarInMap = fieldVarInMap + id ~> sym
        }
      case _ =>
    }
    for (v <- mctx.localMap(TypeChecker.emptySubstMap).values) {
      val (isVal, mname, id, t) = v
      val posOpt = id.attr.posOpt
      if (id.value != "this") {
        val (s1, sym) = idIntro(posOpt.get, s0, mname, id.value, t, posOpt)
        s0 = if (isVal && !l.th.isModifiable(t)) s1 else s1.addClaim(State.Claim.Input(T, F, mname, id.value, sym, sym.pos))
        if (!isHelper) {
          s0 = assumeValueInv(l, smt2, cache, T, s0, sym, posOpt.get, reporter)
        }
        localInMap = localInMap + id.value ~> sym
      } else if (!thisAdded) {
        val (s1, sym) = idIntro(posOpt.get, s0, mname, id.value, t, mctx.posOpt)
        s0 = if (!l.th.isModifiable(t)) s1 else s1.addClaim(State.Claim.Input(T, F, mname, id.value, sym, sym.pos))
        localInMap = localInMap + id.value ~> sym
        thisAdded = T
      }
    }
    return (l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
      localInMap = localInMap)))), s0)
  }

  def checkMethod(nameExePathMap: HashMap[String, String],
                  maxCores: Z,
                  fileOptions: LibUtil.FileOptionMap,
                  th: TypeHierarchy,
                  plugins: ISZ[plugin.Plugin],
                  method: AST.Stmt.Method,
                  caseIndex: Z,
                  config: Config,
                  smt2: Smt2,
                  cache: Logika.Cache,
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
        val receiverTypeOpt: Option[AST.Typed] = if (res.isInObject) {
          None()
        } else {
          th.typeMap.get(res.owner).get match {
            case ti: TypeInfo.Sig => Some(ti.tpe)
            case ti: TypeInfo.Adt => Some(ti.tpe)
            case _ => halt("Infeasible")
          }
        }
        val p = updateInVarMaps(logikaMethod(nameExePathMap, maxCores, fileOptions, th, mconfig, method.isHelper,
          method.hasInline, res.owner, method.sig.id.value, receiverTypeOpt, method.sig.paramIdTypes,
          method.sig.returnType.typedOpt.get, methodPosOpt, reads, requires, modifies, ensures,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get), plugins, None(), ISZ()), method.isHelper, smt2, cache,
          state, reporter)
        state = p._2
        p._1
      }
      val invs: ISZ[Info.Inv] = if (method.isHelper) ISZ[Info.Inv]() else logika.retrieveInvs(res.owner, res.isInObject)
      state = checkMethodPre(logika, smt2, cache, reporter, state, methodPosOpt, invs, requires)
      val stmts = method.bodyOpt.get.stmts
      val (l, ss): (Logika, ISZ[State]) = if (method.isStrictPure) {
        val stmt = stmts(0).asInstanceOf[AST.Stmt.Var]
        val spBody = stmt.initOpt.get
        val pos = spBody.asStmt.posOpt.get
        val t = stmt.attr.typedOpt.get
        val (s0, v) = logika.singleStateValue(pos, state,
          logika.evalAssignExpValue(Split.Default, smt2, cache, t, T, state, spBody, reporter))
        val (s1, sym) = resIntro(pos, s0, logika.context.methodName, t, Some(pos))
        (logika, ISZ(s1.addClaim(State.Claim.Let.Def(sym, v))))
      } else {
        evalStmtsLogika(logika, Split.Default, smt2, cache, None(), T, state, stmts, reporter)
      }
      checkMethodPost(l, smt2, cache, reporter, ss, methodPosOpt, invs, ensures, mconfig.logPc, mconfig.logRawPc,
        if (stmts.nonEmpty) stmts(stmts.size - 1).posOpt else None())
    }

    for (p <- method.sig.params) {
      smt2.addType(config, p.tipe.typedOpt.get, reporter)
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
            checkCase(if (c.label.value == "") None() else Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
          } else {
            for (c <- contract.cases) {
              checkCase(if (c.label.value == "") None() else Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
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

  def collectLocals(s0: State, lcontext: ISZ[String]): ISZ[String] = {
    return StateTransformer(CurrentIdCollector(lcontext)).transformState(Set.empty, s0).ctx.elements
  }

  def rewriteLocal(logika: Logika, s0: State, inScope: B, lcontext: ISZ[String], id: String, posOpt: Option[Position],
                   reporter: Reporter): State = {
    val poss = collectLocalPoss(s0, lcontext, id)
    if (poss.isEmpty && !logika.config.interp && !logika.context.hasInline) {
      reporter.error(posOpt, Logika.kind, s"Missing Modifies clause for $id")
      return s0(status = State.Status.Error)
    }
    val (s1, num) = s0.fresh
    val locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)] + (lcontext, id) ~> ((poss, num))
    val r = StateTransformer(CurrentIdRewriter(locals, inScope)).transformState(F, s1)
    val s2 = r.resultOpt.getOrElse(s1)
    return s2
  }

  def rewriteLocals(s0: State, inScope: B, lcontext: ISZ[String], ids: ISZ[String]): (State, HashMap[(ISZ[String], String), (ISZ[Position], Z)]) = {
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)]
    if (ids.isEmpty) {
      return (s0, locals)
    }
    var s1 = s0
    for (id <- ids) {
      val poss = collectLocalPoss(s0, lcontext, id)
      if (poss.nonEmpty) {
        val (s2, num) = s1.fresh
        locals = locals + (lcontext, id) ~> ((poss, num))
        s1 = s2
      }
    }
    val r = StateTransformer(CurrentIdRewriter(locals, inScope)).transformState(F, s1)
    return (r.resultOpt.getOrElse(s1), locals)
  }

  def rewriteLocalVars(logika: Logika, state: State, inScope: B, localVars: ISZ[AST.ResolvedInfo.LocalVar],
                       posOpt: Option[Position], reporter: Reporter): State = {
    if (localVars.isEmpty) {
      return state
    }
    var current = state
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z)]
    for (l <- localVars) {
      val poss = StateTransformer(CurrentIdPossCollector(l.context, l.id)).
        transformState(Set.empty, current).ctx.elements
      if (poss.isEmpty && !logika.config.interp && !logika.context.hasInline) {
        reporter.error(posOpt, Logika.kind, s"Missing Modifies clause for ${l.id}")
        return state(status = State.Status.Error)
      }
      val (s1, num) = current.fresh
      current = s1
      locals = locals + (l.context, l.id) ~> ((poss, num))
    }
    val r = StateTransformer(CurrentIdRewriter(locals, inScope)).transformState(F, current)
    current = r.resultOpt.get
    return current
  }

  def rewriteObjectVars(logika: Logika, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State,
                        objectVars: HashSMap[AST.ResolvedInfo.Var, (AST.Typed, Position)], pos: Position,
                        reporter: Reporter): State = {
    if (objectVars.isEmpty) {
      return state
    }
    var current = state
    var vars = HashMap.empty[ISZ[String], (ISZ[Position], Z)]
    var varValueMap = HashMap.empty[ISZ[String], State.Value.Sym]
    for (p <- objectVars.entries) {
      val (l, (t, _)) = p
      val ids = l.owner :+ l.id
      val poss = StateTransformer(CurrentNamePossCollector(ids)).
        transformState(ISZ(), current).ctx
      if (poss.isEmpty && !logika.config.interp && !logika.context.hasInline) {
        reporter.error(Some(pos), Logika.kind, st"Missing Modifies clause for ${(ids, ".")}".render)
        return state(status = State.Status.Error)
      }
      val (s1, num) = current.fresh
      val (s2, sym) = nameIntro(pos, s1, ids, t, None())
      varValueMap = varValueMap + ids ~> sym
      current = s2
      vars = vars + ids ~> ((poss, num))
    }
    val rt = StateTransformer(CurrentNameRewriter(vars)).transformState(F, current)
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
        val o1 = varValueMap.get(name).get
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
      typedOpt = Some(AST.Typed.Fun(AST.Purity.Impure,F, ISZ(AST.Typed.b), AST.Typed.unit))
    )
    return AST.Stmt.Expr(AST.Exp.Invoke(
      None(), AST.Exp.Ident(AST.Id("assume", AST.Attr(posOpt)), assumeResAttr), ISZ(), ISZ(cond),
      AST.ResolvedAttr(assumeResAttr.posOpt, assumeResAttr.resOpt, AST.Typed.unitOpt)
    ), AST.TypedAttr(posOpt, AST.Typed.unitOpt))
  }

  @pure def afterPos(pos: Position): Position = {
    return message.FlatPos(pos.uriOpt,
      conversions.Z.toU32(pos.endLine + 1),
      conversions.Z.toU32(1),
      conversions.Z.toU32(pos.endLine + 1),
      conversions.Z.toU32(2),
      conversions.Z.toU32(pos.offset),
      conversions.Z.toU32(1))
  }

  @pure def normType(t: AST.Typed): AST.Typed = {
    t match {
      case t: AST.Typed.Method if t.tpe.isByName => return t.tpe.ret
      case _ => return t
    }
  }

  def pureMethod(nameExePathMap: HashMap[String, String], maxCores: Z,
                 fileOptions: LibUtil.FileOptionMap, th: TypeHierarchy, config: Config,
                 plugins: ISZ[plugin.Plugin], smt2: Smt2, cache: Logika.Cache, state: State,
                 receiverTypeOpt: Option[AST.Typed], funType: AST.Typed.Fun, owner: ISZ[String], id: String,
                 isHelper: B, isStrictPure: B, paramIds: ISZ[AST.Id], body: AST.AssignExp, reporter: Reporter,
                 implicitContextOpt: Option[(String, Position)]): (State, State.ProofFun) = {
    val pf = State.ProofFun(receiverTypeOpt, owner, id, funType.isByName, for (id <- paramIds) yield id.value, funType.args, Util.normType(funType.ret))
    if (smt2.pureFuns.contains(pf)) {
      return (state, pf)
    } else {
      val posOpt = body.asStmt.posOpt
      val pos = posOpt.get
      val (svs, maxFresh, ok, decl, declClaim): (ISZ[(State, State.Value.Sym)], Z, B, ST, ST) = {
        val context = pf.context :+ pf.id
        val logika: Logika = logikaMethod(nameExePathMap, maxCores, fileOptions, th, config, isHelper, F, pf.context,
          pf.id, pf.receiverTypeOpt, ops.ISZOps(paramIds).zip(pf.paramTypes), pf.returnType, posOpt, ISZ(), ISZ(), ISZ(),
          ISZ(), ISZ(), plugins, implicitContextOpt, ISZ())
        var s0 = state(claims = ISZ())
        val (s1, res) = idIntro(posOpt.get, s0, context, "Res", pf.returnType, posOpt)
        val s2: State =
          if (isHelper || isStrictPure && config.strictPureMode == Config.StrictPureMode.Uninterpreted) s1
          else assumeValueInv(logika, smt2, cache, T, s1, res, pos, reporter)
        val (d, dc) = smt2.addProofFunDecl(config, pf, res, ops.ISZOps(s2.claims).slice(s1.claims.size, s2.claims.size), reporter)
        s0 = s0(nextFresh = s2.nextFresh, status = s2.status)
        for (pair <- ops.ISZOps(paramIds).zip(pf.paramTypes) if pair._1.value != "this") {
          val (pid, pt) = pair
          val (s0_1, pv) = idIntro(pos, s0, context, pid.value, pt, pid.attr.posOpt)
          val s0_2: State = if (isHelper) s0_1 else assumeValueInv(logika, smt2, cache, T, s0_1, pv, pos, reporter)
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
          if (s.ok) {
            status = T
          }
          val (s2, sym) = logika.value2Sym(s, v, pos)
          sss = sss :+ ((s2, sym))
          if (maxFresh < s2.nextFresh) {
            maxFresh = s2.nextFresh
          }
        }
        assert(svs.isEmpty || maxFresh >= 0)
        (for (ss <- sss) yield (ss._1(nextFresh = maxFresh), ss._2), maxFresh, status, d, dc)
      }

      if (ok && svs.nonEmpty) {
        smt2.addProofFun(config, pos, pf, svs, 0, decl, declClaim, reporter)
      }

      val s1 = state(status = State.statusOf(ok), nextFresh = maxFresh)
      if (svs.nonEmpty && config.sat && s1.ok) {
        val title: String = s"the derived proof function of $id"
        smt2.satResult(pf.context :+ pf.id, config, cache, Smt2.satTimeoutInMs, T, title, pos, ISZ(), reporter) match {
          case (T, _) =>
          case (_, result) =>
            if (result.kind == Smt2Query.Result.Kind.Error) {
              reporter.error(posOpt, Logika.kind, s"Error occurred when checking the satisfiability of proof function derived from @strictpure method")
            } else {
              reporter.error(posOpt, Logika.kind, "Unsatisfiable proof function derived from @strictpure method")
            }
        }
      }
      return (s1, pf)
    }
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

  def evalExtractPureMethod(logika: Logika, smt2: Smt2, cache: Logika.Cache, state: State, receiverTypeOpt: Option[AST.Typed],
                            receiverOpt: Option[State.Value.Sym], owner: ISZ[String], id: String, isHelper: B,
                            exp: AST.Exp, reporter: Reporter): (State, State.Value) = {
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
            val e = AST.Exp.This(logika.context.methodName, AST.TypedAttr(posOpt, receiverTypeOpt))
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
      val (s2, pf) = pureMethod(logika.context.nameExePathMap, logika.context.maxCores, logika.context.fileOptions,
        logika.th, logika.config, logika.plugins, smt2, cache, s0, receiverTypeOpt, AST.Typed.Fun(AST.Purity.Pure,F, paramTypes, t),
        owner, id, isHelper, T, paramIds, AST.Stmt.Expr(newExp, AST.TypedAttr(posOpt, tOpt)), reporter,
        logika.context.implicitCheckTitlePosOpt)
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

  @pure def strictPureClaimId(i: Z, pos: Position): String = {
    return s"claim_${i}_${pos.beginLine}_${pos.beginColumn}"
  }

  def detectUnsupportedFeatures(stmt: AST.Stmt.Method): ISZ[message.Message] = {
    val ufd = UnsupportedFeatureDetector(stmt.sig.id.attr.posOpt, stmt.sig.id.value, message.Reporter.create)
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

  def addObjectInv(logika: Logika, smt2: Smt2, cache: Logika.Cache, name: ISZ[String], state: State, pos: Position,
                   reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    val l = logika(context = logika.context(methodOpt = Some(Context.Method(
      isHelper = F,
      hasInline = F,
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
      posOpt = None(),
      storage = logika.context.methodOpt.map((mctx: Context.Method) => mctx.storage).getOrElse(HashMap.empty)
    ))))
    val invs = l.retrieveInvs(name, T)
    if (invs.isEmpty) {
      return (state, ISZ())
    }
    val (owner, id) = invOwnerId(invs, None())
    val inv = l.invs2exp(invs, HashMap.empty).get
    val (s0, v) = evalExtractPureMethod(l, smt2, cache, state, None(), None(), owner, id, T, inv, reporter)
    val (s1, sym) = l.value2Sym(s0, v, pos)
    return (s1, ISZ(sym))
  }

  def assumeObjectInv(logika: Logika, smt2: Smt2, cache: Logika.Cache, name: ISZ[String], state: State, pos: Position,
                      reporter: Reporter): State = {
    if (logika.config.interp || logika.context.hasInline) {
      return state
    }
    val (s0, conds) = addObjectInv(logika, smt2, cache, name, state, pos, reporter)
    return s0.addClaims(for (cond <- conds) yield State.Claim.Prop(T, cond))
  }

  def addValueInv(logika: Logika, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, receiver: State.Value.Sym,
                  pos: Position, reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    if (logika.config.interp || logika.context.hasInline) {
      return (state, ISZ())
    }
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
    smt2.addType(logika.config, t, reporter)
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
    val (s5, cond) = evalExtractPureMethod(logika, smt2, cache, state, Some(receiver.tipe), Some(receiver), owner, id,
      T, inv, reporter)
    val (s6, sym) = logika.value2Sym(s5, cond, pos)
    return (s6, ISZ(sym))
  }

  def assumeValueInv(logika: Logika, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, receiver: State.Value.Sym,
                     pos: Position, reporter: Reporter): State = {
    if (logika.config.interp || logika.context.hasInline) {
      return state
    }
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

  def checkInvs(logika: Logika, posOpt: Option[Position], isAssume: B, title: String, smt2: Smt2, cache: Logika.Cache,
                rtCheck: B, s0: State, receiverTypeOpt: Option[AST.Typed], receiverOpt: Option[State.Value.Sym],
                invs: ISZ[Info.Inv], substMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
    if (logika.config.interp || logika.context.hasInline) {
      return s0
    }
    if (logika.config.transitionCache) {
      cache.getTransitionAndUpdateSmt2(logika.th, logika.config,
        Logika.Cache.Transition.Stmts(for (inv <- invs) yield inv.ast), logika.context.methodName, s0, smt2) match {
        case Some((ISZ(nextState), cached)) =>
          for (inv <- invs) {
            reporter.coverage(F, cached, inv.posOpt.get)
          }
          return nextState
        case _ =>
      }
    }
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
      val (s1, v) = evalExtractPureMethod(logika, smt2, cache, s0, receiverTypeOpt, receiverOpt, owner, id, T, claim, reporter)
      if (!s1.ok) {
        return None()
      }
      val (s2, sym) = logika.value2Sym(s1, v, pos)
      if (isAssume) {
        val s3 = logika.evalAssumeH(T, smt2, cache, title, s2, sym, posOpt, reporter)
        return Some(s3)
      } else {
        val s3 = logika.evalAssertH(T, smt2, cache, title, s2, sym, posOpt, ISZ(), reporter)
        if (!s3.ok) {
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
    for (inv <- invs if s4.ok) {
      s4 = logika.evalInv(posOpt, isAssume, title, smt2, cache, rtCheck, s4, inv.ast, substMap, reporter)
    }
    if (logika.config.transitionCache && s4.ok) {
      val cached = cache.setTransition(logika.th, logika.config,
        Logika.Cache.Transition.Stmts(for (inv <- invs) yield inv.ast), logika.context.methodName, s0, ISZ(s4), smt2)
      for (inv <- invs) {
        reporter.coverage(T, cached, inv.posOpt.get)
      }
    } else {
      for (inv <- invs) {
        reporter.coverage(F, Logika.zeroU64, inv.posOpt.get)
      }
    }
    return s4
  }

  def evalAssignReceiver(modifies: ISZ[AST.Exp.Ref], logika: Logika, logikaComp: Logika, smt2: Smt2, cache: Logika.Cache,
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

  @pure def bigAnd(claims: ISZ[State.Claim]): State.Claim = {
    if (claims.size == 1) {
      return claims(0)
    }
    var cs = ISZ[State.Claim]()
    for (claim <- claims) {
      claim match {
        case claim: State.Claim.And => cs = cs ++ claim.claims
        case _ => cs = cs :+ claim
      }
    }
    return State.Claim.And(cs)
  }

  @pure def createClaimsToExps(plugins: ISZ[plugin.ClaimPlugin], pos: Position, context: ISZ[String],
                               claims: ISZ[State.Claim], th: TypeHierarchy, includeFreshLines: B, atRewrite: B): ClaimsToExps = {
    val collector = LetEqNumMapCollector(HashMap.empty, HashMap.empty)
    for (claim <- claims) {
      collector.transformStateClaim(claim)
    }
    val cs2es = ClaimsToExps(plugins, pos, context, th, includeFreshLines, atRewrite, collector.letMap, collector.eqMap,
      HashMap.empty)
    return cs2es
  }

  @pure def claimsToExps(plugins: ISZ[plugin.ClaimPlugin], pos: Position, context: ISZ[String],
                         claims: ISZ[State.Claim], th: TypeHierarchy, includeFreshLines: B, atRewrite: B): (ISZ[AST.Exp], ClaimsToExps.AtMap) = {
    val cs2es = createClaimsToExps(plugins, pos, context, claims, th, includeFreshLines, atRewrite)
    val r = cs2es.translate(claims)
    val rs = HashSSet ++ r
    return (rs.elements, cs2es.atMap)
  }

  @pure def claimsToExpsLastOpt(plugins: ISZ[plugin.ClaimPlugin], pos: Position, context: ISZ[String],
                               claims: ISZ[State.Claim], th: TypeHierarchy, includeFreshLines: B, atRewrite: B): (ISZ[AST.Exp], Option[AST.Exp], ClaimsToExps.AtMap) = {
    val cs2es = createClaimsToExps(plugins, pos, context, claims, th, includeFreshLines, atRewrite)
    val rOps = ops.ISZOps(cs2es.translate(claims))
    val hasLast: B = if (claims.nonEmpty) cs2es.translate(ISZ(claims(claims.size - 1))).nonEmpty else F
    return ((HashSSet ++ rOps.dropRight(1)).elements, if (hasLast) Some(rOps.s(rOps.s.size - 1)) else None(), cs2es.atMap)
  }

  @pure def saveLocals(depth: Z, s0: State, currentContext: ISZ[String]): (State, LocalSaveMap) = {
    val lvic = LocalSaver(depth, currentContext, emptyLocalSaveMap)
    val s1 = lvic.transformState(s0).getOrElse(s0)
    return (s1, lvic.localMap)
  }

  @pure def restoreLocals(s0: State, localMap: LocalSaveMap): State = {
    return StateTransformer(PrePostLocalRestorer(localMap)).transformState(F, s0).resultOpt.getOrElse(s0)
  }

  @pure def removeOld(s: State): State = {
    if (s.ok) {
      var cs = ISZ[State.Claim]()
      var changed = F
      for (c <- s.claims) {
        c match {
          case _: State.Claim.Old => changed = T
          case _ => cs = cs :+ c
        }
      }
      if (changed) {
        return s(claims = cs)
      }
    }
    return s
  }

  @strictpure def removeOlds(ss: ISZ[State]): ISZ[State] = for (s <- ss) yield removeOld(s)

  def evalStmts(l: Logika, split: Split.Type, smt2: Smt2, cache: Logika.Cache, rOpt: Option[State.Value.Sym],
                rtCheck: B, state: State, stmts: ISZ[AST.Stmt], reporter: Reporter): ISZ[State] = {
    return evalStmtsLogika(l, split, smt2, cache, rOpt, rtCheck, state, stmts, reporter)._2
  }

  def evalStmtsLogika(l: Logika, split: Split.Type, smt2: Smt2, cache: Logika.Cache, rOpt: Option[State.Value.Sym],
                      rtCheck: B, state: State, stmts: ISZ[AST.Stmt], reporter: Reporter): (Logika, ISZ[State]) = {
    var logika = l
    val initConfig = logika.config
    val context = logika.context
    var currents = ISZ(state)
    var done = ISZ[State]()

    val size: Z = if (rOpt.nonEmpty) stmts.size - 1 else stmts.size
    for (i <- 0 until size) {
      val cs = currents
      currents = ISZ()
      val stmt = stmts(i)
      for (current <- cs) {
        val currentNoOld: State = if (stmt.isInstanceOf[AST.Stmt.DeduceSteps] || stmt.isInstanceOf[AST.Stmt.DeduceSequent]
          || context.pathConditionsOpt.nonEmpty) current else if (stmt.isInstruction) removeOld(current) else current
        if (currentNoOld.ok) {
          stmt match {
            case AST.Stmt.Expr(e: AST.Exp.Invoke) if e.attr.resOpt == TypeChecker.setOptionsResOpt =>
              logika.logPc(current, reporter, stmt.posOpt)
              val tool = e.args(0).asInstanceOf[AST.Exp.LitString].value
              val value: String = e.args(1) match {
                case arg: AST.Exp.LitString => arg.value
                case AST.Exp.Select(Some(arg: AST.Exp.LitString), _, _) => arg.value.stripMargin
                case _ => halt(s"Infeasible: ${e.args(1)}")
              }
              if (tool == OptionsUtil.logika) {
                OptionsUtil.toConfig(initConfig, l.context.maxCores, LibUtil.setOptions, l.context.nameExePathMap, value) match {
                  case Either.Left(c) =>
                    logika = logika(config = c)
                    reporter.coverage(F, org.sireum.U64.fromZ(0), stmt.posOpt.get)
                    currents = currents :+ currentNoOld
                  case Either.Right(msgs) =>
                    for (msg <- msgs) {
                      reporter.error(e.args(1).posOpt, Logika.kind, msg)
                    }
                    currents = currents :+ currentNoOld(status = State.Status.Error)
                }
              } else {
                var changed = F
                var newPlugins = ISZ[plugin.Plugin]()
                for (p <- logika.plugins) {
                  p.setOptions(tool, value) match {
                    case Some(newP) =>
                      changed = T
                      newPlugins = newPlugins :+ newP
                    case _ => newPlugins = newPlugins :+ p
                  }
                }
                if (changed) {
                  logika = logika(plugins = newPlugins)
                }
                currents = currents :+ currentNoOld
              }
            case _ =>
              val nextStates: ISZ[State] = if (logika.config.transitionCache) {
                val ensures: ISZ[AST.Exp] = if (context.methodOpt.nonEmpty) context.methodOpt.get.ensures else ISZ()
                val transition: Logika.Cache.Transition = if (stmt.hasReturnMemoized && ensures.nonEmpty)
                  Logika.Cache.Transition.StmtExps(stmt, context.methodOpt.get.ensures)
                else Logika.Cache.Transition.Stmt(stmt)
                cache.getTransitionAndUpdateSmt2(logika.th, logika.config, transition, logika.context.methodName, currentNoOld, smt2) match {
                  case Some((ss, cached)) =>
                    if (stmt.isInstruction) {
                      reporter.coverage(F, cached, stmt.posOpt.get)
                      if (stmt.isInstanceOf[AST.Stmt.Return]) {
                        for (e <- ensures) {
                          reporter.coverage(F, cached, e.posOpt.get)
                        }
                      }
                    }
                    ss
                  case _ =>
                    if (stmt.isInstruction) {
                      logika.logPc(current, reporter, stmt.posOpt)
                    }
                    val (l2, ss) = logika.evalStmt(split, smt2, cache, rtCheck, currentNoOld, stmts(i), reporter)
                    logika = l2
                    if (!reporter.hasError && ops.ISZOps(ss).forall((s: State) => s.status != State.Status.Error)) {
                      val cached = cache.setTransition(logika.th, logika.config, transition, logika.context.methodName, currentNoOld, ss, smt2)
                      if (stmt.isInstruction) {
                        reporter.coverage(T, cached, stmt.posOpt.get)
                        if (stmt.isInstanceOf[AST.Stmt.Return]) {
                          for (e <- ensures) {
                            reporter.coverage(T, cached, e.posOpt.get)
                          }
                        }
                      }
                    } else {
                      if (stmt.isInstruction) {
                        reporter.coverage(F, Logika.zeroU64, stmt.posOpt.get)
                        if (stmt.isInstanceOf[AST.Stmt.Return]) {
                          for (e <- ensures) {
                            reporter.coverage(F, Logika.zeroU64, e.posOpt.get)
                          }
                        }
                      }
                    }
                    ss
                }
              } else {
                if (stmt.isInstruction) {
                  logika.logPc(current, reporter, stmt.posOpt)
                }
                val (l2, ss) = logika.evalStmt(split, smt2, cache, rtCheck, currentNoOld, stmts(i), reporter)
                logika = l2
                ss
              }
              currents = currents ++ nextStates
          }
        } else {
          done = done :+ currentNoOld
        }
      }
    }

    val r: ISZ[State] = if (rOpt.nonEmpty) (
      for (current <- currents;
           s <- logika.evalAssignExp(split, smt2, cache, rOpt, rtCheck, current, stmts(stmts.size - 1).asAssignExp, reporter))
      yield s) ++ done
    else currents ++ done
    return (logika, if (context.pathConditionsOpt.nonEmpty) r else removeOlds(r))
  }

  def extractAssignExpOpt(mi: lang.symbol.Info.Method): Option[AST.AssignExp] = {
    if (mi.ast.isStrictPure && mi.ast.bodyOpt.nonEmpty) {
      mi.ast.bodyOpt.get.stmts match {
        case ISZ(stmt: AST.Stmt.Var, _: AST.Stmt.Return) => return stmt.initOpt
        case stmts => halt(s"Infeasible: $stmts")
      }
    } else {
      return None()
    }
  }

  @strictpure def isEquivLeftRight(e: AST.Exp.Binary): B =
    (e.attr.resOpt == equivResOpt || e.attr.resOpt == eqResOpt) && e.left == e.right

  @pure def isEquivResOpt(th: TypeHierarchy, resOpt: Option[AST.ResolvedInfo], t: AST.Typed): B = {
    resOpt match {
      case Some(res: AST.ResolvedInfo.BuiltIn) =>
        if (res.kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv) {
          return T
        }
        if (res.kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryEq && th.isSubstitutableWithoutSpecVars(t)) {
          return T
        }
      case _ =>
    }
    return F
  }
}