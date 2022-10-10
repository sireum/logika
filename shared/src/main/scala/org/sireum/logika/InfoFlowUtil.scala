// #Sireum
package org.sireum.logika

import org.sireum._
import org.sireum.lang.ast.MethodContract.InfoFlow
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.State.Claim.Let
import org.sireum.logika.State.{Claim, Value}
import org.sireum.message.Position

object InfoFlowUtil {

  val secondTraceSuffix: String = "~"

  @datatype class SymValueRewriter(val fresh: Z) extends StateTransformer.PrePost[Z] {
    override def preStateValueSym(maxSym: Z,
                                  o: State.Value.Sym): StateTransformer.PreResult[Z, State.Value] = {
      val r = o.num + fresh
      val _maxSym: Z = if (r > maxSym) r else maxSym

      return StateTransformer.PreResult(_maxSym, T, Some(o(num = r)))
    }

    override def preStateClaimLetCurrentId(ctx: Z, o: Let.CurrentId): StateTransformer.PreResult[Z, Claim.Let] = {
      return StateTransformer.PreResult(ctx, T, Some(o(id = s"${o.id}${secondTraceSuffix}")))
    }

    override def preStateClaimLetId(ctx: Z, o: Let.Id): StateTransformer.PreResult[Z, Claim.Let] = {
      return StateTransformer.PreResult(ctx, T, Some(o(id = s"${o.id}${secondTraceSuffix}")))
    }
  }


  def processInfoFlowInAgrees(logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, state: State,
                              methodPosOpt: Option[Position], infoFlows: ISZ[InfoFlow]): (State, ISZ[ISZ[State.Value.Sym]]) = {
    var s = state
    var syms: ISZ[ISZ[State.Value.Sym]] = ISZ()
    for (infoFlow <- infoFlows if s.status) {
      var ssyms: ISZ[State.Value.Sym] = ISZ()
      for (inExp <- infoFlow.inAgrees) {
        inExp match {
          case ref: AST.Exp.Ref =>
            val res = ref.resOpt.get
            res match {
              case lv: AST.ResolvedInfo.LocalVar =>
                val (s1, r) = Util.idIntro(ref.posOpt.get, s, lv.context, s"${lv.id}", ref.typedOpt.get, None())
                s = s1
                ssyms = ssyms :+ r
              case x => halt(s"Need to handle $x")
            }
          case x =>
            val split = Split.Disabled
            val rtCheck = F
            val (s1, r) = logika.singleStateValue(logika.evalExp(split, smt2, cache, rtCheck, state, inExp, reporter))
            s = s1
            r match {
              case sym: State.Value.Sym => ssyms = ssyms :+ sym
              case _ => halt(s"Unexpected value: $r")
            }
        }
      }
      if (ssyms.nonEmpty) {
        syms = syms :+ ssyms
      }
    }
    return (s, syms)
  }

  def checkInfoFlowOutAgrees(logika: Logika, smt2: Smt2, cache: Smt2.Cache, reporter: Reporter, states: ISZ[State],
                             methodPosOpt: Option[Position], infoFlows: ISZ[InfoFlow], inAgreeSyms: ISZ[ISZ[Value.Sym]], value: Option[Position]): ISZ[State] = {

    if (inAgreeSyms.nonEmpty) {
      assert(infoFlows.size == inAgreeSyms.size, s"${infoFlows.size} vs ${inAgreeSyms.size}")

      var r: ISZ[State] = ISZ()
      for (flowIndex <- 0 until infoFlows.size) {
        val inSyms: ISZ[State.Value.Sym] = inAgreeSyms(flowIndex)
        val outAgrees = infoFlows(flowIndex).outAgrees
        val label = infoFlows(flowIndex).label

        for (state <- states) {
          if (!state.status) {
            r = r :+ state
          } else {
            var s = state

            val origNextFresh = s.nextFresh

            // introduce sym value for the outAgrees
            var outSyms: ISZ[State.Value.Sym] = ISZ()
            for (outExp <- outAgrees) {
              outExp match {
                case ref: AST.Exp.Ref =>
                  val res = ref.resOpt.get
                  res match {
                    case lv: AST.ResolvedInfo.LocalVar =>
                      val (s1, r) = Util.idIntro(ref.posOpt.get, s, lv.context, s"${lv.id}", ref.typedOpt.get, None())
                      s = s1
                      outSyms = outSyms :+ r
                    case x => halt(s"Need to handle $x")
                  }
                case x =>
                  val split = Split.Disabled
                  val rtCheck = F
                  val (s1, r) = logika.singleStateValue(logika.evalExp(split, smt2, cache, rtCheck, state, outExp, reporter))
                  s = s1
                  r match {
                    case sym: State.Value.Sym => outSyms = outSyms :+ sym
                    case _ => halt(s"Unexpected value: $r")
                  }
              }
            }

            // create 2nd trace
            {
              val rewriter = StateTransformer[Z](SymValueRewriter(origNextFresh))
              val result = rewriter.transformState(origNextFresh, s)

              val secondTraceClaims = result.resultOpt.get.claims
              s = s(claims = s.claims ++ secondTraceClaims, nextFresh = result.ctx + 1)
            }

            // add in agreements claims
            for (inSym <- inSyms) {
              val secInSym = inSym(num = inSym.num + origNextFresh)
              s = s.addClaim(State.Claim.Eq(inSym, secInSym))
            }

            val pos = methodPosOpt.get

            // add out agreements claims
            var bstack: Stack[State.Value.Sym] = Stack.empty
            for (outSym <- outSyms) {
              val (s1, sym) = s.freshSym(AST.Typed.b, pos)
              s = s1
              bstack = bstack.push(sym)

              val secOutSym = outSym(num = outSym.num + origNextFresh)
              val claim = State.Claim.Let.Binary(sym, outSym, AST.Exp.BinaryOp.Eq, secOutSym, secOutSym.tipe)
              s = s.addClaim(claim)
            }

            while (bstack.size > 1) {
              val (sym1, _bstack) = bstack.pop.get
              val (sym2, __bsstack) = _bstack.pop.get
              bstack = __bsstack
              val (s1, sym3) = s.freshSym(AST.Typed.b, pos)
              bstack = bstack.push(sym3)
              s = s1
              val claim = State.Claim.Let.Binary(sym3, sym1, AST.Exp.BinaryOp.And, sym2, AST.Typed.b)
              s = s.addClaim(claim)
            }

            val sym = bstack.pop.get._1
            val conclusion = State.Claim.Prop(T, sym)

            val validity = smt2.valid(cache = cache, reportQuery = T, log = logika.config.logVc, logDirOpt = logika.config.logVcDirOpt,
              title = s"Flow case $label at [${pos.beginLine}, ${pos.endLine}]", pos = pos,
              premises = s.claims, conclusion = conclusion, reporter = reporter)

            validity.kind match {
              case Smt2Query.Result.Kind.Unsat => r = r :+ s(status = T)
              case Smt2Query.Result.Kind.Sat => logika.error(Some(pos), s"Flow case $label violation", reporter)
              case Smt2Query.Result.Kind.Unknown => logika.error(methodPosOpt, s"Could not verify flow case $label", reporter)
              case Smt2Query.Result.Kind.Timeout => logika.error(methodPosOpt, s"Timed out while checking flow case $label", reporter)
              case Smt2Query.Result.Kind.Error => logika.error(methodPosOpt, s"Error encountered when checking flow case $label", reporter)
            }

            r = r :+ s(status = F)
          }
        }
      }
      return r
    } else {
      return states
    }
  }
}
