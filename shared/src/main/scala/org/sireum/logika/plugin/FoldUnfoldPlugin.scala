// #Sireum
/*
 Copyright (c) 2017-2025, Robby, Kansas State University
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

package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.tipe.TypeChecker
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, State, StepProofContext, Util}

object FoldUnfoldPlugin {
  @record class LocalVarContextSubstitutor(val oldContext: ISZ[String],
                                           val newContext: ISZ[String],
                                           val thisIdentOpt: MOption[AST.Exp]) extends AST.MTransformer {
    override def postResolvedInfoLocalVar(o: AST.ResolvedInfo.LocalVar): MOption[AST.ResolvedInfo] = {
      if (o.context == oldContext) {
        return MSome(o(context = newContext))
      } else {
        return MNone()
      }
    }

    override def postExpThis(o: AST.Exp.This): MOption[AST.Exp] = {
      return thisIdentOpt
    }
  }

  @pure def substAssignExpLocalVarContext(exp: AST.AssignExp, oldContext: ISZ[String], newContext: ISZ[String],
                                    thisIdentOpt: MOption[AST.Exp]): AST.AssignExp = {
    val lvcs = LocalVarContextSubstitutor(oldContext, newContext, thisIdentOpt)
    return lvcs.transformAssignExp(exp).getOrElseEager(exp)
  }
}

import FoldUnfoldPlugin._

@datatype class FoldUnfoldPlugin extends JustificationPlugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "FoldUnfoldPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return (res.id == "Fold" || res.id == "Unfold") && res.owner == justificationName
          case _ => return F
        }
      case _ => return F
    }
  }

  override def handle(logika: Logika,
                      smt2: Smt2,
                      cache: Logika.Cache,
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): State = {
    @strictpure def err: State = state(status = State.Status.Error)
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val justId = just.invokeIdent.id.value
    val isUnfold = justId == "Unfold"
    val posOpt = just.invokeIdent.id.attr.posOpt
    val fromStepId: AST.ProofAst.StepId = AST.Util.toStepIds(just.args, Logika.kind, reporter) match {
      case Some(as) => as(0)
      case _ => return err
    }
    val fromClaim: AST.Exp = spcMap.get(fromStepId) match {
      case Some(spc: StepProofContext.Regular) => spc.exp
      case Some(_) =>
        reporter.error(posOpt, Logika.kind, s"Cannot use compound proof step $fromStepId as an argument for $justId")
        return err
      case _ =>
        reporter.error(posOpt, Logika.kind, s"Could not find proof step $fromStepId")
        return err
    }

    val tOpt = Plugin.commonLabeled(logika.th, posOpt, fromStepId, if (isUnfold) fromClaim else step.claim,
      if (isUnfold) step.claim else fromClaim, reporter)
    if (tOpt.isEmpty) {
      return err
    }

    val Plugin.CommonLabeledResult(sortedNums, unfoldFromMap, unfoldToMap, labeled, aFromClaim, aToClaim) = tOpt.get

    for (num <- sortedNums) {
      val unfoldTo: AST.Exp.StrictPureBlock = unfoldToMap.get(num).get.exp match {
        case e: AST.Exp.StrictPureBlock => e
        case e =>
          reporter.error(e.posOpt, Logika.kind, s"Expecting a strictly pure block expression")
          return err
      }

      val unfoldFrom: AST.Exp.Invoke = unfoldFromMap.get(num).get.exp match {
        case e: AST.Exp.Invoke => e
        case e: AST.Exp.InvokeNamed =>
          var argOpts = ISZ.create(e.args.size, Option.none[AST.Exp]())
          for (i <- 0 until argOpts.size) {
            val namedArg = e.args(i)
            argOpts = argOpts(namedArg.index ~> Some(namedArg.arg))
          }
          var args = ISZ[AST.Exp]()
          for (i <- 0 until argOpts.size) {
            argOpts(i) match {
              case Some(earg) => args = args :+ earg
              case _ =>
                reporter.error(e.ident.attr.posOpt, Logika.kind, s"Missing argument #$i for ${e.ident.id.value}")
                return err
            }
          }
          AST.Exp.Invoke(e.receiverOpt, e.ident, e.targs, args, e.attr)
        case e =>
          reporter.error(e.posOpt, Logika.kind, s"Expecting an invocation expression")
          return err
      }

      def errSp(): State = {
        reporter.error(unfoldFrom.posOpt, Logika.kind, s"Expecting a defined @strictpure method invocation expression")
        return err
      }

      val (minfo, body): (Info.Method, AST.AssignExp) = unfoldFrom.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method =>
          val typeRel = TypeChecker.TypeRelation.Supertype
          if (res.isInObject) {
            val mi = logika.th.nameMap.get(res.owner :+ res.id).get.asInstanceOf[Info.Method]
            if (!mi.ast.isStrictPure) {
              return errSp()
            }
            val msm = TypeChecker.unifyFun(Logika.kind, logika.th, unfoldFrom.posOpt, typeRel, res.tpeOpt.get,
              mi.ast.sig.funType, message.Reporter.create).get
            Util.extractAssignExpOpt(mi) match {
              case Some(ae) => (mi, AST.Util.substAssignExp(ae, msm))
              case _ => return errSp()
            }
          } else {
            val receiver = unfoldFrom.receiverOpt.get
            logika.th.typeMap.get(res.owner).get match {
              case info: TypeInfo.Sig =>
                val mi = info.methods.get(res.id).get
                if (!mi.ast.isStrictPure) {
                  return errSp()
                }
                val tsm = TypeChecker.buildTypeSubstMap(res.owner, posOpt, info.ast.typeParams,
                  receiver.typedOpt.get.asInstanceOf[AST.Typed.Name].args, reporter).get
                val msm = TypeChecker.unifyFun(Logika.kind, logika.th, unfoldFrom.posOpt, typeRel,
                  mi.ast.sig.funType.subst(tsm), res.tpeOpt.get, message.Reporter.create).get
                Util.extractAssignExpOpt(mi) match {
                  case Some(ae) => (mi, AST.Util.substAssignExp(ae, tsm ++ msm.entries))
                  case _ => return errSp()
                }
              case info: TypeInfo.Adt =>
                val mi = info.methods.get(res.id).get
                val tsm = TypeChecker.buildTypeSubstMap(res.owner, posOpt, info.ast.typeParams,
                  receiver.typedOpt.get.asInstanceOf[AST.Typed.Name].args, reporter).get
                val msm = TypeChecker.unifyFun(Logika.kind, logika.th, unfoldFrom.posOpt, typeRel,
                  mi.ast.sig.funType.subst(tsm), res.tpeOpt.get, message.Reporter.create).get
                Util.extractAssignExpOpt(mi) match {
                  case Some(ae) => (mi, AST.Util.substAssignExp(ae, tsm ++ msm.entries))
                  case _ => return errSp()
                }
              case _ =>
                return errSp()
            }
          }
        case _ => return errSp()
      }

      val unfoldFromPos = unfoldFrom.posOpt.get
      val oldContext = minfo.name
      val newContext = minfo.name :+ s"_${unfoldFromPos.beginLine}_${unfoldFromPos.beginColumn}"

      var vals = ISZ[AST.Stmt]()
      var locals = ISZ[AST.ResolvedInfo.LocalVar]()
      var thisIdentOpt = MOption.none[AST.Exp]()
      if (!minfo.isInObject) {
        val local = AST.ResolvedInfo.LocalVar(newContext,
          AST.ResolvedInfo.LocalVar.Scope.Current, F, T, s"this$$${unfoldFromPos.beginLine}_${unfoldFromPos.beginColumn}")
        val receiver = unfoldFrom.receiverOpt.get
        val id = AST.Id(local.id, AST.Attr(receiver.posOpt))
        val localOpt = Option.some[AST.ResolvedInfo](local)
        vals = vals :+ AST.Stmt.Var(F, T, id, None(), Some(AST.Stmt.Expr(receiver,
          AST.TypedAttr(receiver.posOpt, receiver.typedOpt))),
          AST.ResolvedAttr(receiver.posOpt, localOpt, receiver.typedOpt))
        thisIdentOpt = MSome(AST.Exp.Ident(id, AST.ResolvedAttr(receiver.posOpt, localOpt, receiver.typedOpt)))
      }

      for (i <- 0 until minfo.ast.sig.params.size) {
        val p = minfo.ast.sig.params(i)
        val arg = unfoldFrom.args(i)
        val local = AST.ResolvedInfo.LocalVar(newContext,
          AST.ResolvedInfo.LocalVar.Scope.Current, F, T, p.id.value)
        locals = locals :+ local
        vals = vals :+ AST.Stmt.Var(F, T, p.id, None(),
          Some(AST.Stmt.Expr(arg, AST.TypedAttr(arg.posOpt, arg.typedOpt))),
          AST.ResolvedAttr(arg.posOpt, Some(local), arg.typedOpt))
      }

      val newBody = substAssignExpLocalVarContext(body, oldContext, newContext, thisIdentOpt).asStmt
      val unfoldFromSpBlock = AST.Exp.StrictPureBlock(AST.Stmt.Block(AST.Body(vals :+ newBody, locals),
        AST.Attr(unfoldFrom.posOpt)), AST.TypedAttr(unfoldFrom.posOpt, unfoldFrom.typedOpt))

      val unfoldToNorm = logika.th.normalizeExp(unfoldTo)
      val unfoldFromSpBlockNorm = logika.th.normalizeExp(unfoldFromSpBlock)
      if (unfoldToNorm != unfoldFromSpBlockNorm) {
        reporter.error(posOpt, Logika.kind,
          st"The labeled expression #$num in the stated claim and in $fromStepId's' claim are not equivalent after ${if (isUnfold) "unfolding" else "folding"}".render)
        return err
      }
    }

    if (logika.config.detailedInfo) {
      val eqSTs: ISZ[ST] = for (num <- sortedNums) yield
        st"""+ Labeled expression #$num:
            |
            |  ${unfoldFromMap.get(num).get}
            |  ≡
            |  ${unfoldToMap.get(num).get}"""
      val desc = st"$justId (of ${(justificationName, ".")})"
      reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Accepted by using the $desc
            |proof tactic implemented in the $name, because:
            |
            |* The claims of proof steps $fromStepId and ${step.id} abstracted over matching
            |  $labeled are structurally equivalent, i.e.,
            |
            |  $aFromClaim
            |  ≡
            |  $aToClaim
            |
            |* Each of the matching labeled expressions are proven to be
            |  equivalent by ${if (isUnfold) "unfolding" else "folding"}, i.e.,
            |
            |  ${(eqSTs, "\n\n")}
            |""".render)
    }

    return logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
  }
}
