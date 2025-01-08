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
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}

object ValIntroElimPlugin {
  @record class Substitutor(val i: Z, val map: HashSMap[ISZ[String], (Z, message.Position, AST.Exp)]) extends AST.Util.InvocationSubstitutor {
    override def preExpIdent(o: AST.Exp.Ident): AST.MTransformer.PreResult[AST.Exp] = {
      o.resOpt match {
        case Some(res: AST.ResolvedInfo.LocalVar) =>
          map.get(res.context :+ res.id) match {
            case Some((index, _, e)) if i > index => return AST.MTransformer.PreResult(F, MSome(e))
            case _ =>
          }
        case _ =>
      }
      return AST.MTransformer.PreResultExpIdent
    }
  }
}

@datatype class ValIntroElimPlugin extends JustificationPlugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "ValIntroElimPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return (res.id == "ValE" || res.id == "ValI") && res.owner == justificationName
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
    val isElim = justId == "ValE"
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

    val tOpt = Plugin.commonLabeled(logika.th, posOpt, fromStepId, if (isElim) fromClaim else step.claim,
      if (isElim) step.claim else fromClaim, reporter)
    if (tOpt.isEmpty) {
      return err
    }

    val Plugin.CommonLabeledResult(sortedNums, fromMap, toMap, labeled, aFromClaim, aToClaim) = tOpt.get

    val (text, fid, tid, fClaim, tClaim): (String, AST.ProofAst.StepId, AST.ProofAst.StepId, AST.Exp, AST.Exp) =
      if (isElim) (s"val-elimination${if (sortedNums.size > 1) "s" else ""}", fromStepId, step.id, fromClaim, step.claim)
      else (s"val-introduction${if (sortedNums.size > 1) "s" else ""}", step.id, fromStepId, step.claim, fromClaim)

    var evidence = ISZ[ST]()
    var ok = T
    for (num <- sortedNums) {
      val from: AST.Exp.StrictPureBlock = fromMap.get(num).get.exp match {
        case e: AST.Exp.StrictPureBlock => e
        case e =>
          reporter.error(e.posOpt, Logika.kind, s"Expecting a strictly pure block expression")
          return err
      }
      var fromVals = HashSMap.empty[String, (Z, AST.Stmt.Var)]
      for (i <- 0 until from.block.body.stmts.size) {
        from.block.body.stmts(i) match {
          case stmt: AST.Stmt.Var => fromVals = fromVals + stmt.id.value ~> (i, stmt)
          case _ =>
        }
      }
      val to: AST.Exp.StrictPureBlock = toMap.get(num).get.exp match {
        case e: AST.Exp.StrictPureBlock => e
        case e =>
          reporter.error(e.posOpt, Logika.kind, s"Expecting a strictly pure block expression")
          return err
      }
      var toValIds = ISZ[String]()
      for (stmt <- to.block.body.stmts) {
        stmt match {
          case stmt: AST.Stmt.Var => toValIds = toValIds :+ stmt.id.value
          case _ =>
        }
      }
      fromVals = fromVals -- toValIds
      if (fromVals.isEmpty) {
        reporter.error(posOpt, Logika.kind, s"Expecting more val definitions in labeled #$num of $fid than of $tid")
        return err
      }

      var lvMap = HashSMap.empty[ISZ[String], (Z, message.Position, AST.Exp)]
      for (p <- fromVals.values) {
        val (index, v) = p
        val res = v.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
        v.initOpt.get match {
          case init: AST.Stmt.Expr => lvMap = lvMap + (res.context :+ res.id) ~> (index, v.posOpt.get, init.exp)
          case init =>
            val stmt = init.asStmt
            lvMap = lvMap + (res.context :+ res.id) ~> (index, v.posOpt.get, AST.Exp.StrictPureBlock(AST.Stmt.Block(
              AST.Body(ISZ(stmt), ISZ()), AST.Attr(stmt.posOpt)), AST.TypedAttr(stmt.posOpt, v.attr.typedOpt)))
        }
      }

      var newStmts = ISZ[AST.Stmt]()
      for (i <- 0 until from.block.body.stmts.size) {
        var subst = T
        val stmt = from.block.body.stmts(i)
        stmt match {
          case stmt: AST.Stmt.Var =>
            val res = stmt.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
            if (fromVals.contains(res.id)) {
              subst = F
            }
          case _ =>
        }
        if (subst) {
          val s = ValIntroElimPlugin.Substitutor(i, lvMap)
          newStmts = newStmts :+ s.transformStmt(stmt).getOrElseEager(stmt)
        }
      }

      val newFrom = from(block = from.block(body = from.block.body(stmts = newStmts)))
      val fromNorm = logika.th.normalizeExp(newFrom)
      val toNorm = logika.th.normalizeExp(to)
      if (fromNorm != toNorm) {
        ok = F
        reporter.error(posOpt, Logika.kind, s"The labeled expression #$num of $fid and $tid are not equivalent after $text")
      } else if (logika.config.detailedInfo) {
        val substs: ISZ[ST] = for (p <- lvMap.entries) yield st"${p._2._3.prettyST} / ${p._1(p._1.size - 1)} @L${p._2._2.beginLine}"
        evidence = evidence :+
          st"""+ Labeled expression #$num:
              |
              |  [${(substs, ", ")}](
              |    ${fClaim.prettyST}
              |  )
              |  ≡
              |  ${tClaim.prettyST}"""
      }
    }

    if (!ok) {
      return err
    }

    if (logika.config.detailedInfo) {
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
            |* Each of the matching labeled expressions are equivalent by
            |  val-definition substitution${if (sortedNums.size > 1) "s" else ""}, i.e.,
            |
            |  ${(evidence, "\n\n")}
            |""".render)
    }

    return logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
  }
}
