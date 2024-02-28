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
package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.{ast => AST}
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

@datatype class PropNatDedPlugin extends JustificationPlugin {

  val name: String = "PropNatDedPlugin"

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("OrE", "ImplyI", "SImplyI", "NegI", "BottomE", "PbC")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification", "natded", "prop")

  val bottom: AST.Exp = AST.Exp.LitB(F, AST.Attr(None()))

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply if !just.hasWitness =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return justificationIds.contains(res.id) && res.owner == justificationName
          case _ => return F
        }
      case _ => return F
    }
  }

  override def checkMode(logika: Logika, just: AST.ProofAst.Step.Justification, reporter: Reporter): B = {
    return T
  }

  override def handle(logika: Logika,
                      smt2: Smt2,
                      cache: Logika.Cache,
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): State = {
    @strictpure def err: State = state(status = State.Status.Error)
    @pure def isBuiltIn(exp: AST.Exp.Binary, kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.BuiltIn if res.kind == kind => return T
        case _ => return F
      }
    }
    @pure def isUBuiltIn(exp: AST.Exp, kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
      exp match {
        case exp: AST.Exp.Unary =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.BuiltIn if res.kind == kind => return T
            case _ =>
          }        case _ =>
      }
      return F
    }
    @pure def isBottom(exp: AST.Exp): B = {
      if (exp == bottom) {
        return T
      }
      val res: AST.ResolvedInfo = exp match {
        case exp: AST.Exp.Ident => exp.attr.resOpt.get
        case exp: AST.Exp.Select => exp.attr.resOpt.get
        case _ => return F
      }
      res match {
        case res: AST.ResolvedInfo.Var => return res.id == "F" && res.owner == AST.Typed.sireumName
        case _ => return F
      }
    }
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    val argsOpt = AST.Util.toStepIds(just.args, Logika.kind, reporter)
    if (argsOpt.isEmpty) {
      return err
    }
    val args = argsOpt.get
    var acceptedMsg: ST =
      st"""Accepted by using the ${res.id} proof tactic implemented in the $name,
          |because"""

    def implyH(opKind: AST.ResolvedInfo.BuiltIn.Kind.Type, opDesc: String): B = {
      val claim: AST.Exp.Binary = step.claim match {
        case stepClaim: AST.Exp.Binary if isBuiltIn(stepClaim, opKind) => stepClaim
        case _ =>
          reporter.error(step.claim.posOpt, Logika.kind, s"Expecting $opDesc")
          return F
      }
      val ISZ(subProofNo) = args
      val subProof: HashSet[AST.Exp] = spcMap.get(subProofNo) match {
        case Some(sp: StepProofContext.SubProof) if sp.assumption == logika.th.normalizeExp(claim.left) => HashSet ++ sp.claims + sp.assumption
        case _ =>
          reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the antecedent of step ${step.id}'s claim")
          return F
      }
      if (!subProof.contains(logika.th.normalizeExp(claim.right))) {
        reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find the consequent of step ${step.id}'s claim in sub-proof $subProofNo")
        return F
      }
      acceptedMsg =
        st"""$acceptedMsg sub-proof $subProofNo:
            |
            | * starts by assuming ${step.id}'s antecedent claim, i.e., ${claim.left.prettyST}, and
            |
            | * proves ${step.id}'s consequent claim, i.e., ${claim.right.prettyST}
            |"""
      return T
    }

    res.id match {
      case string"OrE" =>
        val ISZ(orClaimNo, leftSubProofNo, rightSubProofNo) = args
        val orClaim: AST.Exp.Binary = spcMap.get(orClaimNo) match {
          case Some(StepProofContext.Regular(_, _, exp: AST.Exp.Binary)) if isBuiltIn(exp, AST.ResolvedInfo.BuiltIn.Kind.BinaryOr) =>
            exp
          case Some(StepProofContext.Regular(_, _, exp: AST.Exp.Binary)) if isBuiltIn(exp, AST.ResolvedInfo.BuiltIn.Kind.BinaryLe) =>
            AST.Exp.Binary(
              exp(op = AST.Exp.BinaryOp.Lt, attr = exp.attr(resOpt = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryLt)))),
              AST.Exp.BinaryOp.Or,
              exp(op = AST.Exp.BinaryOp.Eq, attr = exp.attr(resOpt = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryEq)))),
              AST.ResolvedAttr(exp.posOpt, Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryOr)), AST.Typed.bOpt), exp.posOpt
            )
          case Some(StepProofContext.Regular(_, _, exp: AST.Exp.Binary)) if isBuiltIn(exp, AST.ResolvedInfo.BuiltIn.Kind.BinaryGe) =>
            AST.Exp.Binary(
              exp(op = AST.Exp.BinaryOp.Gt, attr = exp.attr(resOpt = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryGt)))),
              AST.Exp.BinaryOp.Or,
              exp(op = AST.Exp.BinaryOp.Eq, attr = exp.attr(resOpt = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryEq)))),
              AST.ResolvedAttr(exp.posOpt, Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryOr)), AST.Typed.bOpt), exp.posOpt
            )
          case _ =>
            reporter.error(orClaimNo.posOpt, Logika.kind, s"Expecting a proof step with a disjunction binary expression claim")
            return err
        }
        val leftSubProof: HashSet[AST.Exp] = spcMap.get(leftSubProofNo) match {
          case Some(sp@StepProofContext.SubProof(_, exp, _)) if exp == logika.th.normalizeExp(orClaim.left) => HashSet ++ sp.claims
          case _ =>
            reporter.error(leftSubProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the left-operand of $orClaimNo's claim")
            return err
        }
        val rightSubProof: HashSet[AST.Exp] = spcMap.get(rightSubProofNo) match {
          case Some(sp@StepProofContext.SubProof(_, exp, _)) if exp == logika.th.normalizeExp(orClaim.right) => HashSet ++ sp.claims
          case _ =>
            reporter.error(rightSubProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the right-operand of $orClaimNo's claim")
            return err
        }
        val stepClaim = logika.th.normalizeExp(step.claim)
        if (leftSubProof.contains(stepClaim) && rightSubProof.contains(stepClaim)) {
          acceptedMsg =
            st"""$acceptedMsg: sub-proofs $leftSubProofNo and $rightSubProofNo contain ${step.id}'s claim:
                |
                |* sub-proof $leftSubProofNo starts with assuming the left-hand-side of $orClaimNo,
                |
                |* sub-proof $rightSubProofNo starts with assuming the right-hand-side of $orClaimNo, and
                |
                |* both sub-proofs proves ${step.claim.prettyST}"""
        } else {
          stepClaim match {
            case stepClaim: AST.Exp.Binary if isBuiltIn(stepClaim, AST.ResolvedInfo.BuiltIn.Kind.BinaryOr) && leftSubProof.contains(logika.th.normalizeExp(stepClaim.left)) && rightSubProof.contains(logika.th.normalizeExp(stepClaim.right)) =>
            case _ =>
              reporter.error(step.id.posOpt, Logika.kind, s"Could not infer the stated claim from both sub-proofs $leftSubProofNo and $rightSubProofNo using ${just.invokeIdent.id.value}")
              return err
          }
        }
      case string"ImplyI" =>
        if(!implyH(AST.ResolvedInfo.BuiltIn.Kind.BinaryImply, "an implication")) {
          return err
        }
      case string"SImplyI" =>
        if (!implyH(AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply, "a conditional implication")) {
          return err
        }
      case string"NegI" =>
        val claim: AST.Exp.Unary = step.claim match {
          case stepClaim: AST.Exp.Unary if isUBuiltIn(stepClaim, AST.ResolvedInfo.BuiltIn.Kind.UnaryNot) => stepClaim
          case _ =>
            reporter.error(step.claim.posOpt, Logika.kind, s"Expecting an implication")
            return err
        }
        val ISZ(subProofNo) = args
        val subProof: ISZ[AST.Exp] = spcMap.get(subProofNo) match {
          case Some(sp: StepProofContext.SubProof) if sp.assumption == logika.th.normalizeExp(claim.exp) => sp.claims
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the operand of step ${step.id}'s claim")
            return err
        }
        if (ops.ISZOps(subProof).exists(isBottom _)) {
          acceptedMsg =
            st"""$acceptedMsg because sub-proof $subProofNo:
                |
                |* starts with assuming the non-negation of ${step.id}'s claim, and
                |
                |* proves F
                |"""
        } else {
          reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find F in sub-proof $subProofNo")
          return err
        }
      case string"BottomE" =>
        val ISZ(bottomNo) = args
        spcMap.get(bottomNo) match {
          case Some(sp: StepProofContext.Regular) if isBottom(sp.exp) =>
            acceptedMsg =
              st"""$acceptedMsg ${sp.stepNo}'s claim is F
                  |"""
          case _ =>
            reporter.error(bottomNo.posOpt, Logika.kind, s"Expecting F as step $bottomNo's claim")
            return err
        }
      case string"PbC" =>
        val ISZ(subProofNo) = args
        val subProof: ISZ[AST.Exp] = spcMap.get(subProofNo) match {
          case Some(sp: StepProofContext.SubProof) if isUBuiltIn(sp.assumption, AST.ResolvedInfo.BuiltIn.Kind.UnaryNot) => sp.claims
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the negation of step ${step.id}'s claim")
            return err
        }
        if (ops.ISZOps(subProof).exists(isBottom _)) {
          acceptedMsg =
            st"""$acceptedMsg sub-proof $subProofNo:
                |
                |* starts with assuming the negation of ${step.id}'s claim, and
                |
                |* proves F
                |"""
        } else {
          reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find F in sub-proof $subProofNo")
          return err
        }
    }
    val s0 = logika.evalRegularStepClaimRtCheck(smt2, cache, F, state, step.claim, step.id.posOpt, reporter)
    if (s0.ok) {
      reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified, acceptedMsg.render)
    }
    return s0
  }
}