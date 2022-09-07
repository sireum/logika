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
package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.{ast => AST}
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

@datatype class PropNatDedPlugin extends Plugin {

  val name: String = "PropNatDedPlugin"

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("OrE", "ImplyI", "SImplyI", "NegI", "BottomE", "PbC")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification", "natded", "prop")

  val bottom: AST.Exp = AST.Exp.LitB(F, AST.Attr(None()))

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return justificationIds.contains(res.id) && res.owner == justificationName
          case _ => return F
        }
      case _ => return F
    }
  }

  override def handle(logika: Logika,
                      smt2: Smt2,
                      cache: Smt2.Cache,
                      log: B,
                      logDirOpt: Option[String],
                      spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): Plugin.Result = {
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
        case res: AST.ResolvedInfo.Var => return res.id === "F" && res.owner == AST.Typed.sireumName
        case _ =>return F
      }
    }
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, state.claims)
    val argsOpt = AST.Util.toStepIds(just.args, Logika.kind, reporter)
    if (argsOpt.isEmpty) {
      return emptyResult
    }
    val args = argsOpt.get

    def implyH(opKind: AST.ResolvedInfo.BuiltIn.Kind.Type, opDesc: String): B = {
      val claim: AST.Exp.Binary = step.claim match {
        case stepClaim: AST.Exp.Binary if isBuiltIn(stepClaim, AST.ResolvedInfo.BuiltIn.Kind.BinaryImply) => stepClaim
        case _ =>
          reporter.error(step.claim.posOpt, Logika.kind, s"Expecting an $opDesc")
          return F
      }
      val ISZ(subProofNo) = args
      val subProof: HashSet[AST.Exp] = spcMap.get(subProofNo) match {
        case Some(sp: StepProofContext.SubProof) if sp.assumption == AST.Util.normalizeExp(claim.left) => HashSet ++ sp.claims + sp.assumption
        case _ =>
          reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the antecedent of step ${step.id}'s claim")
          return F
      }
      if (!subProof.contains(AST.Util.normalizeExp(claim.right))) {
        reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find the consequent of step ${step.id}'s claim in sub-proof $subProofNo")
        return F
      }
      return T
    }

    res.id match {
      case string"OrE" =>
        val ISZ(orClaimNo, leftSubProofNo, rightSubProofNo) = args
        val orClaim: AST.Exp.Binary = spcMap.get(orClaimNo) match {
          case Some(StepProofContext.Regular(_, exp: AST.Exp.Binary, _)) if isBuiltIn(exp, AST.ResolvedInfo.BuiltIn.Kind.BinaryOr) => exp
          case _ =>
            reporter.error(orClaimNo.posOpt, Logika.kind, s"Expecting a proof step with a disjunction binary expression claim")
            return emptyResult
        }
        val leftSubProof: HashSet[AST.Exp] = spcMap.get(leftSubProofNo) match {
          case Some(sp@StepProofContext.SubProof(_, exp, _)) if exp == AST.Util.normalizeExp(orClaim.left) => HashSet ++ sp.claims
          case _ =>
            reporter.error(leftSubProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the left-operand of $orClaimNo's claim")
            return emptyResult
        }
        val rightSubProof: HashSet[AST.Exp] = spcMap.get(rightSubProofNo) match {
          case Some(sp@StepProofContext.SubProof(_, exp, _)) if exp == AST.Util.normalizeExp(orClaim.right) => HashSet ++ sp.claims
          case _ =>
            reporter.error(rightSubProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the right-operand of $orClaimNo's claim")
            return emptyResult
        }
        val stepClaim = step.claimNorm
        val ok = leftSubProof.contains(stepClaim) && rightSubProof.contains(stepClaim)
        if (!ok) {
          stepClaim match {
            case stepClaim: AST.Exp.Binary if isBuiltIn(stepClaim, AST.ResolvedInfo.BuiltIn.Kind.BinaryOr) && leftSubProof.contains(AST.Util.normalizeExp(stepClaim.left)) && rightSubProof.contains(AST.Util.normalizeExp(stepClaim.right)) =>
            case _ =>
              reporter.error(step.id.posOpt, Logika.kind, s"Could not infer the stated claim from both sub-proofs $leftSubProofNo and $rightSubProofNo using ${just.invokeIdent.id.value}")
              return emptyResult
          }
        }
      case string"ImplyI" =>
        if(!implyH(AST.ResolvedInfo.BuiltIn.Kind.BinaryImply, "implication")) {
          return emptyResult
        }
      case string"SImplyI" =>
        if (!implyH(AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply, "conditional implication")) {
          return emptyResult
        }
      case string"NegI" =>
        val claim: AST.Exp.Unary = step.claim match {
          case stepClaim: AST.Exp.Unary if isUBuiltIn(stepClaim, AST.ResolvedInfo.BuiltIn.Kind.UnaryNot) => stepClaim
          case _ =>
            reporter.error(step.claim.posOpt, Logika.kind, s"Expecting an implication")
            return emptyResult
        }
        val ISZ(subProofNo) = args
        val subProof: ISZ[AST.Exp] = spcMap.get(subProofNo) match {
          case Some(sp: StepProofContext.SubProof) if sp.assumption == AST.Util.normalizeExp(claim.exp) => sp.claims
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the operand of step ${step.id}'s claim")
            return emptyResult
        }
        if (!ops.ISZOps(subProof).exists(isBottom _)) {
          reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find F in sub-proof $subProofNo")
          return emptyResult
        }
      case string"BottomE" =>
        val ISZ(bottomNo) = args
        spcMap.get(bottomNo) match {
          case Some(sp: StepProofContext.Regular) if isBottom(sp.exp) =>
          case _ =>
            reporter.error(bottomNo.posOpt, Logika.kind, s"Expecting F as step $bottomNo's claim")
            return emptyResult
        }
      case string"PbC" =>
        val ISZ(subProofNo) = args
        val subProof: ISZ[AST.Exp] = spcMap.get(subProofNo) match {
          case Some(sp: StepProofContext.SubProof) if isUBuiltIn(sp.assumption, AST.ResolvedInfo.BuiltIn.Kind.UnaryNot) => sp.claims
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the negation of step ${step.id}'s claim")
            return emptyResult
        }
        if (!ops.ISZOps(subProof).exists(isBottom _)) {
          reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find F in sub-proof $subProofNo")
          return emptyResult
        }
    }
    val (status, nextFresh, claims, claim) = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
    if (status) {
      val desc = st"${res.id} (of ${(res.owner, ".")})".render
      reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
        st"""Accepted by using the $desc
            |proof tactic implemented in the $name""".render)
    }
    return Plugin.Result(status, nextFresh, claims :+ claim)
  }
}