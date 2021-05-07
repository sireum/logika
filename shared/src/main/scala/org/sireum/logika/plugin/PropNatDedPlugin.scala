// #Sireum
/*
 Copyright (c) 2021, Robby, Kansas State University
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

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("OrE", "ImplyI", "NegI", "BottomE", "PbC")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification", "natded", "prop")

  val bottom: AST.Exp = AST.Exp.LitB(F, AST.Attr(None()))

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Incept =>
        val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
        return justificationIds.contains(res.id) && res.owner == justificationName
      case _ => return F
    }
  }

  override def handle(logika: Logika,
                      smt2: Smt2,
                      log: B,
                      logDirOpt: Option[String],
                      spcMap: HashSMap[Z, StepProofContext],
                      state: State,
                      step: AST.ProofAst.Step.Regular,
                      reporter: Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, state.claims)
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
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Incept]
    val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    var args = ISZ[AST.Exp.LitZ]()
    for (arg <- just.args) {
      arg match {
        case arg: AST.Exp.LitZ => args = args :+ arg
        case _ => reporter.error(arg.posOpt, Logika.kind, "Expecting a proof step number literal")
      }
    }
    if (args.size != just.args.size) {
      return emptyResult
    }
    res.id match {
      case string"OrE" =>
        val ISZ(orClaimNo, leftSubProofNo, rightSubProofNo) = args
        val orClaim: AST.Exp.Binary = spcMap.get(orClaimNo.value) match {
          case Some(StepProofContext.Regular(_, exp: AST.Exp.Binary, _)) if isBuiltIn(exp, AST.ResolvedInfo.BuiltIn.Kind.BinaryOr) => exp
          case _ =>
            reporter.error(orClaimNo.posOpt, Logika.kind, s"Expecting a proof step with a disjunction binary expression claim")
            return emptyResult
        }
        val leftSubProof: HashSet[AST.Exp] = spcMap.get(leftSubProofNo.value) match {
          case Some(sp@StepProofContext.SubProof(_, exp, _)) if exp == orClaim.left => HashSet ++ sp.claims
          case _ =>
            reporter.error(leftSubProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the left-operand of #${orClaimNo.value}'s claim'")
            return emptyResult
        }
        val rightSubProof: HashSet[AST.Exp] = spcMap.get(rightSubProofNo.value) match {
          case Some(sp@StepProofContext.SubProof(_, exp, _)) if exp == orClaim.right => HashSet ++ sp.claims
          case _ =>
            reporter.error(rightSubProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the right-operand of #${orClaimNo.value}'s claim'")
            return emptyResult
        }
        val ok = leftSubProof.contains(step.claim) && rightSubProof.contains(step.claim)
        if (!ok) {
          step.claim match {
            case stepClaim: AST.Exp.Binary if isBuiltIn(stepClaim, AST.ResolvedInfo.BuiltIn.Kind.BinaryOr) && leftSubProof.contains(stepClaim.left) && rightSubProof.contains(stepClaim.right) =>
            case _ =>
              reporter.error(step.no.posOpt, Logika.kind, s"Could not infer the stated claim from both sub-proofs #${leftSubProofNo.value} and #${rightSubProofNo.value} using ${just.invokeIdent.id.value}")
              return emptyResult
          }
        }
      case string"ImplyI" =>
        val claim: AST.Exp.Binary = step.claim match {
          case stepClaim: AST.Exp.Binary if isBuiltIn(stepClaim, AST.ResolvedInfo.BuiltIn.Kind.BinaryImply) => stepClaim
          case _ =>
            reporter.error(step.claim.posOpt, Logika.kind, s"Expecting an implication")
            return emptyResult
        }
        val ISZ(subProofNo) = args
        val subProof: HashSet[AST.Exp] = spcMap.get(subProofNo.value) match {
          case Some(sp: StepProofContext.SubProof) if sp.assumption == claim.left => HashSet ++ sp.claims + sp.assumption
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the antecedent of step #${step.no.value}'s claim")
            return emptyResult
        }
        if (!subProof.contains(claim.right)) {
          reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find the consequent of step #${step.no.value}'s claim in sub-proof #${subProofNo.value}")
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
        val subProof: HashSet[AST.Exp] = spcMap.get(subProofNo.value) match {
          case Some(sp: StepProofContext.SubProof) if sp.assumption == claim.exp => HashSet ++ sp.claims
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the operand of step #${step.no.value}'s claim")
            return emptyResult
        }
        if (!subProof.contains(bottom)) {
          reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find F in sub-proof #${subProofNo.value}")
          return emptyResult
        }
      case string"BottomE" =>
        val ISZ(bottomNo) = args
        spcMap.get(bottomNo.value) match {
          case Some(sp: StepProofContext.Regular) if sp.exp == bottom =>
          case _ =>
            reporter.error(bottomNo.posOpt, Logika.kind, s"Expecting F as step #${bottomNo.value}'s claim")
            return emptyResult
        }
      case string"PbC" =>
        val ISZ(subProofNo) = args
        val subProof: HashSet[AST.Exp] = spcMap.get(subProofNo.value) match {
          case Some(sp: StepProofContext.SubProof) if isUBuiltIn(sp.assumption, AST.ResolvedInfo.BuiltIn.Kind.UnaryNot) => HashSet ++ sp.claims
          case _ =>
            reporter.error(subProofNo.posOpt, Logika.kind, s"Expecting a sub-proof step assuming the negation of step #${step.no.value}'s claim")
            return emptyResult
        }
        if (!subProof.contains(bottom)) {
          reporter.error(subProofNo.posOpt, Logika.kind, s"Could not find F in sub-proof #${subProofNo.value}")
          return emptyResult
        }
    }
    val (status, nextFresh, claims, claim) = logika.evalRegularStepClaim(smt2, state, step.claim, step.no.posOpt, reporter)
    return Plugin.Result(status, nextFresh, claims :+ claim)
  }
}