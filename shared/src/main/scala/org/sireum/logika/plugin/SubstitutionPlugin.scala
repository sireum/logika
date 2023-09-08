// #Sireum
/*
 Copyright (c) 2017-2023, Ryan Peroutka, Galois, Inc.
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
import org.sireum.lang.ast.MTransformer.PreResult
import org.sireum.{B, HashSMap}
import org.sireum.lang.ast.{Exp, ProofAst, ResolvedAttr, ResolvedInfo}
import org.sireum.lang.ast.ProofAst.Step
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Reporter
import org.sireum.logika.plugin.SubstitutionPlugin.resolveOp
import org.sireum.ops.ISZOps

@datatype class SubstitutionPlugin extends JustificationPlugin {

  val name: String = "SubstitutionPlugin"

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("Subst_>", "Subst_<")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  override def canHandle(logika: Logika, just: Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return justificationIds.contains(res.id) && res.owner == justificationName
          case _ => return F
        }
      case _ => return F
    }
  }

  override def handle(logika: Logika, smt2: Smt2, cache: Logika.Cache, spcMap: HashSMap[ProofAst.StepId, StepProofContext], state: State, step: Step.Regular, reporter: Logika.Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())

    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Apply]
    val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
    val ISZ(x, y) = AST.Util.toStepIds(just.args, Logika.kind, reporter).get

    spcMap.get(x) match {
      case Some(xSpc: StepProofContext.Regular) =>
        xSpc.exp match {
          case b@AST.Exp.Binary(e1, _, e2) =>
            resolveOp(b) match {
              case AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv =>
              case AST.ResolvedInfo.BuiltIn.Kind.BinaryEq =>
                if (!logika.th.isSubstitutableWithoutSpecVars(b.typedOpt.get)) {
                  val msg = s"Step $x must be substitutable without spec vars in or to use ${AST.ResolvedInfo.BuiltIn.Kind.BinaryEq} for substitution"
                  reporter.error(x.attr.posOpt, Logika.kind, msg)
                  return emptyResult
                }
              case _ =>
                val msg = s"The first expression argument of step $x for ${res.id} in step ${step.id} has to be an equality"
                reporter.error(x.attr.posOpt, Logika.kind, msg)
                return emptyResult
            }
            val (sub, repl): (AST.Exp, AST.Exp) = res.id match {
              case "Subst_<" => (e1, e2)
              case "Subst_>" => (e2, e1)
            }
            spcMap.get(y) match {
              case Some(ySpc: StepProofContext.Regular) =>
                val exp = ySpc.exp
                val s = SubstitutionPlugin.Substitutor(sub, repl)
                val subResult = s.transformExp(exp).getOrElseEager(exp)
                if (subResult != step.claim) {
                  val msg = s"Claim ${step.id} does not match the substituted expression of ${res.id} of $x for $y"
                  reporter.error(step.claim.posOpt, Logika.kind, msg)
                  return emptyResult
                } else {
                  val q = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
                  val (stat, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
                  if (stat && logika.config.detailedInfo) {
                    val msg = s"Accepted because the claim of step ${step.id} matches ${ySpc.exp} with $sub replaced by $repl"
                    reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified, msg)
                  }
                  return Plugin.Result(stat, nextFresh, claims)
                }
              case Some(_) =>
                reporter.error(y.posOpt, Logika.kind, s"Cannot use compound proof step $y as an argument for Substitution")
                return emptyResult
              case _ =>
                reporter.error(y.posOpt, Logika.kind, s"Could not find proof step $y")
                return emptyResult
            }
          case _ =>
            val msg = s"The first expression argument of step $x for ${res.id} in step ${step.id} has to be an equality"
            reporter.error(x.attr.posOpt, Logika.kind, msg)
            return emptyResult
        }
      case Some(_) =>
        reporter.error(x.posOpt, Logika.kind, s"Cannot use compound proof step $x as an argument for Substitution")
        return emptyResult
      case _ =>
        reporter.error(x.posOpt, Logika.kind, s"Could not find proof step $x")
        return emptyResult
    }
  }
}

object SubstitutionPlugin {

  def resolveOp(b: AST.Exp.Binary): ResolvedInfo.BuiltIn.Kind.Type = {
    b.attr.resOpt.get match {
      case AST.ResolvedInfo.BuiltIn(kind) => return kind
      case _ => halt("???")
    }
  }

  @record class Substitutor(val sub: AST.Exp, val repl: AST.Exp) extends Plugin.InvocationSubstitutor {

    override def preExp(exp: AST.Exp): PreResult[AST.Exp] = {
      if (exp == sub) {
        return PreResult(F, MSome(repl))
      } else {
        return PreResult(T, MNone())
      }
    }
  }
}
