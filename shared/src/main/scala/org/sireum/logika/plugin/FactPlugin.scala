// #Sireum

package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.symbol.Info
import org.sireum.lang.{ast => AST}
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

@datatype class FactPlugin extends Plugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "FactPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Incept =>
        val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
        return res.id == "FactClaim" && res.owner == justificationName
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
    @strictpure def err(): Plugin.Result = Plugin.Result(F, state.nextFresh, state.claims)
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Incept]
    val arg: AST.Exp = just.args(0) match {
      case a: AST.Exp.Eta => a.ref.asExp
      case a =>
        reporter.error(a.posOpt, Logika.kind, s"Expecting an eta expansion of a fact")
        return err()
    }
    val name: ISZ[String] = arg match {
      case arg: AST.Exp.Ident =>
        arg.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Fact => res.name
          case _ =>
            reporter.error(arg.posOpt, Logika.kind, s"Expecting a fact")
            return err()
        }
      case arg: AST.Exp.Select =>
        arg.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Fact => res.name
          case _ =>
            reporter.error(arg.posOpt, Logika.kind, s"Expecting a fact")
            return err()
        }
      case arg =>
        reporter.error(arg.posOpt, Logika.kind, s"Expecting a name, but found $arg")
        return err()
    }

    val info = logika.th.nameMap.get(name).get.asInstanceOf[Info.Fact]
    val stepClaim = AST.Util.normalizeFun(step.claim)
    for (claim <- info.ast.claims) {
      if (stepClaim == AST.Util.normalizeFun(claim)) {
        val claimPos = claim.posOpt.get
        val q = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
        val (stat, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
        if (stat) {
          reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
            st"""Accepted by using Fact ${(name, ".")}'s claim at [${claimPos.beginLine}, ${claimPos.beginColumn}], i.e.:
                |
                |$claim
                |""".render)
        }
        return Plugin.Result(stat, nextFresh, claims)
      }
    }

    reporter.error(step.claim.posOpt, Logika.kind, st"Could not find the stated claim in Fact ${(name, ".")}".render)
    return err()
  }

}
