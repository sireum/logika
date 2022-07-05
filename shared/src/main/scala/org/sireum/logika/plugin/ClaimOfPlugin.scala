// #Sireum

package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.symbol.Info
import org.sireum.lang.{ast => AST}
import org.sireum.logika.{Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

@datatype class ClaimOfPlugin extends Plugin {

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val name: String = "ClaimOfPlugin"

  @pure override def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Incept =>
        just.invokeIdent.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Method => return res.id == "ClaimOf" && res.owner == justificationName
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
    @strictpure def err(): Plugin.Result = Plugin.Result(F, state.nextFresh, state.claims)
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Justification.Incept]
    val arg: AST.Exp = just.args(0) match {
      case a: AST.Exp.Eta => a.ref.asExp
      case a =>
        reporter.error(a.posOpt, Logika.kind, s"Expecting an eta expansion of a fact, theorem, or lemma")
        return err()
    }
    val (name, targs): (ISZ[String], ISZ[AST.Typed]) = arg match {
      case arg: AST.Exp.Ident =>
        arg.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Fact => (res.name, ISZ())
          case res: AST.ResolvedInfo.Theorem => (res.name, ISZ())
          case _ =>
            reporter.error(arg.posOpt, Logika.kind, s"Expecting a fact, theorem, or lemma")
            return err()
        }
      case arg: AST.Exp.Select =>
        arg.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Fact => (res.name, for (t <- arg.targs) yield t.typedOpt.get)
          case res: AST.ResolvedInfo.Theorem => (res.name, ISZ())
          case _ =>
            reporter.error(arg.posOpt, Logika.kind, s"Expecting a fact, theorem, or lemma")
            return err()
        }
      case arg =>
        reporter.error(arg.posOpt, Logika.kind, s"Expecting a name, but found $arg")
        return err()
    }

    val (kind, typeParams, claims): (String, ISZ[AST.TypeParam], ISZ[AST.Exp]) = logika.th.nameMap.get(name).get match {
      case inf: Info.Fact => ("Fact", inf.ast.typeParams, inf.ast.claims)
      case inf: Info.Theorem => (if (inf.ast.isLemma) "Lemma" else "Theorem", inf.ast.typeParams, ISZ(inf.ast.claim))
      case _ => halt("Infeasible")
    }
    val sm = lang.tipe.TypeChecker.buildTypeSubstMap(name, arg.posOpt, typeParams, targs, reporter).get
    val stepClaim = AST.Util.normalizeExp(step.claim)
    for (claim <- claims) {
      val normClaim = AST.Util.normalizeExp(claim)
      val substNormClaim = AST.Util.substExpSkipResolvedInfo(normClaim, sm)
      if (stepClaim == substNormClaim) {
        val claimPos = claim.posOpt.get
        val q = logika.evalRegularStepClaim(smt2, cache, state, step.claim, step.id.posOpt, reporter)
        val (stat, nextFresh, claims) = (q._1, q._2, q._3 :+ q._4)
        if (stat) {
          reporter.inform(step.claim.posOpt.get, Reporter.Info.Kind.Verified,
            st"""Accepted by using $kind ${(name, ".")}'s claim at [${claimPos.beginLine}, ${claimPos.beginColumn}], i.e.:
                |
                |$claim
                |""".render)
        }
        return Plugin.Result(stat, nextFresh, claims)
      }
    }

    reporter.error(step.claim.posOpt, Logika.kind, st"Could not find the stated claim in $kind ${(name, ".")}".render)
    return err()
  }

}
