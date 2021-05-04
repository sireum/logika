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
package org.sireum.logika

import org.sireum._
import org.sireum.message.Position
import org.sireum.lang.{ast => AST}
import org.sireum.lang.symbol.Info
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.tipe.TypeChecker
import org.sireum.logika.Logika._

object Plugin {
  @datatype class Result(status: B, nextFresh: Z, clams: ISZ[State.Claim])
}

@sig trait Plugin {
  @pure def canHandle(just: AST.ProofAst.Step.Justification): B

  def handle(logika: Logika,
             smt2: Smt2,
             log: B,
             logDirOpt: Option[String],
             spcMap: HashSMap[Z, StepProofContext],
             state: State,
             step: AST.ProofAst.Step.Regular,
             reporter: Reporter): Plugin.Result
}

@datatype class AutoPlugin extends Plugin {

  val justificationIds: HashSet[String] = HashSet ++ ISZ[String]("auto", "premise", "Auto", "Premise")

  val justificationName: ISZ[String] = ISZ("org", "sireum", "justification")

  val iszzTypedOpt: Option[AST.Typed] = Some(AST.Typed.Name(AST.Typed.isName, ISZ(AST.Typed.z, AST.Typed.z)))

  @pure override def canHandle(just: AST.ProofAst.Step.Justification): B = {
    just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        return justificationIds.contains(just.idString) && just.isOwnedBy(justificationName)
      case just: AST.ProofAst.Step.Justification.Incept if just.witnesses.isEmpty =>
        val res = just.invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
        return res.id == "Auto" && res.owner == justificationName
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
    var args = ISZ[AST.Exp.LitZ]()
    var ok = T
    def processArgs(id: String, justArgs: ISZ[AST.Exp]): Unit = {
      for (arg <- justArgs) {
        arg match {
          case arg: AST.Exp.LitZ => args = args :+ arg
          case arg =>
            ok = F
            reporter.error(arg.posOpt, Logika.kind, s"The $id justification only accepts an integer literal argument")
        }
      }
    }
    val (id, posOpt): (String, Option[Position]) = step.just match {
      case just: AST.ProofAst.Step.Justification.Apply =>
        val id = just.idString
        processArgs(id, just.args)
        (id, just.id.posOpt)
      case just: AST.ProofAst.Step.Justification.Incept =>
        val invokeId = just.invokeIdent.id.value
        def err(arg: AST.Exp): Unit = {
          ok = F
          reporter.error(arg.posOpt, Logika.kind, s"Invalid argument for the $invokeId justification")
        }
        if (just.args.size === 1) {
          just.args(0) match {
            case arg: AST.Exp.Invoke if arg.typedOpt == iszzTypedOpt =>
              arg.attr.resOpt.get match {
                case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Constructor => processArgs(invokeId, arg.args)
                case _ => err(arg)
              }
            case arg: AST.Exp.LitZ => args = args :+ arg
            case arg => err(arg)
          }
        } else {
          processArgs(invokeId, just.args)
        }
        (invokeId, just.invokeIdent.posOpt)
      case _ => halt("Infeasible")
    }
    if (!ok) {
      return Plugin.Result(F, state.nextFresh, ISZ())
    }

    val pos = posOpt.get

    val ((stat, nextFresh, premises, conclusion), claims): ((B, Z, ISZ[State.Claim], State.Claim), ISZ[State.Claim]) =
      if (args.isEmpty) {
        val q = logika.evalRegularStepClaim(smt2, state, step.claim, step.no.posOpt, reporter)
        (q, ops.ISZOps(q._3).slice(state.claims.size, q._3.size) :+ q._4)
      } else {
        var s0 = state(claims = ISZ())
        ok = T
        for (arg <- args) {
          val stepNo = arg.value
          spcMap.get(stepNo) match {
            case Some(spc: StepProofContext.Regular) =>
              s0 = s0.addClaim(State.Claim.And(spc.claims))
            case Some(_) =>
              reporter.error(posOpt, Logika.kind, s"Cannot use compound proof step #$stepNo as an argument for $id")
              ok = F
            case _ =>
              reporter.error(posOpt, Logika.kind, s"Could not find proof step #$stepNo")
              ok = F
          }
        }
        if (!ok) {
          return Plugin.Result(F, s0.nextFresh, s0.claims)
        }
        val q = logika.evalRegularStepClaim(smt2, s0, step.claim, step.no.posOpt, reporter)
        (q, q._3 :+ q._4)
      }
    val status: B = if (stat) {
      val r = smt2.valid(log, logDirOpt, s"$id Justification", pos, premises, conclusion, reporter)

      def error(msg: String): B = {
        reporter.error(posOpt, Logika.kind, msg)
        return F
      }

      r.kind match {
        case Smt2Query.Result.Kind.Unsat => T
        case Smt2Query.Result.Kind.Sat => error(s"Invalid claim of proof step #${step.no.value}")
        case Smt2Query.Result.Kind.Unknown => error(s"Could not deduce the claim of proof step #${step.no.value}")
        case Smt2Query.Result.Kind.Timeout => error(s"Time out when deducing the claim of proof step #${step.no.value}")
        case Smt2Query.Result.Kind.Error => error(s"Error occurred when deducing the claim of proof step #${step.no.value}")
      }
    } else {
      F
    }
    return Plugin.Result(status, nextFresh, claims)
  }

}

object InceptionPlugin {
  @record class Substitutor(substMap: HashMap[String, AST.Typed],
                            context: QName,
                            paramMap: HashMap[String, AST.Exp]) extends AST.MTransformer {
    override def preTyped(o: AST.Typed): AST.MTransformer.PreResult[AST.Typed] = {
      o match {
        case o: AST.Typed.TypeVar =>
          substMap.get(o.id) match {
            case Some(t) => return AST.MTransformer.PreResult(F, MSome(t))
            case _ =>
          }
        case _ =>
      }
      return super.preTyped(o)
    }

    override def preExpIdent(o: AST.Exp.Ident): AST.MTransformer.PreResult[AST.Exp] = {
      o.attr.resOpt.get match {
        case res: AST.ResolvedInfo.LocalVar if paramMap.contains(res.id) && res.context == context =>
          return AST.MTransformer.PreResult(F, MSome(paramMap.get(res.id).get))
        case _ =>
      }
      return super.preExpIdent(o)
    }
  }
}

@datatype class InceptionPlugin extends Plugin {
  @strictpure def canHandle(just: AST.ProofAst.Step.Justification): B = just.isInstanceOf[AST.ProofAst.Step.Inception]

  def handle(logika: Logika,
             smt2: Smt2,
             log: B,
             logDirOpt: Option[String],
             spcMap: HashSMap[Z, StepProofContext],
             state: State,
             step: AST.ProofAst.Step.Regular,
             reporter: Reporter): Plugin.Result = {
    @strictpure def emptyResult: Plugin.Result = Plugin.Result(F, state.nextFresh, ISZ())
    val just = step.just.asInstanceOf[AST.ProofAst.Step.Inception]
    def handleH(invokeIdent: AST.Exp.Ident, args: ISZ[AST.Exp]): Plugin.Result = {
      val res = invokeIdent.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val mi = logika.th.nameMap.get(res.owner :+ res.id).get.asInstanceOf[Info.Method]
      val posOpt = invokeIdent.posOpt
      val contract: AST.MethodContract.Simple = mi.ast.contract match {
        case c: AST.MethodContract.Simple => c
        case _: AST.MethodContract.Cases =>
          reporter.error(posOpt, Logika.kind, "Could not use method with contract cases")
          return emptyResult
      }
      if (contract.reads.nonEmpty) {
        reporter.error(posOpt, Logika.kind, "Could not use method with non-empty reads clause")
        return emptyResult
      }
      if (contract.modifies.nonEmpty) {
        reporter.error(posOpt, Logika.kind, "Could not use method with non-empty modifies clause")
        return emptyResult
      }

      val smOpt = TypeChecker.unifyFun(Logika.kind, logika.th, posOpt, TypeChecker.TypeRelation.Subtype, res.tpeOpt.get,
        mi.methodType.tpe, reporter)
      val ips = InceptionPlugin.Substitutor(smOpt.get, mi.name,
        HashMap.empty[String, AST.Exp] ++ ops.ISZOps(res.paramNames).zip(args))
      if (just.witnesses.isEmpty) {
        var s0 = state
        var props = ISZ[State.Claim]()
        for (require <- contract.requires) {
          for (sv <- logika.evalExp(Logika.Split.Disabled, smt2, T, s0,
            ips.transformExp(require).getOrElseEager(require), reporter) if s0.status) {
            val (s1, sym) = logika.value2Sym(sv._1, sv._2, posOpt.get)
            props = props :+ State.Claim.Prop(T, sym)
            s0 = s1
          }
        }
        if (!s0.status) {
          return emptyResult
        }
        val r = smt2.valid(log, logDirOpt, "Auto Inception", posOpt.get, s0.claims, State.Claim.And(props), reporter)
        r.kind match {
          case Smt2Query.Result.Kind.Unsat =>
          case Smt2Query.Result.Kind.Sat =>
            reporter.error(posOpt, Logika.kind, st"Cannot not satisfy ${(mi.name, ".")}'s pre-conditions'".render)
            return emptyResult(nextFresh = s0.nextFresh)
          case Smt2Query.Result.Kind.Unknown =>
            reporter.error(posOpt, Logika.kind, st"Could not deduce ${(mi.name, ".")}'s pre-conditions'".render)
            return emptyResult(nextFresh = s0.nextFresh)
          case Smt2Query.Result.Kind.Timeout =>
            reporter.error(posOpt, Logika.kind, st"Time out when deducing ${(mi.name, ".")}'s pre-conditions'".render)
            return emptyResult(nextFresh = s0.nextFresh)
          case Smt2Query.Result.Kind.Error =>
            reporter.error(posOpt, Logika.kind, st"Error occurred when deducing ${(mi.name, ".")}'s pre-conditions'".render)
            return emptyResult(nextFresh = s0.nextFresh)
        }
      } else {
        var witnesses = HashSet.empty[AST.Exp]
        var ok = T
        for (w <- just.witnesses) {
          spcMap.get(w.value) match {
            case Some(spc: StepProofContext.Regular) => witnesses = witnesses + spc.exp
            case Some(_) =>
              reporter.error(w.posOpt, Logika.kind, s"Cannot use compound proof step #${w.value} as an argument for inception")
              ok = F
            case _ =>
              reporter.error(w.posOpt, Logika.kind, s"Could not find proof step #${w.value}")
              ok = F
          }
        }
        if (!ok) {
          return emptyResult
        }
        val requires: ISZ[AST.Exp] =
          for (require <- contract.requires) yield ips.transformExp(require).getOrElseEager(require)
        for (i <- 0 until requires.size) {
          if (!witnesses.contains(requires(i))) {
            val pos = contract.requires(i).posOpt.get
            reporter.error(posOpt, Logika.kind, st"Could not find witness for ${(mi.name, ".")}'s pre-condition at [${pos.beginLine}, ${pos.beginColumn}]".render)
            ok = F
          }
        }
        if (!ok) {
          return emptyResult
        }
      }
      val ensures = HashSet.empty[AST.Exp] ++
        (for (ensure <- contract.ensures) yield ips.transformExp(ensure).getOrElseEager(ensure))
      if (!ensures.contains(step.claim)) {
        reporter.error(step.claim.posOpt, Logika.kind, st"Could not derive claim from ${(mi.name, ".")}'s post-conditions".render)
        return emptyResult
      }
      val (status, nextFresh, claims, claim) = logika.evalRegularStepClaim(smt2, state, step.claim, step.no.posOpt, reporter)
      return Plugin.Result(status, nextFresh, ops.ISZOps(claims).slice(state.claims.size, claims.size) :+ claim)
    }
    just match {
      case just: AST.ProofAst.Step.Justification.Incept => return handleH(just.invokeIdent, just.args)
      case just: AST.ProofAst.Step.Justification.InceptNamed => return handleH(just.invokeIdent, just.args)
      case _: AST.ProofAst.Step.Justification.InceptEta =>
        halt("TODO") // TODO
    }
  }
}

