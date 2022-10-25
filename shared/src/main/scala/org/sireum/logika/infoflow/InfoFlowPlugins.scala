// #Sireum
package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.ast.MethodContract.InfoFlow
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.Util.{checkMethodPost, checkMethodPre, logikaMethod, updateInVarMaps}
import org.sireum.logika.infoflow.InfoFlowContext.{InfoFlowsType, Partition}
import org.sireum.logika.plugin.{MethodPlugin, Plugin, StmtPlugin}
import org.sireum.logika.{Config, Logika, Smt2, State}

@datatype class InfoFlowMethodPlugin extends MethodPlugin {

  def name: String = {
    return "Info Flow Method Plugin"
  }

  @pure def canHandle(th: TypeHierarchy, method: AST.Stmt.Method): B = {
    method.contract match {
      case c: AST.MethodContract.Simple => return c.infoFlows.nonEmpty
      case _ => return F
    }
  }

  def handle(th: TypeHierarchy,
             plugins: ISZ[Plugin],
             method: AST.Stmt.Method,
             caseIndex: Z,
             config: Config,
             smt2: Smt2,
             cache: Smt2.Cache,
             reporter: Reporter): B = {

    val mconfig: Config = if (caseIndex >= 0) config(checkInfeasiblePatternMatch = F) else config

    def checkCase(labelOpt: Option[AST.Exp.LitString], reads: ISZ[AST.Exp.Ref], requires: ISZ[AST.Exp],
                  modifies: ISZ[AST.Exp.Ref], ensures: ISZ[AST.Exp], infoFlowsNode: ISZ[InfoFlow]): Unit = {
      var state = State.create
      labelOpt match {
        case Some(label) if label.value != "" => state = state.addClaim(State.Claim.Label(label.value, label.posOpt.get))
        case _ =>
      }
      val res = method.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val methodPosOpt = method.sig.id.attr.posOpt
      var logika: Logika = {
        val receiverTypeOpt: Option[AST.Typed] = if (res.isInObject) {
          None()
        } else {
          th.typeMap.get(res.owner).get match {
            case ti: TypeInfo.Sig => Some(ti.tpe)
            case ti: TypeInfo.Adt => Some(ti.tpe)
            case _ => halt("Infeasible")
          }
        }
        val p = updateInVarMaps(logikaMethod(th, mconfig, res.owner, method.sig.id.value, receiverTypeOpt, method.sig.paramIdTypes,
          method.sig.returnType.typedOpt.get, methodPosOpt, reads, requires, modifies, ensures,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get), plugins, None(), HashSet.empty), smt2, cache, state, reporter)
        state = p._2
        p._1
      }
      val invs = logika.retrieveInvs(res.owner, res.isInObject)
      state = checkMethodPre(logika, smt2, cache, reporter, state, methodPosOpt, invs, requires)

      val infoFlows: InfoFlowsType = HashSMap.empty[String, InfoFlow] ++ infoFlowsNode.map((m: InfoFlow) => ((m.label.value, m)))
      val stateSyms = InfoFlowUtil.processInfoFlowInAgrees(logika, smt2, cache, reporter, state, infoFlows)
      state = stateSyms._1

      logika = logika(context = logika.context(storage =
        InfoFlowContext.putInfoFlows(infoFlows,
          InfoFlowContext.putInAgreements(stateSyms._2, logika.context.storage))))

      val stmts = method.bodyOpt.get.stmts
      val ss: ISZ[State] = if (method.purity == AST.Purity.StrictPure) {
        halt("Infeasible since contracts cannot be attached to strict pure methods")
      } else {
        logika.evalStmts(Split.Default, smt2, cache, None(), T, state, stmts, reporter)
      }

      val partitionsToCheck: ISZ[Partition] = infoFlows.values.map((m: InfoFlow) => ((m.label.value, m.label.posOpt)))
      val ss2: ISZ[State] = InfoFlowUtil.checkInfoFlowAgreements(infoFlows, stateSyms._2, partitionsToCheck,
        logika, smt2, cache, reporter, ss)

      val ssPost: ISZ[State] = checkMethodPost(logika, smt2, cache, reporter, ss2, methodPosOpt, invs, ensures, mconfig.logPc, mconfig.logRawPc,
        if (stmts.nonEmpty) stmts(stmts.size - 1).posOpt else None())
    }

    method.mcontract match {
      case contract: AST.MethodContract.Simple =>
        checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures, contract.infoFlows)
      case contract: AST.MethodContract.Cases =>
        halt("Infeasible until Cases include InfoFlows")
    }

    return T
  }
}

@datatype class InfoFlowStmtPlugin extends StmtPlugin {

  def name: String = {
    return "Info Flow Statement Plugin"
  }

  def hasInlineAgreementPartitions(stmt: AST.Stmt): B = {
    return getInlineAgreementPartitions(stmt).nonEmpty
  }

  def getInlineAgreementPartitions(stmt: AST.Stmt): Option[ISZ[InfoFlowContext.Partition]] = {
    var ret = ISZ[InfoFlowContext.Partition]()
    stmt match {
      case AST.Stmt.DeduceSequent(just, sequents) if sequents.size == 1 =>
        sequents(0).conclusion match {
          case e: AST.Exp.InlineAgree =>
            return Some(e.partitions.map((m: AST.Exp.LitString) => ((m.value, m.posOpt))))
          case _ =>
        }
      case _ =>
    }
    return None()
  }

  @pure def canHandle(logika: Logika, stmt: AST.Stmt): B = {
    return InfoFlowContext.getInfoFlows(logika.context.storage).nonEmpty &&
      InfoFlowContext.getInAgreements(logika.context.storage).nonEmpty &&
      hasInlineAgreementPartitions(stmt)
  }

  def handle(logika: Logika,
             smt2: Smt2,
             cache: Smt2.Cache,
             state: State,
             stmt: AST.Stmt,
             reporter: Reporter): ISZ[State] = {
    val infoFlows = InfoFlowContext.getInfoFlows(logika.context.storage).get
    val inAgrees = InfoFlowContext.getInAgreements(logika.context.storage).get
    var inlinePartitions = getInlineAgreementPartitions(stmt).get

    if (inlinePartitions.isEmpty) {
      val deducePos = stmt.posOpt
      inlinePartitions = infoFlows.values.map((m: InfoFlow) => ((m.label.value, deducePos)))
    }

    var states: ISZ[State] = ISZ()
    for (p <- inlinePartitions if !infoFlows.contains(p._1)) {
      reporter.error(p._2, "Inflow", s"'$p' is not a valid partition")
      states = states :+ state(status = F)
    }

    if (!reporter.hasError) {
      states = InfoFlowUtil.checkInfoFlowAgreements(infoFlows, inAgrees, inlinePartitions,
        logika, smt2, cache, reporter, ISZ(state))
    }

    return states
  }
}
