// #Sireum
package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.lang.ast.MethodContract.InfoFlow
import org.sireum.lang.symbol.TypeInfo
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.{Reporter, Split}
import org.sireum.logika.Util.{checkMethodPost, checkMethodPre, logikaMethod, updateInVarMaps}
import org.sireum.logika.plugin.{MethodPlugin, Plugin}
import org.sireum.logika.{Config, Logika, Smt2, State}

@datatype class InfoFlowMethodPlugin extends MethodPlugin {

  override def name: String = {
    return "Info Flow Method Plugin"
  }

  override def canHandle(th: TypeHierarchy, method: AST.Stmt.Method): B = {
    method.contract match {
      case c: AST.MethodContract.Simple => return c.infoFlows.nonEmpty
      case _ => return F
    }
  }

  override def handle(th: TypeHierarchy,
                      plugins: ISZ[Plugin],
                      method: AST.Stmt.Method,
                      caseIndex: Z,
                      config: Config,
                      smt2: Smt2,
                      cache: Smt2.Cache,
                      reporter: Reporter): B = {

    val mconfig: Config = if (caseIndex >= 0) config(checkInfeasiblePatternMatch = F) else config

    def checkCase(labelOpt: Option[AST.Exp.LitString], reads: ISZ[AST.Exp.Ref], requires: ISZ[AST.Exp],
                  modifies: ISZ[AST.Exp.Ref], ensures: ISZ[AST.Exp], infoFlows: ISZ[InfoFlow]): Unit = {
      var state = State.create
      labelOpt match {
        case Some(label) if label.value != "" => state = state.addClaim(State.Claim.Label(label.value, label.posOpt.get))
        case _ =>
      }
      val res = method.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val methodPosOpt = method.sig.id.attr.posOpt
      val logika: Logika = {
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

      val stateSyms = InfoFlowUtil.processInfoFlowInAgrees(logika, smt2, cache, reporter, state, methodPosOpt, infoFlows)
      state = stateSyms._1

      val stmts = method.bodyOpt.get.stmts
      val ss: ISZ[State] = if (method.purity == AST.Purity.StrictPure) {
        val spBody = stmts(0).asInstanceOf[AST.Stmt.Var].initOpt.get
        logika.evalAssignExp(Split.Default, smt2, cache, None(), T, state, spBody, reporter)
      } else {
        logika.evalStmts(Split.Default, smt2, cache, None(), T, state, stmts, reporter)
      }

      val ss2: ISZ[State] = InfoFlowUtil.checkInfoFlowOutAgrees(logika, smt2, cache, reporter, ss, methodPosOpt, infoFlows, stateSyms._2,
        if (stmts.nonEmpty) stmts(stmts.size - 1).posOpt else None())

      val ssPost: ISZ[State] = checkMethodPost(logika, smt2, cache, reporter, ss2, methodPosOpt, invs, ensures, mconfig.logPc, mconfig.logRawPc,
        if (stmts.nonEmpty) stmts(stmts.size - 1).posOpt else None())
    }

    method.mcontract match {
      case contract: AST.MethodContract.Simple =>
        checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures, contract.infoFlows)
      case contract: AST.MethodContract.Cases =>
        halt("Infeasible. Need to refactor Cases to include InfoFlows")
    }

    return T
  }
}
