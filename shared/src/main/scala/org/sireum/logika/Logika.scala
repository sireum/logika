// #Sireum
/*
 Copyright (c) 2020, Robby, Kansas State University
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
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.symbol.Resolver.QName
import org.sireum.lang.{ast => AST}
import org.sireum.message.{Message, Position}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.plugin._
import Util._

object Logika {

  @enum object Split {
    'Default
    'Enabled
    'Disabled
  }

  @msig trait Reporter extends message.Reporter {
    def state(posOpt: Option[Position], s: State): Unit

    def query(pos: Position, time: Z, r: Smt2Query.Result): Unit

    def empty: Reporter

    def combine(other: Reporter): Reporter

    def illFormed(): Unit
  }

  @record class ReporterImpl(var _messages: ISZ[Message]) extends Reporter {
    var _ignore: B = F

    override def state(posOpt: Option[Position], s: State): Unit = {
    }

    override def query(pos: Position, time: Z, r: Smt2Query.Result): Unit = {
    }

    override def illFormed(): Unit = {
    }

    override def empty: Reporter = {
      return ReporterImpl(ISZ())
    }

    override def messages: ISZ[Message] = {
      return _messages
    }

    override def ignore: B = {
      return _ignore
    }

    override def setIgnore(newIgnore: B): Unit = {
      _ignore = newIgnore
    }

    override def setMessages(newMessages: ISZ[Message]): Unit = {
      _messages = newMessages
    }

    override def timing(desc: String, timeInMs: Z): Unit = {}

    override def combine(other: Reporter): Reporter = {
      _messages = _messages ++ other.messages
      return this
    }
  }

  object Reporter {
    def create: Reporter = {
      return ReporterImpl(ISZ())
    }
  }

  object Context {
    @strictpure def empty: Context = Context(ISZ(), None(), ISZ(), None())
  }

  @datatype class Context(typeParams: ISZ[AST.TypeParam],
                          methodOpt: Option[MethodContext],
                          caseLabels: ISZ[AST.Exp.LitString],
                          implicitCheckOpt: Option[String]) {
    @pure def methodName: ISZ[String] = {
      methodOpt match {
        case Some(m) => return m.name
        case _ => return ISZ()
      }
    }
  }

  @datatype class MethodContext(name: ISZ[String],
                                receiverTypeOpt: Option[AST.Typed],
                                sig: AST.MethodSig,
                                reads: ISZ[AST.Exp.Ident],
                                modifies: ISZ[AST.Exp.Ident],
                                objectVarInMap: HashMap[ISZ[String], State.Value.Sym],
                                fieldVarInMap: HashMap[String, State.Value.Sym],
                                localInMap: HashMap[String, State.Value.Sym],
                                posOpt: Option[Position]) {
    def objectVarMap(sm: HashMap[String, AST.Typed]): HashSMap[ISZ[String], AST.Typed] = {
      var r = HashSMap.empty[ISZ[String], AST.Typed]
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var if res.isInObject && !r.contains(res.owner :+ res.id) =>
            val ids = res.owner :+ res.id
            r = r + ids ~> x.typedOpt.get.subst(sm)
          case _ =>
        }
      }
      return r
    }

    def fieldVarMap(sm: HashMap[String, AST.Typed]): HashSMap[String, (AST.Typed, Option[Position])] = {
      var r = HashSMap.empty[String, (AST.Typed, Option[Position])]
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var if !res.isInObject && !r.contains(res.id) =>
            r = r + res.id ~> ((x.typedOpt.get.subst(sm), x.posOpt))
          case _ =>
        }
      }
      return r
    }

    def localMap(sm: HashMap[String, AST.Typed]): HashSMap[String, (ISZ[String], AST.Id, AST.Typed)] = {
      var r = HashSMap.empty[String, (ISZ[String], AST.Id, AST.Typed)]
      for (p <- sig.params) {
        r = r + p.id.value ~> ((name, p.id, p.tipe.typedOpt.get.subst(sm)))
      }
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar if !r.contains(x.id.value) =>
            r = r + x.id.value ~> ((res.context, x.id, x.typedOpt.get.subst(sm)))
          case _ =>
        }
      }
      return r
    }
  }

  @datatype class InvokeMethodInfo(sig: AST.MethodSig,
                                   contract: AST.MethodContract,
                                   res: AST.ResolvedInfo.Method,
                                   strictPureBodyOpt: Option[AST.AssignExp])

  @datatype class ContractCaseResult(isPreOK: B,
                                     state: State,
                                     retVal: State.Value,
                                     requiresClaim: State.Claim.Prop,
                                     messages: ISZ[message.Message]) {
    @strictpure def isOK: B = state.status
  }

  @datatype trait Task {
    def compute(smt2: Smt2, reporter: Reporter): ISZ[Message]
  }

  object Task {

    @record class IndexTypeVarCollector(var s: HashSet[AST.Typed.TypeVar]) extends AST.MTransformer {
      override def postTypedName(o: AST.Typed.Name): MOption[AST.Typed] = {
        if (o.ids == AST.Typed.isName || o.ids == AST.Typed.msName) {
          o.args(0) match {
            case t: AST.Typed.TypeVar => s = s + t
            case _ =>
          }
        }
        return super.postTypedName(o)
      }
    }

    @datatype class Stmts(th: TypeHierarchy, config: Config, stmts: ISZ[AST.Stmt], plugins: ISZ[Plugin]) extends Task {
      override def compute(smt2: Smt2, reporter: Reporter): ISZ[Message] = {
        val logika = Logika(th, config, Context.empty, F, plugins)
        val itvc = IndexTypeVarCollector(HashSet.empty)
        for (stmt <- stmts) {
          itvc.transformStmt(stmt)
        }
        for (tv <- itvc.s.elements) {
          smt2.addTypeVarIndex(tv)
        }
        for (state <- logika.evalStmts(Split.Default, smt2, None(), T, State.create, stmts, reporter) if state.status) {
          if (stmts.nonEmpty) {
            val lastPos = stmts(stmts.size - 1).posOpt.get
            logika.logPc(config.logPc, config.logRawPc, state, reporter, Some(Logika.afterPos(lastPos)))
          }
        }
        return reporter.messages
      }
    }

    @datatype class Method(par: B, th: TypeHierarchy, config: Config, method: AST.Stmt.Method, plugins: ISZ[Plugin]) extends Task {
      override def compute(smt2: Smt2, reporter: Reporter): ISZ[Message] = {
        val itvc = IndexTypeVarCollector(HashSet.empty)
        itvc.transformStmt(method)
        val tvs = itvc.s.elements
        if (!par && tvs.nonEmpty) {
          val csmt2 = smt2
          for (tv <- tvs) {
            csmt2.addTypeVarIndex(tv)
          }
          checkMethod(th, plugins, method, config, csmt2, reporter)
        } else {
          for (tv <- tvs) {
            smt2.addTypeVarIndex(tv)
          }
          checkMethod(th, plugins, method, config, smt2, reporter)
        }
        return reporter.messages
      }
    }

  }

  val kind: String = "Logika"
  val parsingDesc: String = "Parsing"
  val libraryDesc: String = "Library"
  val typeCheckingDesc: String = "Type Checking"
  val verifyingDesc: String = "Verifying"
  val defaultPlugins: ISZ[Plugin] = ISZ(AutoPlugin(), PropNatDedPlugin(), PredNatDedPlugin(), InceptionPlugin())
  val builtInByNameMethods: HashSet[(B, QName, String)] = HashSet ++ ISZ(
    (F, AST.Typed.isName, "size"), (F, AST.Typed.msName, "size")
  )

  def checkStmts(initStmtss: ISZ[ISZ[AST.Stmt]], config: Config, th: TypeHierarchy,
                 smt2f: lang.tipe.TypeHierarchy => Smt2, reporter: Reporter,
                 par: B, plugins: ISZ[Plugin], verifyingStartTime: Z, includeInit: B): Unit = {
    var tasks = ISZ[Task]()
    if (includeInit) {
      for (initStmts <- initStmtss) {
        tasks = tasks :+ Task.Stmts(th, config, initStmts, plugins)
      }
    }
    var spMethodTasks = ISZ[Task.Method]()

    def rec(stmts: ISZ[AST.Stmt]): Unit = {
      for (stmt <- stmts) {
        stmt match {
          case stmt: AST.Stmt.Method if stmt.bodyOpt.nonEmpty =>
            if (stmt.purity == AST.Purity.StrictPure && stmt.sig.typeParams.isEmpty) {
              spMethodTasks = spMethodTasks :+ Task.Method(par, th, config, stmt, plugins)
            } else {
              tasks = tasks :+ Task.Method(par, th, config, stmt, plugins)
            }
          case stmt: AST.Stmt.Object => rec(stmt.stmts)
          case stmt: AST.Stmt.Adt => rec(stmt.stmts)
          case stmt: AST.Stmt.Sig => rec(stmt.stmts)
          case _ =>
        }
      }
    }

    for (initStmts <- initStmtss) {
      rec(initStmts)
    }

    val smt2 = smt2f(th)

    def combine(r1: Reporter, r2: Reporter): Reporter = {
      val r = r1.combine(r2)
      return r
    }

    @pure def compute(task: Task): Reporter = {
      val r = reporter.empty
      val csmt2 = smt2
      task.compute(csmt2, r)
      return r
    }

    for (task <- spMethodTasks) {
      extension.Cancel.cancellable(() => task.compute(smt2, reporter))
    }

    if (par) {
      combine(reporter, ops.ISZOps(tasks).mParMapFoldLeft[Reporter, Reporter](compute _, combine _, reporter.empty))
    } else {
      for (task <- tasks) {
        extension.Cancel.cancellable(() => task.compute(smt2, reporter))
      }
    }
    reporter.timing(verifyingDesc, extension.Time.currentMillis - verifyingStartTime)
  }

  def checkFile(fileUriOpt: Option[String], input: String, config: Config,
                smt2f: lang.tipe.TypeHierarchy => Smt2, reporter: Reporter,
                par: B, hasLogika: B, plugins: ISZ[Plugin]): Unit = {
    val parsingStartTime = extension.Time.currentMillis
    val isWorksheet: B = fileUriOpt match {
      case Some(p) => !ops.StringOps(p).endsWith(".scala") && !ops.StringOps(p).endsWith(".slang")
      case _ => T
    }

    def checkFileH(): Unit = {
      val topUnitOpt = lang.parser.Parser(input).parseTopUnit[AST.TopUnit](
        isWorksheet = isWorksheet, isDiet = F, fileUriOpt = fileUriOpt, reporter = reporter)
      val libraryStartTime = extension.Time.currentMillis
      reporter.timing(parsingDesc, libraryStartTime - parsingStartTime)
      if (reporter.hasError) {
        reporter.illFormed()
        return
      }
      topUnitOpt match {
        case Some(program: AST.TopUnit.Program) =>
          if (!isWorksheet) {
            return
          }
          val (tc, rep) = extension.Cancel.cancellable(() =>
            lang.FrontEnd.checkedLibraryReporter)
          val typeCheckingStartTime = extension.Time.currentMillis
          reporter.timing(libraryDesc, typeCheckingStartTime - libraryStartTime)
          reporter.reports(rep.messages)
          val (th, p) = extension.Cancel.cancellable(() =>
            lang.FrontEnd.checkWorksheet(par, Some(tc.typeHierarchy), program, reporter))
          if (!reporter.hasError) {
            lang.tipe.PostTipeAttrChecker.checkProgram(p, reporter)
          }
          val verifyingStartTime = extension.Time.currentMillis
          reporter.timing(typeCheckingDesc, verifyingStartTime - typeCheckingStartTime)

          if (!reporter.hasError) {
            if (hasLogika) {
              checkStmts(ISZ(p.body.stmts), config, th, smt2f, reporter, par, plugins, verifyingStartTime, T)
            }
          } else {
            reporter.illFormed()
          }
        case _ =>
      }
    }

    extension.Cancel.cancellable(checkFileH _)
  }

  def checkPrograms(sources: ISZ[(Option[String], String)], files: ISZ[String], config: Config,
                    th: TypeHierarchy, smt2f: lang.tipe.TypeHierarchy => Smt2, reporter: Reporter,
                    par: B, strictAliasing: B, sanityCheck: B, plugins: ISZ[Plugin]): Unit = {
    val parsingStartTime = extension.Time.currentMillis
    val (rep, _, nameMap, typeMap) = extension.Cancel.cancellable(() =>
      lang.FrontEnd.parseProgramAndGloballyResolve(par, sources, th.nameMap, th.typeMap))
    reporter.reports(rep.messages)
    val typeCheckingStartTime = extension.Time.currentMillis
    reporter.timing(parsingDesc, typeCheckingStartTime - parsingStartTime)
    if (reporter.hasError) {
      reporter.illFormed()
      return
    }
    val th2 = extension.Cancel.cancellable(() =>
      TypeHierarchy.build(th(nameMap = nameMap, typeMap = typeMap), reporter))
    if (reporter.hasError) {
      reporter.illFormed()
      return
    }
    val th3 = extension.Cancel.cancellable(() =>
      lang.tipe.TypeOutliner.checkOutline(par, strictAliasing, th2, reporter))
    if (reporter.hasError) {
      reporter.illFormed()
      return
    }
    val fileSet: HashSet[String] = HashSet ++ files
    @pure def shouldCheck(posOpt: Option[Position]): B = {
      posOpt match {
        case Some(pos) => pos.uriOpt match {
          case Some(uri) => return fileSet.contains(uri)
          case _ =>
        }
        case _ =>
      }
      return F
    }
    @pure def filterNameMap(map: lang.symbol.Resolver.NameMap): lang.symbol.Resolver.NameMap = {
      var r = HashMap.empty[QName, Info]
      for (info <- map.values) {
        info match {
          case info: Info.Object if shouldCheck(info.posOpt) => r = r + info.name ~> info
          case _ =>
        }
      }
      return r
    }
    @pure def filterTypeMap(map: lang.symbol.Resolver.TypeMap): lang.symbol.Resolver.TypeMap = {
      var r = HashMap.empty[QName, TypeInfo]
      for (info <- map.values) {
        info match {
          case info: TypeInfo.Adt if shouldCheck(info.posOpt) => r = r + info.name ~> info
          case info: TypeInfo.Sig if shouldCheck(info.posOpt) => r = r + info.name ~> info
          case _ =>
        }
      }
      return r
    }
    val th4 = extension.Cancel.cancellable(() =>
      TypeChecker.checkComponents(par, strictAliasing, th3, filterNameMap(th3.nameMap), filterTypeMap(th3.typeMap), reporter))
    if (reporter.hasError) {
      reporter.illFormed()
      return
    }
    if (sanityCheck) {
      extension.Cancel.cancellable(() =>
        lang.tipe.PostTipeAttrChecker.checkNameTypeMaps(filterNameMap(th4.nameMap), filterTypeMap(th4.typeMap), reporter))
      if (reporter.hasError) {
        reporter.illFormed()
        return
      }
    }
    val verifyingStartTime = extension.Time.currentMillis
    reporter.timing(typeCheckingDesc, verifyingStartTime - typeCheckingStartTime)

    var initStmtss = ISZ[ISZ[AST.Stmt]]()
    for (info <- th4.nameMap.values) {
      info match {
        case info: Info.Object if shouldCheck(info.posOpt) => initStmtss = initStmtss :+ info.ast.stmts
        case _ =>
      }
    }
    for (info <- th4.typeMap.values) {
      info match {
        case info: TypeInfo.Adt if shouldCheck(info.posOpt) => initStmtss = initStmtss :+ info.ast.stmts
        case info: TypeInfo.Sig if shouldCheck(info.posOpt) => initStmtss = initStmtss :+ info.ast.stmts
        case _ =>
      }
    }
    checkStmts(initStmtss, config, th4, smt2f, reporter, par, plugins, verifyingStartTime, F)
  }

  def logikaMethod(th: TypeHierarchy, config: Config, name: ISZ[String], inPfc: B, receiverTypeOpt: Option[AST.Typed],
                   sig: AST.MethodSig, posOpt: Option[Position], reads: ISZ[AST.Exp.Ident], modifies: ISZ[AST.Exp.Ident],
                   caseLabels: ISZ[AST.Exp.LitString], plugins: ISZ[Plugin]): Logika = {
    val mctx = MethodContext(name, receiverTypeOpt, sig, reads, modifies, HashMap.empty, HashMap.empty, HashMap.empty, posOpt)
    val ctx = Context.empty(methodOpt = Some(mctx), caseLabels = caseLabels)
    return Logika(th, config, ctx, inPfc, plugins)
  }

  def checkInv(isPre: B, state: State, logika: Logika, smt2: Smt2, invs: ISZ[lang.symbol.Info.Inv], posOpt: Option[Position], reporter: Reporter): State = {
    var s0 = state
    for (inv <- invs) {
      var i = 0
      val id = inv.ast.id.value
      val isSingle = inv.ast.claims.size == 1
      val methodName: String =
        if (logika.context.methodName.size == 1) logika.context.methodName(0)
        else if (logika.context.methodOpt.get.receiverTypeOpt.isEmpty) st"${(logika.context.methodName, ".")}".render
        else st"${(ops.ISZOps(logika.context.methodName).dropRight(1), ".")}#${logika.context.methodName(0)}".render
      if (isPre) {
        for (claim <- inv.ast.claims if s0.status) {
          val title: String =
            if (isSingle) s"Method $methodName pre-invariant $id"
            else s"Method $methodName pre-invariant $id#$i"
          s0 = logika(context = logika.context(implicitCheckOpt = Some(s"$title: "))).evalAssume(smt2, T, title, s0,
            claim, posOpt, reporter)._1
          i = i + 1
        }
      } else {
        for (claim <- inv.ast.claims if s0.status) {
          val title: String =
            if (isSingle) s"Method $methodName post-invariant $id"
            else s"Method $methodName post-invariant $id#$i"
          s0 = logika(context = logika.context(implicitCheckOpt = Some(s"$title: "))).evalAssert(smt2, T, title, s0,
            claim, posOpt, reporter)._1
          i = i + 1
        }
      }
    }
    val s0Ops = ops.ISZOps(s0.claims)
    return s0(claims = s0Ops.slice(0, state.claims.size) :+ State.Claim.And(
      s0Ops.slice(state.claims.size, s0.claims.size)
    ))
  }

  def checkMethod(th: TypeHierarchy,
                  plugins: ISZ[Plugin],
                  method: AST.Stmt.Method,
                  config: Config,
                  smt2: Smt2,
                  reporter: Reporter): Unit = {
    def checkCase(labelOpt: Option[AST.Exp.LitString], reads: ISZ[AST.Exp.Ident], requires: ISZ[AST.Exp],
                  modifies: ISZ[AST.Exp.Ident], ensures: ISZ[AST.Exp]): Unit = {
      var state = State.create
      labelOpt match {
        case Some(label) if label.value != "" => state = state.addClaim(State.Claim.Label(label.value, label.posOpt.get))
        case _ =>
      }
      val res = method.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val logika: Logika = {
        val mname = res.owner :+ method.sig.id.value
        val receiverTypeOpt: Option[AST.Typed] = if (res.isInObject) {
          None()
        } else {
          th.typeMap.get(res.owner).get match {
            case ti: TypeInfo.Sig => Some(ti.tpe)
            case ti: TypeInfo.Adt => Some(ti.tpe)
            case _ => halt("Infeasible")
          }
        }
        val l = logikaMethod(th, config, mname, F, receiverTypeOpt, method.sig, method.posOpt, reads, modifies,
          if (labelOpt.isEmpty) ISZ() else ISZ(labelOpt.get), plugins)
        val mctx = l.context.methodOpt.get
        var objectVarInMap = mctx.objectVarInMap
        for (p <- mctx.objectVarMap(TypeChecker.emptySubstMap).entries) {
          val (ids, t) = p
          val posOpt = th.nameMap.get(ids).get.posOpt
          val (s, sym) = nameIntro(posOpt.get, state, ids, t, posOpt)
          objectVarInMap = objectVarInMap + ids ~> sym
          state = s
        }
        var fieldVarInMap = mctx.fieldVarInMap
        mctx.receiverTypeOpt match {
          case Some(receiverType) =>
            val (s0, thiz) = idIntro(method.posOpt.get, state, mname, "this", receiverType, method.sig.id.attr.posOpt)
            state = s0
            for (p <- mctx.fieldVarMap(TypeChecker.emptySubstMap).entries) {
              val (id, (t, posOpt)) = p
              val (s1, sym) = state.freshSym(t, posOpt.get)
              state = s1.addClaim(State.Claim.Let.FieldLookup(sym, thiz, id))
              fieldVarInMap = fieldVarInMap + id ~> sym
            }
          case _ =>
        }
        var localInMap = mctx.localInMap
        for (v <- mctx.localMap(TypeChecker.emptySubstMap).values) {
          val (mname, id, t) = v
          val posOpt = id.attr.posOpt
          val (s, sym) = idIntro(posOpt.get, state, mname, id.value, t, posOpt)
          localInMap = localInMap + id.value ~> sym
          state = s
        }
        l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
          localInMap = localInMap))))
      }
      val statePreReqInvSize = state.claims.size
      if (logika.context.methodName.size == 1 && !method.isHelper) {
        state = checkInv(T, state, logika, smt2, th.worksheetInvs, method.posOpt, reporter)
      }
      val stmts = method.bodyOpt.get.stmts
      if (method.purity == AST.Purity.StrictPure) {
        logika.logPc(config.logPc, config.logRawPc, state, reporter, stmts(0).posOpt)
        val imi = InvokeMethodInfo(method.sig, method.contract, res, stmts(0).asInstanceOf[AST.Stmt.Var].initOpt)
        state = logika.strictPureMethod(smt2, state, imi, HashMap.empty, reporter)._1
        for (c <- state.claims; t <- c.types) {
          smt2.addType(t, reporter)
        }
      } else {
        val hasPreReqInv = state.claims.size != statePreReqInvSize
        val statePreReqSize = state.claims.size
        for (r <- requires if state.status) {
          state = logika.evalAssume(smt2, T, "Precondition", state, r, r.posOpt, reporter)._1
        }
        if (state.claims.size != statePreReqSize) {
          val stateOps = ops.ISZOps(state.claims)
          state = state(claims = stateOps.slice(0, statePreReqSize) :+ State.Claim.And(
            stateOps.slice(statePreReqSize, state.claims.size)
          ))
        }
        if (hasPreReqInv && state.claims.size != statePreReqSize) {
          val stateOps = ops.ISZOps(state.claims)
          state = state(claims = stateOps.slice(0, statePreReqInvSize) :+ State.Claim.And(
            stateOps.slice(statePreReqInvSize, state.claims.size)
          ))
        }
        for (s <- logika.evalStmts(Split.Default, smt2, None(), T, state, stmts, reporter)) {
          var s2 = s
          val statePreEnInvSize = state.claims.size
          if (logika.context.methodName.size == 1 && !method.isHelper) {
            s2 = checkInv(F, s2, logika, smt2, th.worksheetInvs, method.posOpt, reporter)
          }
          val hasPreEnInv = state.claims.size != statePreEnInvSize
          val statePreEnSize = state.claims.size
          for (e <- ensures if s2.status) {
            s2 = logika.evalAssert(smt2, T, "Postcondition", s2, e, e.posOpt, reporter)._1
          }
          if (state.claims.size != statePreEnSize) {
            val stateOps = ops.ISZOps(state.claims)
            state = state(claims = stateOps.slice(0, statePreEnSize) :+ State.Claim.And(
              stateOps.slice(statePreEnSize, state.claims.size)
            ))
          }
          if (hasPreEnInv && state.claims.size != statePreEnSize) {
            val stateOps = ops.ISZOps(state.claims)
            state = state(claims = stateOps.slice(0, statePreEnInvSize) :+ State.Claim.And(
              stateOps.slice(statePreEnInvSize, state.claims.size)
            ))
          }
          if (stmts.nonEmpty && s2.status) {
            logika.logPc(config.logPc, config.logRawPc, s2, reporter,
              Some(Logika.afterPos(stmts(stmts.size - 1).posOpt.get)))
          }
        }
      }
    }

    method.contract match {
      case contract: AST.MethodContract.Simple =>
        checkCase(None(), contract.reads, contract.requires, contract.modifies, contract.ensures)
      case contract: AST.MethodContract.Cases =>
        for (c <- contract.cases) {
          checkCase(if (c.label.value === "") None() else Some(c.label), contract.reads, c.requires, contract.modifies, c.ensures)
        }
    }
  }

  @pure def idIntro(pos: Position, state: State, idContext: ISZ[String],
                    id: String, t: AST.Typed, idPosOpt: Option[Position]): (State, State.Value.Sym) = {
    val (s0, sym) = state.freshSym(t, pos)
    return (s0.addClaim(State.Claim.Let.CurrentId(F, sym, idContext, id, idPosOpt)), sym)
  }

  @pure def nameIntro(pos: Position, state: State, ids: ISZ[String], t: AST.Typed,
                      namePosOpt: Option[Position]): (State, State.Value.Sym) = {
    val (s0, sym) = state.freshSym(t, pos)
    return (s0.addClaim(State.Claim.Let.CurrentName(sym, ids, namePosOpt)), sym)
  }

  @pure def resIntro(pos: Position, state: State, context: ISZ[String], t: AST.Typed,
                     posOpt: Option[Position]): (State, State.Value.Sym) = {
    return idIntro(pos, state, context, "Res", t, posOpt)
  }

  def collectLocalPoss(s0: State, lcontext: ISZ[String], id: String): ISZ[Position] = {
    return StateTransformer(CurrentIdPossCollector(lcontext, id)).transformState(Set.empty, s0).ctx.elements
  }

  def rewriteLocal(th: TypeHierarchy, s0: State, addNewSym: B, lcontext: ISZ[String], id: String, posOpt: Option[Position],
                   reporter: Reporter): State = {
    val poss = collectLocalPoss(s0, lcontext, id)
    if (poss.isEmpty) {
      reporter.error(posOpt, kind, s"Missing Modifies clause for $id")
      return s0(status = F)
    }
    val (s1, num) = s0.fresh
    val locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z, B)] + (lcontext, id) ~> ((poss, num, addNewSym))
    val r = StateTransformer(CurrentIdRewriter(th, posOpt, s1.nextFresh, locals)).transformState(ISZ(), s1)
    val s2 = r.resultOpt.get
    return s2(nextFresh = s2.nextFresh + r.ctx.size, claims = s2.claims ++ r.ctx)
  }

  def rewriteLocals(th: TypeHierarchy, s0: State, lcontext: ISZ[String], ids: ISZ[String]): (State, ISZ[State.Claim]) = {
    if (ids.isEmpty) {
      return (s0, ISZ())
    }
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z, B)]
    var s1 = s0
    for (id <- ids) {
      val poss = collectLocalPoss(s0, lcontext, id)
      if (poss.nonEmpty) {
        val (s2, num) = s1.fresh
        locals = locals + (lcontext, id) ~> ((poss, num, F))
        s1 = s2
      }
    }
    val r = StateTransformer(CurrentIdRewriter(th, None(), s1.nextFresh, locals)).transformState(ISZ(), s1)
    return (r.resultOpt.getOrElse(s1), r.ctx)
  }

  def rewriteLocalVars(th: TypeHierarchy, introSym: B, state: State, localVars: ISZ[AST.ResolvedInfo.LocalVar], posOpt: Option[Position], reporter: Reporter): State = {
    if (localVars.isEmpty) {
      return state
    }
    var current = state
    var locals = HashMap.empty[(ISZ[String], String), (ISZ[Position], Z, B)]
    for (l <- localVars) {
      val poss = StateTransformer(CurrentIdPossCollector(l.context, l.id)).
        transformState(Set.empty, current).ctx.elements
      if (poss.isEmpty) {
        reporter.error(posOpt, kind, s"Missing Modifies clause for ${l.id}")
        return state(status = F)
      }
      val (s1, num) = current.fresh
      current = s1
      locals = locals + (l.context, l.id) ~> ((poss, num, introSym))
    }
    val r = StateTransformer(CurrentIdRewriter(th, posOpt, current.nextFresh, locals)).transformState(ISZ(), current)
    current = r.resultOpt.get
    return current(nextFresh = current.nextFresh + r.ctx.size, claims = current.claims ++ r.ctx)
  }

  def rewriteObjectVars(th: TypeHierarchy, state: State, objectVars: HashSMap[AST.ResolvedInfo.Var, (AST.Typed, Position)],
                        pos: Position, reporter: Reporter): State = {
    if (objectVars.isEmpty) {
      return state
    }
    var current = state
    var vars = HashMap.empty[ISZ[String], (ISZ[Position], Z)]
    for (l <- objectVars.keys) {
      val ids = l.owner :+ l.id
      val poss = StateTransformer(CurrentNamePossCollector(ids)).
        transformState(ISZ(), current).ctx
      if (poss.isEmpty) {
        reporter.error(Some(pos), kind, s"Missing Modifies clause for ${(l.owner, ".")}.${l.id}")
        return state(status = F)
      }
      val (s1, num) = current.fresh
      current = s1
      vars = vars + ids ~> ((poss, num))
    }
    val rt = StateTransformer(CurrentNameRewriter(vars)).transformState(HashMap.empty, current)
    current = rt.resultOpt.get
    for (p <- objectVars.entries) {
      val (x, (t, namePos)) = p
      val name =  x.owner :+ x.id
      val (s2, sym) = nameIntro(pos, current, name, t, Some(namePos))
      current = s2
      val tipe = sym.tipe
      if (!th.isMutable(tipe, T)) {
        val (s3, cond) = current.freshSym(AST.Typed.b, pos)
        current = s3.addClaims(ISZ(State.Claim.Let.Binary(cond, sym, AST.Exp.BinaryOp.Eq, rt.ctx.get(name).get, tipe),
          State.Claim.Prop(T, cond)))
      } else if (AST.Util.isSeq(tipe)) {
        val (s3, size1) = current.freshSym(AST.Typed.z, pos)
        val (s4, size2) = s3.freshSym(AST.Typed.z, pos)
        val (s5, cond) = s4.freshSym(AST.Typed.b, pos)
        val o1 = rt.ctx.get(name).get
        current = s5.addClaims(ISZ(
          State.Claim.Let.FieldLookup(size1, o1, "size"),
          State.Claim.Let.FieldLookup(size2, sym, "size"),
          State.Claim.Let.Binary(cond, size2, AST.Exp.BinaryOp.Eq, size1, AST.Typed.z),
          State.Claim.Prop(T, cond)
        ))
      }
    }
    return current
  }

  def conjunctClaimSuffix(s0: State, s1: State): State = {
    if (s1.claims.size - s0.claims.size <= 1) {
      assert(s1.claims.size - s0.claims.size >= 0)
      return s1
    }
    val size1 = s0.claims.size
    val size2 = s1.claims.size
    val claimsOps = ops.ISZOps(s1.claims)
    return s1(claims = claimsOps.slice(0, size1) :+ State.Claim.And(claimsOps.slice(size1, size2)))
  }

  def constructAssume(cond: AST.Exp, posOpt: Option[Position]): AST.Stmt = {
    val assumeResAttr = AST.ResolvedAttr(
      posOpt = posOpt,
      resOpt = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.Assume)),
      typedOpt = Some(AST.Typed.Fun(F, F, ISZ(AST.Typed.b), AST.Typed.unit))
    )
    AST.Stmt.Expr(AST.Exp.Invoke(
      None(), AST.Exp.Ident(AST.Id("assume", AST.Attr(posOpt)), assumeResAttr), ISZ(), ISZ(cond),
      AST.ResolvedAttr(assumeResAttr.posOpt, assumeResAttr.resOpt, AST.Typed.unitOpt)
    ), AST.TypedAttr(posOpt, AST.Typed.unitOpt))
  }

  @strictpure def afterPos(pos: Position): Position = message.FlatPos(pos.uriOpt,
    conversions.Z.toU32(pos.endLine + 1),
    conversions.Z.toU32(1),
    conversions.Z.toU32(pos.endLine + 1),
    conversions.Z.toU32(2),
    conversions.Z.toU32(pos.offset),
    conversions.Z.toU32(1))
}

import Logika.Reporter
import Logika.Split

@datatype class Logika(th: lang.tipe.TypeHierarchy,
                       config: Config,
                       context: Logika.Context,
                       inPfc: B,
                       plugins: ISZ[Plugin]) {

  @pure def isBasic(smt2: Smt2, t: AST.Typed): B = {
    if (Smt2.basicTypes.contains(t)) {
      return T
    }
    t match {
      case t: AST.Typed.Name =>
        smt2.typeHierarchy.typeMap.get(t.ids) match {
          case Some(_: TypeInfo.SubZ) => return T
          case _ => return F
        }
      case _ => return F
    }
    return T
  }

  def zero(tipe: AST.Typed.Name, pos: Position): State.Value = {
    if (tipe == AST.Typed.z) {
      return State.Value.Z(0, pos)
    }
    val ti = th.typeMap.get(tipe.ids).get.asInstanceOf[TypeInfo.SubZ]
    return z2SubZVal(ti, 0, pos)
  }

  def checkSeqIndexing(smt2: Smt2, rtCheck: B, s0: State, seq: State.Value, i: State.Value, posOpt: Option[Position],
                       reporter: Reporter): State = {
    if (!rtCheck) {
      return s0
    }
    val pos = posOpt.get
    val (s1, v) = s0.freshSym(AST.Typed.b, pos)
    val s2 = s1.addClaim(State.Claim.Let.SeqInBound(v, seq, i))
    val claim = State.Claim.Prop(T, v)
    val r = smt2.valid(config.logVc, config.logVcDirOpt, st"${context.implicitCheckOpt}Implicit Indexing Assertion at [${pos.beginLine}, ${pos.beginColumn}]".render,
      pos, s2.claims, claim, reporter)
    r.kind match {
      case Smt2Query.Result.Kind.Unsat => return s0
      case Smt2Query.Result.Kind.Sat => error(Some(pos), st"${context.implicitCheckOpt}Possibly out of bound sequence indexing".render, reporter)
      case Smt2Query.Result.Kind.Unknown => error(Some(pos), st"${context.implicitCheckOpt}Could not deduce that the sequence indexing is in bound".render, reporter)
      case Smt2Query.Result.Kind.Timeout => error(Some(pos), st"${context.implicitCheckOpt}Timed out when deducing that the sequence indexing is in bound".render, reporter)
      case Smt2Query.Result.Kind.Error => error(Some(pos), st"${context.implicitCheckOpt}Error encountered when deducing that the sequence indexing is in bound".render, reporter)
    }
    return s2(status = F)
  }

  def strictPureMethod(smt2: Smt2, state: State, imi: Logika.InvokeMethodInfo, substMap: HashMap[String, AST.Typed],
                       reporter: Reporter): (State, State.ProofFun) = {
    val funType = imi.res.tpeOpt.get.subst(substMap)
    val pf: State.ProofFun = {
      val res = imi.res
      val receiverTypeOpt: Option[AST.Typed] = if (res.isInObject) {
        None()
      } else {
        th.typeMap.get(res.owner).get match {
          case ti: TypeInfo.Sig => Some(ti.tpe.subst(substMap))
          case ti: TypeInfo.Adt => Some(ti.tpe.subst(substMap))
          case _ => halt("Infeasible")
        }
      }
      State.ProofFun(receiverTypeOpt, res.owner, res.id, res.paramNames, funType.args, funType.ret)
    }
    if (smt2.strictPureMethods.contains(pf)) {
      return (state, pf)
    } else {
      smt2.strictPureMethodsUp(smt2.strictPureMethods + pf ~> ((st"", st"")))
      val b = imi.strictPureBodyOpt.get
      val (res, prefix, svs): (State.Value.Sym, Z, ISZ[(State, State.Value)]) = {
        val body: AST.AssignExp = if (substMap.isEmpty) {
          b
        } else {
          AST.Transformer(AST.Util.TypePrePostSubstitutor(substMap)).transformAssignExp(F, b).resultOpt.getOrElse(b)
        }
        val posOpt = body.asStmt.posOpt
        val context = pf.context :+ pf.id
        val logika: Logika = Logika.logikaMethod(th, config, context, T, pf.receiverTypeOpt, imi.sig,
          posOpt, ISZ(), ISZ(), ISZ(), plugins)
        val s0 = state(claims = ISZ())
        val (s1, r) = Logika.idIntro(posOpt.get, s0, context, "Res", funType.ret, posOpt)
        val split: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
        (r, s0.claims.size, logika.evalAssignExpValue(split, smt2, funType.ret, T, s1, body, reporter))
      }

      smt2.addStrictPureMethod(b.asStmt.posOpt.get, pf, svs, res, prefix)

      val s1 = state(nextFresh = maxStateValuesNextFresh(svs))
      if (config.sat) {
        val posOpt = b.asStmt.posOpt
        val title: String = s"the derived proof function of ${imi.res.id}"
        if (!smt2.sat(config.logVc, config.logVcDirOpt, title, posOpt.get, s1.claims, reporter)) {
          reporter.error(posOpt, Logika.kind, "Unsatisfiable proof function derived from @strictpure method")
        }
      }
      return (s1, pf)
    }
  }

  def evalLit(lit: AST.Lit): State.Value = {
    lit match {
      case e: AST.Exp.LitB => return State.Value.B(e.value, e.posOpt.get)
      case e: AST.Exp.LitC => return State.Value.C(e.value, e.posOpt.get)
      case e: AST.Exp.LitF32 => return State.Value.F32(e.value, e.posOpt.get)
      case e: AST.Exp.LitF64 => return State.Value.F64(e.value, e.posOpt.get)
      case e: AST.Exp.LitR => return State.Value.R(e.value, e.posOpt.get)
      case e: AST.Exp.LitString => return State.Value.String(e.value, e.posOpt.get)
      case e: AST.Exp.LitZ => return State.Value.Z(e.value, e.posOpt.get)
    }
  }

  def text2SubZVal(ti: TypeInfo.SubZ, text: String, pos: Position): State.Value = {
    val t = ti.typedOpt.get.asInstanceOf[AST.Typed.Name]
    (ti.ast.isBitVector, ti.ast.bitWidth) match {
      case (T, 8) => return State.Value.S8(S8(text).get, t, pos)
      case (T, 16) => return State.Value.S16(S16(text).get, t, pos)
      case (T, 32) => return State.Value.S32(S32(text).get, t, pos)
      case (T, 64) => return State.Value.S64(S64(text).get, t, pos)
      case (F, 8) => return State.Value.U8(U8(text).get, t, pos)
      case (F, 16) => return State.Value.U16(U16(text).get, t, pos)
      case (F, 32) => return State.Value.U32(U32(text).get, t, pos)
      case (F, 64) => return State.Value.U64(U64(text).get, t, pos)
      case (_, _) => return State.Value.Range(org.sireum.Z(text).get, t, pos)
    }
  }

  def z2SubZVal(ti: TypeInfo.SubZ, n: Z, pos: Position): State.Value = {
    val t = ti.typedOpt.get.asInstanceOf[AST.Typed.Name]
    (ti.ast.isBitVector, ti.ast.bitWidth) match {
      case (T, 8) => return State.Value.S8(conversions.Z.toS8(n), t, pos)
      case (T, 16) => return State.Value.S16(conversions.Z.toS16(n), t, pos)
      case (T, 32) => return State.Value.S32(conversions.Z.toS32(n), t, pos)
      case (T, 64) => return State.Value.S64(conversions.Z.toS64(n), t, pos)
      case (F, 8) => return State.Value.U8(conversions.Z.toU8(n), t, pos)
      case (F, 16) => return State.Value.U16(conversions.Z.toU16(n), t, pos)
      case (F, 32) => return State.Value.U32(conversions.Z.toU32(n), t, pos)
      case (F, 64) => return State.Value.U64(conversions.Z.toU64(n), t, pos)
      case (_, _) => return State.Value.Range(n, t, pos)
    }
  }

  def evalInterpolate(lit: AST.Exp.StringInterpolate): State.Value = {
    lit.prefix match {
      case string"z" => return State.Value.Z(org.sireum.Z(lit.lits(0).value).get, lit.posOpt.get)
      case string"r" => return State.Value.R(org.sireum.R(lit.lits(0).value).get, lit.posOpt.get)
      case string"c" => return State.Value.C(conversions.String.toCis(lit.lits(0).value)(0), lit.posOpt.get)
      case string"f32" => return State.Value.F32(org.sireum.F32(lit.lits(0).value).get, lit.posOpt.get)
      case string"f64" => return State.Value.F64(org.sireum.F64(lit.lits(0).value).get, lit.posOpt.get)
      case _ =>
        val t = lit.typedOpt.get.asInstanceOf[AST.Typed.Name].ids
        th.typeMap.get(t).get match {
          case ti: TypeInfo.SubZ => return text2SubZVal(ti, lit.lits(0).value, lit.posOpt.get)
          case _ =>
        }
        halt(s"TODO: $lit")
    }
  }

  def evalThisIdH(state: State, id: String, t: AST.Typed, pos: Position): (State, State.Value.Sym) = {
    val mc = context.methodOpt.get
    val (s0, receiver) = Logika.idIntro(pos, state, mc.name, "this", mc.receiverTypeOpt.get, None())
    val (s1, r) = s0.freshSym(t, pos)
    return (s1.addClaim(State.Claim.Let.FieldLookup(r, receiver, id)), r)
  }

  def evalExps(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, numOfExps: Z, fe: Z => AST.Exp@pure,
               reporter: Reporter): ISZ[(State, ISZ[State.Value])] = {
    var done = ISZ[(State, ISZ[State.Value])]()
    var currents = ISZ((state, ISZ[State.Value]()))
    for (i <- 0 until numOfExps) {
      val e = fe(i)
      val cs = currents
      currents = ISZ()
      var nextFresh: Z = state.nextFresh
      for (current <- cs) {
        val (s0, vs) = current
        for (p <- evalExp(split, smt2, rtCheck, s0, e, reporter)) {
          val (s1, v) = p
          if (s1.status) {
            currents = currents :+ ((s1, vs :+ v))
            if (nextFresh < s1.nextFresh) {
              nextFresh = s1.nextFresh
            }
          } else {
            done = done :+ ((s1, vs :+ v))
          }
        }
      }
      currents = for (p <- currents) yield (p._1(nextFresh = nextFresh), p._2)
    }
    return currents ++ done
  }

  def evalArgs(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, numOfArgs: Z,
               eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]], reporter: Reporter): ISZ[(State, ISZ[Option[State.Value]])] = {
    eargs match {
      case Either.Left(es) =>
        @strictpure def fe(i: Z): AST.Exp = es(i)

        return for (p <- evalExps(split, smt2, rtCheck, state, es.size, fe _, reporter)) yield
          ((p._1, for (v <- p._2) yield Some(v)))
      case Either.Right(nargs) =>
        @strictpure def feM(i: Z): AST.Exp = nargs(i).arg

        var r = ISZ[(State, ISZ[Option[State.Value]])]()
        for (p <- evalExps(split, smt2, rtCheck, state, nargs.size, feM _, reporter)) {
          val (s0, args) = p
          var m = HashMap.empty[Z, Option[State.Value]]
          for (i <- 0 until args.size) {
            m = m + nargs(i).index ~> Some(args(i))
          }
          r = r :+ ((s0, for (i <- 0 until numOfArgs) yield m.get(i).getOrElse(None())))
        }
        return r
    }
  }

  def evalExp(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, e: AST.Exp, reporter: Reporter): ISZ[(State, State.Value)] = {
    if (!state.status) {
      return ISZ((state, State.errorValue))
    }

    def checkRange(s0: State, value: State.Value, pos: Position): State = {
      val t = value.tipe
      t match {
        case t: AST.Typed.Name =>
          th.typeMap.get(t.ids).get match {
            case ti: TypeInfo.SubZ if !ti.ast.isBitVector =>
              var s1 = s0
              if (ti.ast.hasMin) {
                val (s2, sym) = s1.freshSym(AST.Typed.b, pos)
                val s3 = s2.addClaim(State.Claim.Let.Binary(sym, z2SubZVal(ti, ti.ast.min, pos), AST.Exp.BinaryOp.Le, value, t))
                s1 = evalAssertH(smt2, s"Min range check for $t", s3, sym, e.posOpt, reporter)
              }
              if (s1.status && ti.ast.hasMax) {
                val (s4, sym) = s1.freshSym(AST.Typed.b, pos)
                val s5 = s4.addClaim(State.Claim.Let.Binary(sym, value, AST.Exp.BinaryOp.Le, z2SubZVal(ti, ti.ast.max, pos), t))
                s1 = evalAssertH(smt2, s"Max range check for $t", s5, sym, e.posOpt, reporter)
              }
              return s1
            case _ =>
          }
        case _ =>
      }
      return s0
    }

    def evalIdentH(s0: State, res: AST.ResolvedInfo, t: AST.Typed, pos: Position): (State, State.Value) = {
      res match {
        case AST.ResolvedInfo.Var(T, F, T, AST.Typed.sireumName, id) if id == "T" || id == "F" =>
          return (s0, if (id == "T") State.Value.B(T, pos) else State.Value.B(F, pos))
        case res: AST.ResolvedInfo.LocalVar =>
          val (s1, r) = Logika.idIntro(pos, s0, res.context, res.id, t, None())
          return (s1, r)
        case res: AST.ResolvedInfo.Var =>
          if (res.isInObject) {
            val (s1, r) = Logika.nameIntro(pos, s0, res.owner :+ res.id, t, None())
            return (s1, r)
          } else {
            val (s1, r) = evalThisIdH(s0, res.id, t, pos)
            return (s1, r)
          }
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalIdent(exp: AST.Exp.Ident): ISZ[(State, State.Value)] = {
      val res = exp.attr.resOpt.get
      res match {
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method && res.tpeOpt.get.isByName &&
          !Logika.builtInByNameMethods.contains((res.isInObject, res.owner, res.id)) =>
          val mType = res.tpeOpt.get
          val attr = AST.ResolvedAttr(exp.id.attr.posOpt, exp.attr.resOpt, Some(mType.ret))
          return evalInvoke(state, None(), exp, Either.Left(ISZ()), attr)
        case _ =>
          return ISZ(evalIdentH(state, res, exp.attr.typedOpt.get, exp.posOpt.get))
      }
    }

    def evalUnaryExp(exp: AST.Exp.Unary): ISZ[(State, State.Value)] = {

      val s0 = state

      exp.attr.resOpt.get match {
        case AST.ResolvedInfo.BuiltIn(kind) if isBasic(smt2, exp.typedOpt.get) =>
          def evalUnaryExpH(p: (State, State.Value)): (State, State.Value) = {
            val (s1, v) = p
            if (!s1.status) {
              return (s1, State.errorValue)
            }
            kind match {
              case AST.ResolvedInfo.BuiltIn.Kind.UnaryPlus => return (s1, v)
              case _ =>
                val pos = exp.posOpt.get
                val (s2, sym) = s1.freshSym(v.tipe, pos)
                val s3 = s2(claims = s2.claims :+ State.Claim.Let.Unary(sym, exp.opString, v))
                return (checkRange(s3, sym, pos), sym)
            }
          }

          return for (p <- evalExp(split, smt2, rtCheck, s0, exp.exp, reporter)) yield evalUnaryExpH(p)
        case _ =>
          halt(s"TODO: $exp") // TODO
      }
    }

    def evalBinaryExp(exp: AST.Exp.Binary): ISZ[(State, State.Value)] = {
      @pure def isCond(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
          case _ => return F
        }
        return T
      }

      @pure def isSeq(m: AST.ResolvedInfo.Method): B = {
        m.id match {
          case AST.Exp.BinaryOp.Append =>
          case AST.Exp.BinaryOp.AppendAll =>
          case AST.Exp.BinaryOp.Prepend =>
          case AST.Exp.BinaryOp.RemoveAll => halt(s"TODO: $m")
          case _ => return F
        }
        return m.owner == AST.Typed.isName || m.owner == AST.Typed.msName
      }

      @pure def reqNonZeroCheck(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): B = {
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryDiv =>
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryRem =>
          case _ => return F
        }
        return rtCheck
      }

      def checkNonZero(s0: State, op: String, value: State.Value, pos: Position): State = {
        val (s1, sym) = s0.freshSym(AST.Typed.b, pos)
        val tipe = value.tipe.asInstanceOf[AST.Typed.Name]
        val claim = State.Claim.Let.Binary(sym, value, AST.Exp.BinaryOp.Ne, zero(tipe, pos), tipe)
        val r = smt2.valid(config.logVc, config.logVcDirOpt,
          st"${context.implicitCheckOpt}Non-zero second operand of '$op' at [${pos.beginLine}, ${pos.beginColumn}]".render,
          pos, s0.claims :+ claim, State.Claim.Prop(T, sym), reporter)
        r.kind match {
          case Smt2Query.Result.Kind.Unsat => return s1.addClaim(claim)
          case Smt2Query.Result.Kind.Sat => error(Some(pos), st"${context.implicitCheckOpt}Possibly zero second operand for ${exp.op}".render, reporter)
          case Smt2Query.Result.Kind.Unknown => error(Some(pos), st"${context.implicitCheckOpt}Could not deduce non-zero second operand for ${exp.op}".render, reporter)
          case Smt2Query.Result.Kind.Timeout => error(Some(pos), st"${context.implicitCheckOpt}Timed out when deducing non-zero second operand for ${exp.op}".render, reporter)
          case Smt2Query.Result.Kind.Error => error(Some(pos), st"${context.implicitCheckOpt}Error encountered when deducing non-zero second operand for ${exp.op}".render, reporter)
        }
        return s1(status = F)
      }

      def evalBasic(s0: State, kind: AST.ResolvedInfo.BuiltIn.Kind.Type, v1: State.Value): ISZ[(State, State.Value)] = {
        def evalBasicH(p: (State, State.Value)): (State, State.Value) = {
          val (s1, v2) = p
          val s2: State = if (reqNonZeroCheck(kind)) {
            checkNonZero(s1, exp.op, v2, exp.right.posOpt.get)
          } else {
            s1
          }
          if (!s2.status) {
            return (s2, State.errorValue)
          }
          val rTipe = e.typedOpt.get
          val pos = e.posOpt.get
          val (s3, rExp) = s2.freshSym(rTipe, pos)
          val s4 = s3.addClaim(State.Claim.Let.Binary(rExp, v1, exp.op, v2, v1.tipe))
          return (checkRange(s4, rExp, pos), rExp)
        }

        return for (p <- evalExp(split, smt2, rtCheck, s0, exp.right, reporter)) yield evalBasicH(p)
      }

      def evalCond(s0: State, kind: AST.ResolvedInfo.BuiltIn.Kind.Type, v1: State.Value.Sym): ISZ[(State, State.Value)] = {
        val pos = exp.left.posOpt.get
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
            val s1 = s0.addClaim(State.Claim.Prop(T, v1))

            def evalCondAndH(p: (State, State.Value)): ISZ[(State, State.Value)] = {
              val (s2, v2) = p
              if (!s2.status) {
                return ISZ((s2, State.errorValue))
              }
              val (s3, r) = s2.freshSym(AST.Typed.b, exp.right.posOpt.get)
              val s4 = s3.addClaim(State.Claim.Let.Ite(r, v1, v2, State.Value.B(F, pos)))
              return ISZ((s4(claims = s0.claims ++ ops.ISZOps(s4.claims).slice(s1.claims.size, s4.claims.size)), r))
            }

            return for (p <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter); r <- evalCondAndH(p)) yield r
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
            val s1 = s0.addClaim(State.Claim.Prop(F, v1))

            def evalCondOrH(p: (State, State.Value)): ISZ[(State, State.Value)] = {
              val (s2, v2) = p
              if (!s2.status) {
                return ISZ((s2, State.errorValue))
              }
              val (s3, r) = s2.freshSym(AST.Typed.b, exp.right.posOpt.get)
              val s4 = s3.addClaim(State.Claim.Let.Ite(r, v1, State.Value.B(T, pos), v2))
              return ISZ((s4(claims = s0.claims ++ ops.ISZOps(s4.claims).slice(s1.claims.size, s4.claims.size)), r))
            }

            return for (p <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter); r <- evalCondOrH(p)) yield r
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
            val s1 = s0.addClaim(State.Claim.Prop(T, v1))

            def evalCondImplyH(p: (State, State.Value)): ISZ[(State, State.Value)] = {
              val (s2, v2) = p
              if (!s2.status) {
                return ISZ((s2, State.errorValue))
              }
              val (s3, r) = s2.freshSym(AST.Typed.b, exp.right.posOpt.get)
              val s4 = s3.addClaim(State.Claim.Let.Ite(r, v1, v2, State.Value.B(T, pos)))
              return ISZ((s4(claims = s0.claims ++ ops.ISZOps(s4.claims).slice(s1.claims.size, s4.claims.size)), r))
            }

            return for (p <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter); r <- evalCondImplyH(p)) yield r
          case _ => halt("Infeasible")
        }
      }

      def evalSeq(s0: State, m: AST.ResolvedInfo.Method): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        for (p1 <- evalExp(split, smt2, rtCheck, s0, exp.left, reporter)) {
          val (s1, v1) = p1
          if (s1.status) {
            for (p2 <- evalExp(split, smt2, rtCheck, s1, exp.right, reporter)) {
              val (s2, v2) = p2
              if (s2.status) {
                val rTipe = e.typedOpt.get
                val (s3, rExp) = s2.freshSym(rTipe, e.posOpt.get)
                val s4 = s3.addClaim(State.Claim.Let.Binary(rExp, v1, exp.op, v2,
                  if (ops.StringOps(m.id).endsWith(":")) v2.tipe else v1.tipe))
                r = r :+ ((s4, rExp))
              } else {
                r = r :+ ((s2, State.errorValue))
              }
            }
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
        return r
      }

      val s0 = state

      exp.attr.resOpt.get match {
        case AST.ResolvedInfo.BuiltIn(kind) =>
          var r = ISZ[(State, State.Value)]()
          for (p <- evalExp(split, smt2, rtCheck, s0, exp.left, reporter)) {
            val (s1, v1) = p
            if (s1.status) {
              if (isCond(kind)) {
                val (s2, left) = value2Sym(s1, v1, exp.left.posOpt.get)
                r = r ++ evalCond(s2, kind, left)
              } else if (exp.op == "==" || exp.op == "!=" || isBasic(smt2, v1.tipe)) {
                r = r ++ evalBasic(s1, kind, v1)
              } else {
                halt(s"TODO: $e") // TODO
              }
            } else {
              r = r :+ ((s1, State.errorValue))
            }
          }
          return r
        case m: AST.ResolvedInfo.Method =>
          if (isSeq(m)) {
            return evalSeq(s0, m)
          }
          val posOpt = exp.posOpt
          return evalInvoke(s0, Some(exp.left), AST.Exp.Ident(AST.Id(exp.op, AST.Attr(posOpt)), exp.attr),
            Either.Left(ISZ(exp.right)), exp.attr)
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalSelectH(sp: Split.Type, res: AST.ResolvedInfo, receiverOpt: Option[AST.Exp], id: String, tipe: AST.Typed,
                    pos: Position): ISZ[(State, State.Value)] = {
      def evalField(t: AST.Typed): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        for (p <- evalExp(sp, smt2, rtCheck, state, receiverOpt.get, reporter)) {
          val (s0, o) = p
          if (s0.status) {
            val (s1, sym) = s0.freshSym(t, pos)
            r = r :+ ((s1.addClaim(State.Claim.Let.FieldLookup(sym, o, id)), sym))
          } else {
            r = r :+ ((s0, State.errorValue))
          }
        }
        return r
      }

      def evalEnumElement(eres: AST.ResolvedInfo.EnumElement): (State, State.Value) = {
        return (state, State.Value.Enum(tipe.asInstanceOf[AST.Typed.Name], eres.owner, eres.name, eres.ordinal, pos))
      }

      def evalTupleLit(tres: AST.ResolvedInfo.Tuple): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        val (s0, sym) = state.freshSym(tipe, pos)
        for (p <- evalExp(split, smt2, rtCheck, s0, receiverOpt.get, reporter)) {
          val (s1, v) = p
          if (s1.status) {
            r = r :+ ((s1.addClaim(State.Claim.Let.FieldLookup(sym, v, s"_${tres.index}")), sym))
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
        return r
      }

      res match {
        case res: AST.ResolvedInfo.Var =>
          assert(!res.isInObject && receiverOpt.nonEmpty)
          return evalField(tipe)
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method && res.tpeOpt.get.isByName =>
          return evalField(res.tpeOpt.get.ret)
        case res: AST.ResolvedInfo.LocalVar => return ISZ(evalIdentH(state, res, tipe, pos))
        case res: AST.ResolvedInfo.EnumElement => return ISZ(evalEnumElement(res))
        case res: AST.ResolvedInfo.Tuple =>
          assert(receiverOpt.nonEmpty)
          return evalTupleLit(res)
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def evalSelect(exp: AST.Exp.Select): ISZ[(State, State.Value)] = {
      val pos = exp.id.attr.posOpt.get
      @pure def random(tpe: AST.Typed): ISZ[(State, State.Value)] = {
        val s0 = state
        val (s1, sym) = s0.freshSym(tpe, pos)
        var s2 = s1.addClaim(State.Claim.Def.Random(sym, pos))
        tpe match {
          case tpe: AST.Typed.Name =>
            th.typeMap.get(tpe.ids).get match {
              case ti: TypeInfo.SubZ =>
                if (ti.ast.hasMin) {
                  val (s3, minCond) = s2.freshSym(tpe, pos)
                  s2 = s3.addClaims(ISZ(State.Claim.Let.Binary(minCond, z2SubZVal(ti, ti.ast.min, pos),
                    AST.Exp.BinaryOp.Le, sym, tpe), State.Claim.Prop(T, minCond)))
                }
                if (ti.ast.hasMax) {
                  val (s4, maxCond) = s2.freshSym(tpe, pos)
                  s2 = s4.addClaims(ISZ(State.Claim.Let.Binary(maxCond, sym, AST.Exp.BinaryOp.Le,
                    z2SubZVal(ti, ti.ast.min, pos), tpe), State.Claim.Prop(T, maxCond)))
                }
              case _ =>
            }
          case _ =>
        }
        return ISZ((s2, sym))
      }
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.BuiltIn if res.kind == AST.ResolvedInfo.BuiltIn.Kind.Random =>
          return random(exp.typedOpt.get)
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Ext && res.owner.size == 3
          && ops.ISZOps(res.owner).dropRight(1) == AST.Typed.sireumName && res.id == "random" =>
          return random(res.tpeOpt.get.ret)
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method && res.tpeOpt.get.isByName &&
          !Logika.builtInByNameMethods.contains((res.isInObject, res.owner, res.id)) =>
          val mType = res.tpeOpt.get
          val attr = AST.ResolvedAttr(exp.id.attr.posOpt, exp.attr.resOpt, Some(mType.ret))
          return evalInvoke(state, exp.receiverOpt, AST.Exp.Ident(exp.id, exp.attr), Either.Left(ISZ()), attr)
        case res => return evalSelectH(split, res, exp.receiverOpt, exp.id.value, exp.typedOpt.get, pos)
      }
    }

    def evalConstructor(sp: Split.Type,
                        isCopy: B,
                        invokeReceiverOpt: Option[AST.Exp],
                        ident: AST.Exp.Ident,
                        eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]],
                        attr: AST.ResolvedAttr): ISZ[(State, State.Value)] = {
      val t = attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
      var r = ISZ[(State, State.Value)]()

      def evalSConstructor(): Unit = {
        val (s0, sym) = state.freshSym(t, attr.posOpt.get)
        for (p <- evalArgs(sp, smt2, rtCheck, s0, -1, eargs, reporter)) {
          val (s1, args) = p
          if (s1.status) {
            val it = t.args(0).asInstanceOf[AST.Typed.Name]
            var indices = ISZ[State.Value]()
            if (it == AST.Typed.z) {
              indices = for (i <- 0 until args.size) yield State.Value.Z(i, args(i).get.pos)
            } else {
              val subz = smt2.typeHierarchy.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ].ast

              @pure def z2subz(n: Z, pos: Position): State.Value = {
                if (subz.isBitVector) {
                  if (subz.bitWidth == 8) {
                    return if (subz.isSigned) State.Value.S8(conversions.Z.toS8(n), it, pos)
                    else State.Value.U8(conversions.Z.toU8(n), it, pos)
                  } else if (subz.bitWidth == 16) {
                    return if (subz.isSigned) State.Value.S16(conversions.Z.toS16(n), it, pos)
                    else State.Value.U16(conversions.Z.toU16(n), it, pos)
                  } else if (subz.bitWidth == 32) {
                    return if (subz.isSigned) State.Value.S32(conversions.Z.toS32(n), it, pos)
                    else State.Value.U32(conversions.Z.toU32(n), it, pos)
                  } else if (subz.bitWidth == 64) {
                    return if (subz.isSigned) State.Value.S64(conversions.Z.toS64(n), it, pos)
                    else State.Value.U64(conversions.Z.toU64(n), it, pos)
                  } else {
                    halt(s"Infeasible bit-width: ${subz.bitWidth}")
                  }
                } else {
                  return State.Value.Range(n, it, pos)
                }
              }

              var i = 0
              var index = subz.index
              while (i < args.size) {
                indices = indices :+ z2subz(index, args(i).get.pos)
                index = index + 1
                i = i + 1
              }
            }
            smt2.addSeqLit(t, indices.size, reporter)
            val as: ISZ[State.Claim.Def.SeqLit.Arg] =
              for (p <- ops.ISZOps(indices).zip(args)) yield State.Claim.Def.SeqLit.Arg(p._1, p._2.get)
            r = r :+ ((s1.addClaim(State.Claim.Def.SeqLit(sym, as)), sym))
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
      }

      def evalAdtConstructor(s0: State, receiverOpt: Option[State.Value]): Unit = {
        val (s1, sym) = s0.freshSym(t, attr.posOpt.get)
        val ti = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
        val params = ti.ast.params
        for (p <- evalArgs(sp, smt2, rtCheck, s1, params.size, eargs, reporter)) {
          val s2 = p._1
          val args = p._2.toMS
          if (s2.status) {
            var s3 = s2
            eargs match {
              case Either.Right(_) =>
                for (i <- 0 until args.size) {
                  if (args(i).isEmpty) {
                    val receiver = receiverOpt.get
                    val param = params(i)
                    val pt = param.tipe.typedOpt.get
                    val (s4, sym) = s3.freshSym(pt, param.id.attr.posOpt.get)
                    s3 = s4.addClaim(State.Claim.Let.FieldLookup(sym, receiver, param.id.value))
                    args(i) = Some(sym)
                  }
                }
              case _ =>
            }
            r = r :+ ((s3.addClaim(State.Claim.Def.AdtLit(sym, args.toIS.map((vOpt: Option[State.Value]) => vOpt.get))), sym))
          } else {
            r = r :+ ((s2, State.errorValue))
          }
        }
      }

      if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
        evalSConstructor()
      } else {
        val stateReceiverOpts: ISZ[(State, Option[State.Value])] = {
          if (isCopy) {
            val receiver: AST.Exp = invokeReceiverOpt match {
              case Some(_) => AST.Exp.Select(invokeReceiverOpt, ident.id, ident.targs, ident.attr)
              case _ => ident
            }
            for (p <- evalExp(split, smt2, rtCheck, state, receiver, reporter)) yield (p._1, Some(p._2))
          } else {
            ISZ((state, None()))
          }
        }
        for (p <- stateReceiverOpts) {
          val (s0, receiverOpt) = p
          evalAdtConstructor(s0, receiverOpt)
        }
      }
      return r
    }

    def evalReceiver(sp: Split.Type, receiverOpt: Option[AST.Exp], ident: AST.Exp.Ident, isInObject: B): ISZ[(State, State.Value)] = {
      receiverOpt match {
        case Some(rcv) =>
          ident.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var =>
              return evalSelectH(sp, res, receiverOpt, ident.id.value, ident.typedOpt.get, ident.posOpt.get)
            case _ => return evalExp(sp, smt2, rtCheck, state, rcv, reporter)
          }
        case _ =>
          if (isInObject) {
            return ISZ()
          } else {
            return ISZ(evalThis(AST.Exp.This(AST.TypedAttr(ident.posOpt, context.methodOpt.get.receiverTypeOpt))))
          }
      }
    }

    def evalSeqSelect(exp: AST.Exp.Invoke): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      val srcv: ISZ[(State, State.Value)] = exp.receiverOpt match {
        case Some(rcv) => evalExp(split, smt2, rtCheck, state, rcv , reporter)
        case _ => evalIdent(exp.ident)
      }
      for (p0 <- srcv; p1 <- evalExp(split, smt2, rtCheck, p0._1, exp.args(0), reporter)) {
        val (_, seq) = p0
        val (s1, i) = p1
        val s2 = checkSeqIndexing(smt2, rtCheck, s1, seq, i, exp.args(0).posOpt, reporter)
        val (s3, v) = s2.freshSym(exp.typedOpt.get, exp.posOpt.get)
        r = r :+ ((s3.addClaim(State.Claim.Let.SeqLookup(v, seq, i)), v))
      }
      return r
    }

    def evalResult(exp: AST.Exp.Result): (State, State.Value) = {
      val (s, sym) = Logika.resIntro(exp.posOpt.get, state, context.methodOpt.get.name, exp.typedOpt.get, None())
      return (s, sym)
    }

    def evalThis(exp: AST.Exp.This): (State, State.Value) = {
      val (s, sym) = Logika.idIntro(exp.posOpt.get, state, context.methodOpt.get.name, "this", exp.typedOpt.get, None())
      return (s, sym)
    }

    def evalInput(input: AST.Exp.Input): (State, State.Value) = {
      input.exp match {
        case exp: AST.Exp.Ident =>
          exp.attr.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              context.methodOpt.get.localInMap.get(res.id) match {
                case Some(sym) => return (state, sym)
                case _ =>
                  error(exp.posOpt, s"Identifier ${exp.id.value} was not declared to be read/modified", reporter)
                  return (state(status = F), State.Value.B(F, e.posOpt.get))
              }
            case res: AST.ResolvedInfo.Var =>
              if (res.isInObject) {
                val ids = res.owner :+ res.id
                context.methodOpt.get.objectVarInMap.get(ids) match {
                  case Some(sym) => return (state, sym)
                  case _ =>
                    error(exp.posOpt, s"Identifier ${exp.id.value} was not declared to be read/modified", reporter)
                    return (state(status = F), State.Value.B(F, e.posOpt.get))
                }
              } else {
                context.methodOpt.get.fieldVarInMap.get(res.id) match {
                  case Some(sym) =>
                    return (state, sym)
                  case _ =>
                    error(exp.posOpt, s"Identifier ${exp.id.value} was not declared to be read/modified", reporter)
                    return (state(status = F), State.Value.B(F, e.posOpt.get))
                }
              }
            case _ => halt(s"Infeasible: $exp")
          }
        case _ => halt("TODO: non-simple input")
      }
    }

    def evalQuantType(quant: AST.Exp.QuantType): (State, State.Value) = {
      var quantClaims = ISZ[State.Claim]()
      val (s0, sym) = state.freshSym(AST.Typed.b, quant.attr.posOpt.get)
      var nextFresh = s0.nextFresh
      val sp: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
      for (p <- this (inPfc = T).evalAssignExpValue(sp, smt2, AST.Typed.b, rtCheck, s0, quant.fun.exp, reporter)) {
        val (s1, v) = p
        val (s2, expSym) = value2Sym(s1, v, quant.fun.exp.asStmt.posOpt.get)
        if (s2.status) {
          quantClaims = quantClaims :+ State.Claim.And(ops.ISZOps(s2.claims).slice(s0.claims.size, s2.claims.size) :+ State.Claim.Prop(T, expSym))
        }
        if (nextFresh < s2.nextFresh) {
          nextFresh = s2.nextFresh
        }
      }
      val vars: ISZ[State.Claim.Let.Quant.Var] =
        for (p <- quant.fun.params) yield State.Claim.Let.Quant.Var.Id(quant.fun.context, p.idOpt.get.value, p.typedOpt.get)
      if (quantClaims.isEmpty) {
        return (s0(status = F), State.errorValue)
      }
      val qcs: ISZ[State.Claim] =
        if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
        else ISZ(State.Claim.And(quantClaims))
      return (s0(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym)
    }

    def evalQuantRange(quant: AST.Exp.QuantRange): ISZ[(State, State.Value)] = {
      val qVarType = quant.attr.typedOpt.get
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val s0 = state
      val sp: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
      var r = ISZ[(State, State.Value)]()
      for (p1 <- evalExp(sp, smt2, rtCheck, s0, quant.lo, reporter);
           p2 <- evalExp(sp, smt2, rtCheck, p1._1, quant.hi, reporter)) {
        val (_, lo) = p1
        val (s2, hi) = p2
        if (s2.status) {
          val (s3, ident) = evalIdentH(s2, quant.attr.resOpt.get, qVarType, quant.fun.params(0).idOpt.get.attr.posOpt.get)
          val (s4, loSym) = s3.freshSym(AST.Typed.b, quant.lo.posOpt.get)
          val s5 = s4.addClaim(State.Claim.Let.Binary(loSym, lo, AST.Exp.BinaryOp.Le, ident, qVarType))
          val loProp = State.Claim.Prop(T, loSym)
          val (s6, hiSym) = s5.freshSym(AST.Typed.b, quant.hi.posOpt.get)
          val hiProp = State.Claim.Prop(T, hiSym)
          val s7 = s6.addClaim(State.Claim.Let.Binary(hiSym, ident,
            if (quant.hiExact) AST.Exp.BinaryOp.Le else AST.Exp.BinaryOp.Lt, hi, qVarType))
          val (s8, sym) = s7.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var.Id(quant.fun.context, qVarRes.id, qVarType))
          var quantClaims = ISZ[State.Claim]()
          var nextFresh: Z = s8.nextFresh
          for (p <- this (inPfc = T).evalAssignExpValue(sp, smt2, AST.Typed.b, rtCheck, s8.addClaims(ISZ(loProp, hiProp)), quant.fun.exp, reporter)) {
            val (s9, v) = p
            val (s10, expSym) = value2Sym(s9, v, quant.fun.exp.asStmt.posOpt.get)
            if (s10.status) {
              val props: ISZ[State.Claim] = ISZ(loProp, hiProp, State.Claim.Prop(T, expSym))
              val s10ClaimsOps = ops.ISZOps(s10.claims)
              val quantClaim = (s10ClaimsOps.slice(s2.claims.size, s8.claims.size) ++ s10ClaimsOps.slice(s8.claims.size + 2, s10.claims.size)) :+
                (if (quant.isForall) State.Claim.Imply(props) else State.Claim.And(props))
              quantClaims = quantClaims :+ State.Claim.And(quantClaim)
            }
            if (nextFresh < s10.nextFresh) {
              nextFresh = s10.nextFresh
            }
          }
          if (quantClaims.isEmpty) {
            r = r :+ ((s2(status = F), State.errorValue))
          } else {
            val qcs: ISZ[State.Claim] =
              if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
              else ISZ(State.Claim.And(quantClaims))
            r = r :+ ((s2(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym))
          }
        } else {
          r = r :+ ((s2, State.errorValue))
        }
      }
      return r
    }

    def evalQuantEachIndex(quant: AST.Exp.QuantEach, seqExp: AST.Exp): ISZ[(State, State.Value)] = {
      val qVarType = quant.attr.typedOpt.get
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val sType: AST.Typed.Name = seqExp.typedOpt.get match {
        case t: AST.Typed.Name => t
        case t: AST.Typed.Method => t.tpe.ret.asInstanceOf[AST.Typed.Name]
        case _ => halt("Infeasible")
      }
      val s0 = state
      val sp: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
      var r = ISZ[(State, State.Value)]()
      for (p1 <- evalExp(sp, smt2, rtCheck, s0, seqExp, reporter)) {
        val (s2, s) = p1
        if (s2.status) {
          val (s3, ident) = evalIdentH(s2, quant.attr.resOpt.get, qVarType, quant.fun.params(0).idOpt.get.attr.posOpt.get)
          val (s4, inBoundSym) = s3.freshSym(AST.Typed.b, seqExp.posOpt.get)
          val s5 = s4.addClaim(State.Claim.Let.SeqInBound(inBoundSym, s, ident))
          val inBoundProp = State.Claim.Prop(T, inBoundSym)
          val (s6, sym) = s5.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var.Id(quant.fun.context, qVarRes.id, qVarType))
          var quantClaims = ISZ[State.Claim]()
          var nextFresh: Z = s6.nextFresh
          for (p <- this (inPfc = T).evalAssignExpValue(sp, smt2, AST.Typed.b, rtCheck, s6.addClaims(ISZ(inBoundProp)), quant.fun.exp, reporter)) {
            val (s7, v) = p
            val (s8, expSym) = value2Sym(s7, v, quant.fun.exp.asStmt.posOpt.get)
            if (s8.status) {
              val props: ISZ[State.Claim] = ISZ(inBoundProp, State.Claim.Prop(T, expSym))
              val s8ClaimsOps = ops.ISZOps(s8.claims)
              val quantClaim = (s8ClaimsOps.slice(s2.claims.size, s6.claims.size) ++ s8ClaimsOps.slice(s6.claims.size + 1, s8.claims.size)) :+
                (if (quant.isForall) State.Claim.Imply(props) else State.Claim.And(props))
              quantClaims = quantClaims :+ State.Claim.And(quantClaim)
            }
            if (nextFresh < s8.nextFresh) {
              nextFresh = s8.nextFresh
            }
          }
          if (quantClaims.isEmpty) {
            r = r :+ ((s2(status = F), State.errorValue))
          } else {
            val qcs: ISZ[State.Claim] =
              if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
              else ISZ(State.Claim.And(quantClaims))
            r = r :+ ((s2(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym))
          }
        } else {
          r = r :+ ((s2, State.errorValue))
        }
      }
      return r
    }

    def evalQuantEach(quant: AST.Exp.QuantEach): ISZ[(State, State.Value)] = {
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val sType: AST.Typed.Name = quant.seq.typedOpt.get match {
        case t: AST.Typed.Name => t
        case t: AST.Typed.Method => t.tpe.ret.asInstanceOf[AST.Typed.Name]
        case _ => halt("Infeasible")
      }
      val iType = sType.args(0)
      val eType = sType.args(1)
      val pos = quant.fun.params(0).idOpt.get.attr.posOpt.get
      var r = ISZ[(State, State.Value)]()
      val sp: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
      for (p <- evalExp(sp, smt2, rtCheck, state, quant.seq, reporter)) {
        val (s0, seq) = p
        if (s0.status) {
          val (s1, qvar) = Logika.idIntro(pos, s0, qVarRes.context, s"${qVarRes.id}$$Idx", iType, Some(pos))
          val (s2, size) = s1.freshSym(AST.Typed.z, pos)
          val s3 = s2.addClaim(State.Claim.Let.FieldLookup(size, seq, "size"))
          val (s4, nonEmpty) = s3.freshSym(AST.Typed.b, pos)
          val s5 = s4.addClaim(State.Claim.Let.Binary(nonEmpty, size, AST.Exp.BinaryOp.Gt, zero(AST.Typed.z, pos), AST.Typed.z))
          val nonEmptyProp = State.Claim.Prop(T, nonEmpty)
          val (s6, inBound) = s5.freshSym(AST.Typed.b, pos)
          val s7 = s6.addClaim(State.Claim.Let.SeqInBound(inBound, seq, qvar))
          val inBoundProp = State.Claim.Prop(T, inBound)
          val (s8, select) = s7.freshSym(eType, pos)
          val s9 = s8.addClaim(State.Claim.Let.SeqLookup(select, seq, qvar))
          val s10 = s9.addClaim(State.Claim.Let.CurrentId(T, select, qVarRes.context, qVarRes.id, None()))
          val (s11, sym) = s10.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var.Sym(qvar))
          var quantClaims = ISZ[State.Claim]()
          var nextFresh: Z = s11.nextFresh
          for (p <- this (inPfc = T).evalAssignExpValue(sp, smt2, AST.Typed.b, rtCheck, s11.addClaims(ISZ(nonEmptyProp, inBoundProp)), quant.fun.exp, reporter)) {
            val (s12, v) = p
            val (s13, expSym) = value2Sym(s12, v, quant.fun.exp.asStmt.posOpt.get)
            if (s13.status) {
              val props: ISZ[State.Claim] = ISZ(nonEmptyProp, inBoundProp, State.Claim.Prop(T, expSym))
              val s9ClaimsOps = ops.ISZOps(s13.claims)
              val quantClaim = (s9ClaimsOps.slice(s1.claims.size, s11.claims.size) ++ s9ClaimsOps.slice(s11.claims.size + 2, s13.claims.size)) :+
                (if (quant.isForall) State.Claim.Imply(props) else State.Claim.And(props))
              quantClaims = quantClaims :+ State.Claim.And(quantClaim)
            }
            if (nextFresh < s13.nextFresh) {
              nextFresh = s13.nextFresh
            }
          }
          if (quantClaims.isEmpty) {
            r = r :+ ((s0(status = F), State.errorValue))
          } else {
            val qcs: ISZ[State.Claim] =
              if (quantClaims.size == 1) quantClaims(0).asInstanceOf[State.Claim.And].claims
              else ISZ(State.Claim.And(quantClaims))
            r = r :+ ((s0(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym))
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return r
    }

    def methodInfo(isInObject: B, owner: QName, id: String): Logika.InvokeMethodInfo = {
      def extractAssignExpOpt(mi: lang.symbol.Info.Method): Option[AST.AssignExp] = {
        if (mi.ast.purity == AST.Purity.StrictPure) {
          mi.ast.bodyOpt.get.stmts match {
            case ISZ(stmt: AST.Stmt.Var, _: AST.Stmt.Return) => return stmt.initOpt
            case stmts => halt(s"Infeasible: $stmts")
          }
        } else {
          return None()
        }
      }

      def extractResolvedInfo(attr: AST.ResolvedAttr): AST.ResolvedInfo.Method = {
        return attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      }

      if (isInObject) {
        th.nameMap.get(owner :+ id) match {
          case Some(mi: lang.symbol.Info.Method) =>
            return Logika.InvokeMethodInfo(mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr),
              extractAssignExpOpt(mi))
          case Some(mi: lang.symbol.Info.ExtMethod) =>
            return Logika.InvokeMethodInfo(mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr), None())
          case info => halt(s"Infeasible: $owner.$id => $info")
        }
      } else {
        th.typeMap.get(owner) match {
          case Some(info: lang.symbol.TypeInfo.Adt) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return Logika.InvokeMethodInfo(mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr),
                  extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return Logika.InvokeMethodInfo(mi.ast.sig, AST.MethodContract.Simple.empty,
                      extractResolvedInfo(mi.ast.attr), None())
                  case _ => halt("Infeasible")
                }
            }
          case Some(info: lang.symbol.TypeInfo.Sig) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return Logika.InvokeMethodInfo(mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr),
                  extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return Logika.InvokeMethodInfo(mi.ast.sig, AST.MethodContract.Simple.empty,
                      extractResolvedInfo(mi.ast.attr), None())
                  case _ => halt("Infeasible")
                }
            }
          case Some(info) => halt(s"TODO: $info") // TODO
          case _ => halt("Infeasible")
        }
      }
    }

    def methodResST(res: AST.ResolvedInfo.Method): ST = {
      val owner: ISZ[String] =
        if (res.owner.size >= 2 && res.owner(0) == "org" && res.owner(1) == "sireum") ops.ISZOps(res.owner).drop(2)
        else res.owner
      return if (owner.isEmpty) st"${res.id}"
      else if (res.isInObject) st"${(owner, ".")}.${res.id}"
      else st"${(owner, ".")}#${res.id}"
    }

    def evalInvoke(s0: State,
                   invokeReceiverOpt: Option[AST.Exp],
                   ident: AST.Exp.Ident,
                   eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]],
                   attr: AST.ResolvedAttr): ISZ[(State, State.Value)] = {
      val res = attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val resST = methodResST(res)
      val posOpt = attr.posOpt
      val pos = posOpt.get
      val receiverPosOpt: Option[Position] =
        if (invokeReceiverOpt.nonEmpty) invokeReceiverOpt.get.posOpt
        else ident.posOpt
      val info = methodInfo(res.isInObject, res.owner, res.id)
      val contract = info.contract
      val isUnit = info.sig.returnType.typedOpt == AST.Typed.unitOpt
      val ctx = res.owner :+ res.id

      var r = ISZ[(State, State.Value)]()
      val stateSubstMapReceiverOpts: ISZ[(State, HashMap[String, AST.Typed], Option[State.Value.Sym])] =
        if (res.isInObject) {
          ISZ((s0, TypeChecker.emptySubstMap, None()))
        } else {
          var ssmros = ISZ[(State, HashMap[String, AST.Typed], Option[State.Value.Sym])]()
          for (p <- evalReceiver(split, invokeReceiverOpt, ident, res.isInObject)) {
            var typeSubstMap = TypeChecker.emptySubstMap
            val p2 = value2Sym(p._1, p._2, receiverPosOpt.get)
            val s1 = p2._1
            val receiver = p2._2
            val receiverType = receiver.tipe.asInstanceOf[AST.Typed.Name]
            th.typeMap.get(receiverType.ids) match {
              case Some(ti: TypeInfo.Adt) =>
                TypeChecker.buildTypeSubstMap(receiverType.ids, receiverPosOpt, ti.ast.typeParams, receiverType.args,
                  reporter) match {
                  case Some(sm) => typeSubstMap = typeSubstMap ++ sm.entries
                  case _ => r = r :+ ((s1, State.errorValue))
                }
              case Some(ti: TypeInfo.Sig) =>
                TypeChecker.buildTypeSubstMap(receiverType.ids, receiverPosOpt, ti.ast.typeParams, receiverType.args,
                  reporter) match {
                  case Some(sm) => typeSubstMap = typeSubstMap ++ sm.entries
                  case _ => r = r :+ ((s1, State.errorValue))
                }
              case _ => halt(s"Infeasible: $receiverType")
            }
            ssmros = ssmros :+ ((s1, typeSubstMap, Some(receiver)))
          }
          ssmros
        }

      def strictPure(s1: State, typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed,
                     receiverOpt: Option[State.Value.Sym], paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]): Unit = {
        val (s2, pf) = strictPureMethod(smt2, s1, info, typeSubstMap, reporter)
        val (s3, re) = s2.freshSym(retType, pos)
        var args: ISZ[State.Value] = for (q <- paramArgs) yield q._4
        receiverOpt match {
          case Some(receiver) => args = receiver +: args
          case _ =>
        }
        r = r :+ ((s3.addClaim(State.Claim.Let.ProofFunApply(re, pf, args)), re))
      }

      def compositional(s: State, typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed,
                        receiverOpt: Option[State.Value.Sym], paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]): Unit = {
        var s1 = s
        for (q <- paramArgs) {
          val (l, _, arg, v) = q
          val (s3, sym) = value2Sym(s1, v, arg.posOpt.get)
          s1 = s3.addClaim(State.Claim.Let.CurrentId(F, sym, l.context, l.id, arg.posOpt))
        }

        def evalContractCase(logikaComp: Logika, currentReceiverOpt: Option[State.Value.Sym], assume: B, cs0: State,
                             labelOpt: Option[AST.Exp.LitString], invs: ISZ[Info.Inv], requires: ISZ[AST.Exp],
                             ensures: ISZ[AST.Exp]): Logika.ContractCaseResult = {
          val modLocals = contract.modifiedLocalVars

          def modVarsResult(ms0: State, mposOpt: Option[Position]): (State, State.Value) = {
            var ms1 = ms0
            val modObjectVars = contract.modifiedObjectVars
            val mpos = mposOpt.get
            ms1 = Logika.rewriteObjectVars(th, ms1, modObjectVars, mpos, reporter)
            ms1 = Logika.rewriteLocalVars(th, T, ms1, modLocals.keys, mposOpt, reporter)
            if (isUnit) {
              return (ms1, State.Value.Unit(mpos))
            } else {
              val (ms2, v) = Logika.resIntro(mpos, ms1, ctx, retType, mposOpt)
              ms1 = ms2
              return (ms1, v)
            }
          }

          def modVarsRewrite(ms0: State, modPosOpt: Option[Position]): State = {
            var ms1 = ms0
            for (q <- paramArgs) {
              val (p, t, arg, _) = q
              if (modLocals.contains(p)) {
                val (ms2, v) = Logika.idIntro(arg.posOpt.get, ms1, p.context, p.id, t, None())
                ms1 = singleState(assignRec(Split.Disabled, smt2, ms2, arg, v, reporter))
              }
            }
            var rwLocals: ISZ[AST.ResolvedInfo.LocalVar] = for (q <- paramArgs) yield q._1
            if (!isUnit) {
              rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "Res")
            }
            if (receiverOpt.nonEmpty) {
              rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "this")
            }
            ms1 = Logika.rewriteLocalVars(th, F, ms1, rwLocals, modPosOpt, reporter)
            currentReceiverOpt match {
              case Some(receiver) =>
                ms1 = ms1.addClaim(State.Claim.Let.CurrentId(F, receiver, context.methodOpt.get.name, "this",
                  context.methodOpt.get.posOpt))
              case _ =>
            }
            return ms1
          }

          val rep = Reporter.create
          var cs1 = cs0
          val label: String = labelOpt match {
            case Some(label) if label.value != "" =>
              cs1 = cs1.addClaim(State.Claim.Label(label.value, label.posOpt.get))
              s"(${label.value}) p"
            case _ => "P"
          }
          var i = 0
          val cs1PreReqInvSize = cs1.claims.size
          for (inv <- invs) {
            val id = inv.ast.id.value
            i = 0
            val isSingle = inv.ast.claims.size == 1
            for (claim <- inv.ast.claims) {
              val title: String =
                if (isSingle) s"${label}re-invariant $id"
                else s"${label}re-invariant $id#$i"
              if (assume) {
                val p = logikaComp.evalAssume(smt2, F, title, cs1, AST.Util.substExp(claim, typeSubstMap), posOpt, rep)
                val size = p._1.claims.size
                cs1 = p._1(claims = ops.ISZOps(p._1.claims).slice(0, size - 1))
              } else {
                cs1 = logikaComp.evalAssert(smt2, F, title, cs1, AST.Util.substExp(claim, typeSubstMap), posOpt, rep)._1
              }
              i = i + 1
            }
          }
          if (cs1.claims.size != cs1PreReqInvSize) {
            val cs1Ops = ops.ISZOps(cs1.claims)
            cs1 = cs1(claims = cs1Ops.slice(0, cs1PreReqInvSize) :+ State.Claim.And(
              cs1Ops.slice(cs1PreReqInvSize, cs1.claims.size)
            ))
          }
          val hasPreReqInv = cs1.claims.size != cs1PreReqInvSize
          var requireSyms = ISZ[State.Value]()
          i = 0
          val cs1PreReqSize = cs1.claims.size
          for (require <- requires if cs1.status) {
            val title: String =
              if (requires.size == 1) st"${label}re-condition of $resST".render
              else st"${label}re-condition#$i of $resST".render

            val (cs2, sym): (State, State.Value.Sym) =
              if (assume) {
                val p = logikaComp.evalAssume(smt2, F, title, cs1, AST.Util.substExp(require, typeSubstMap), posOpt, rep)
                val size = p._1.claims.size
                assert(p._1.claims(size - 1) == State.Claim.Prop(T, p._2))
                (p._1(claims = ops.ISZOps(p._1.claims).slice(0, size - 1)), p._2)
              } else {
                logikaComp.evalAssert(smt2, F, title, cs1, AST.Util.substExp(require, typeSubstMap), posOpt, rep)
              }
            cs1 = cs2
            requireSyms = requireSyms :+ sym
            if (!cs1.status) {
              val (cs3, rsym) = cs1.freshSym(AST.Typed.b, pos)
              cs1 = cs3.addClaim(State.Claim.Let.And(rsym, requireSyms))
              return Logika.ContractCaseResult(F, cs1, State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
            }
            i = i + 1
          }
          if (cs1.claims.size != cs1PreReqSize) {
            val cs1Ops = ops.ISZOps(cs1.claims)
            cs1 = cs1(claims = cs1Ops.slice(0, cs1PreReqSize) :+ State.Claim.And(
              cs1Ops.slice(cs1PreReqSize, cs1.claims.size)
            ))
          }
          if (hasPreReqInv && cs1.claims.size != cs1PreReqSize) {
            val cs1Ops = ops.ISZOps(cs1.claims)
            cs1 = cs1(claims = cs1Ops.slice(0, cs1PreReqInvSize) :+ State.Claim.And(
              cs1Ops.slice(cs1PreReqInvSize, cs1.claims.size)
            ))
          }
          val (cs4, result) = modVarsResult(cs1, posOpt)
          cs1 = cs4
          val cs1PreEnInvSize = cs1.claims.size
          for (inv <- invs) {
            val id = inv.ast.id.value
            i = 0
            val isSingle = inv.ast.claims.size == 1
            for (claim <- inv.ast.claims) {
              val title: String =
                if (isSingle) s"${label}ost-invariant $id"
                else s"${label}ost-invariant $id#$i"
              cs1 = logikaComp.evalAssume(smt2, F, title, cs1, AST.Util.substExp(claim, typeSubstMap), posOpt, rep)._1
              i = i + 1
            }
          }
          if (cs1.claims.size != cs1PreEnInvSize) {
            val cs1Ops = ops.ISZOps(cs1.claims)
            cs1 = cs1(claims = cs1Ops.slice(0, cs1PreEnInvSize) :+ State.Claim.And(
              cs1Ops.slice(cs1PreEnInvSize, cs1.claims.size)
            ))
          }
          val hasPreEnInv = cs1.claims.size != cs1PreEnInvSize
          i = 0
          val cs1PreEnSize = cs1.claims.size
          for (ensure <- ensures if cs1.status) {
            val title: String =
              if (ensures.size == 1) st"${label}ost-condition of $resST".render
              else st"${label}ost-condition#$i of $resST".render
            cs1 = logikaComp.evalAssume(smt2, F, title, cs1, AST.Util.substExp(ensure, typeSubstMap), posOpt, rep)._1
            if (!cs1.status) {
              val (cs5, rsym) = cs1.freshSym(AST.Typed.b, pos)
              cs1 = cs5.addClaim(State.Claim.Let.And(rsym, requireSyms))
              return Logika.ContractCaseResult(T, cs1, State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
            }
            i = i + 1
          }
          if (cs1.claims.size != cs1PreEnSize) {
            val cs1Ops = ops.ISZOps(cs1.claims)
            cs1 = cs1(claims = cs1Ops.slice(0, cs1PreEnSize) :+ State.Claim.And(
              cs1Ops.slice(cs1PreEnSize, cs1.claims.size)
            ))
          }
          if (hasPreEnInv && cs1.claims.size != cs1PreEnSize) {
            val cs1Ops = ops.ISZOps(cs1.claims)
            cs1 = cs1(claims = cs1Ops.slice(0, cs1PreEnInvSize) :+ State.Claim.And(
              cs1Ops.slice(cs1PreEnInvSize, cs1.claims.size)
            ))
          }
          cs1 = modVarsRewrite(cs1, posOpt)
          val (cs6, rsym) = cs1.freshSym(AST.Typed.b, pos)
          cs1 = cs6.addClaim(State.Claim.Let.And(rsym, requireSyms))
          return Logika.ContractCaseResult(T, Logika.conjunctClaimSuffix(cs0, cs1), result, State.Claim.Prop(T, rsym),
            rep.messages)
        }

        val logikaComp: Logika = {
          val l = Logika.logikaMethod(th, config, ctx, F, receiverOpt.map(t => t.tipe), info.sig, receiverPosOpt,
            contract.reads, contract.modifies, ISZ(), plugins)
          val mctx = l.context.methodOpt.get
          var objectVarInMap = mctx.objectVarInMap
          for (p <- mctx.objectVarMap(typeSubstMap).entries) {
            val (ids, t) = p
            val (s4, sym) = Logika.nameIntro(pos, s1, ids, t, None())
            objectVarInMap = objectVarInMap + ids ~> sym
            s1 = s4
          }
          var fieldVarInMap = mctx.fieldVarInMap
          mctx.receiverTypeOpt match {
            case Some(receiverType) =>
              val (s5, thiz) = Logika.idIntro(mctx.posOpt.get, s1, mctx.name, "this", receiverType, mctx.sig.id.attr.posOpt)
              s1 = s5
              for (p <- mctx.fieldVarMap(typeSubstMap).entries) {
                val (id, (t, posOpt)) = p
                val (s6, sym) = s1.freshSym(t, posOpt.get)
                s1 = s6.addClaim(State.Claim.Let.FieldLookup(sym, thiz, id))
                fieldVarInMap = fieldVarInMap + id ~> sym
              }
            case _ =>
          }
          var localInMap = mctx.localInMap
          for (p <- mctx.localMap(typeSubstMap).entries) {
            val (id, (ctx, _, t)) = p
            val (s7, sym) = Logika.idIntro(pos, s1, ctx, id, t, None())
            localInMap = localInMap + id ~> sym
            s1 = s7
          }
          l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
            localInMap = localInMap))))
        }
        val currentReceiverOpt: Option[State.Value.Sym] = context.methodOpt match {
          case Some(m) => m.receiverTypeOpt match {
            case Some(currentReceiverType) =>
              val lcontext = context.methodOpt.get.name
              val p = Logika.idIntro(posOpt.get, s1, lcontext, "this", currentReceiverType, None())
              s1 = p._1
              s1 = Logika.rewriteLocal(th, s1, F, lcontext, "this", posOpt, reporter)
              Some(p._2)
            case _ => None()
          }
          case _ => None()
        }
        receiverOpt match {
          case Some(receiver) =>
            s1 = s1.addClaim(State.Claim.Let.CurrentId(F, receiver, res.owner :+ res.id, "this", receiverPosOpt))
          case _ =>
        }
        val invs: ISZ[Info.Inv] = if (res.owner.isEmpty) th.worksheetInvs else ISZ()
        contract match {
          case contract: AST.MethodContract.Simple =>
            val ccr = evalContractCase(logikaComp, currentReceiverOpt, F, s1, None(), invs, contract.requires, contract.ensures)
            reporter.reports(ccr.messages)
            r = r :+ ((ccr.state, ccr.retVal))
          case contract: AST.MethodContract.Cases =>
            val root = s1
            var isPreOK = F
            var ccrs = ISZ[Logika.ContractCaseResult]()
            var okCcrs = ISZ[Logika.ContractCaseResult]()
            for (cas <- contract.cases) {
              val ccr = evalContractCase(logikaComp, currentReceiverOpt, T, s1,
                if (cas.label.value == "") None() else Some(cas.label), invs, cas.requires, cas.ensures)
              ccrs = ccrs :+ ccr
              isPreOK = isPreOK || ccr.isPreOK
              if (ccr.isOK) {
                okCcrs = okCcrs :+ ccr
              }
              s1 = s1(nextFresh = ccr.state.nextFresh)
            }
            if (!isPreOK) {
              for (ccr <- ccrs) {
                reporter.reports(ccr.messages)
              }
            }
            if (!isPreOK || okCcrs.isEmpty) {
              r = r :+ ((s1(status = F), State.errorValue))
            } else if (okCcrs.size == 1) {
              val ccr = okCcrs(0)
              s1 = s1(claims = ccr.state.claims :+ ccr.requiresClaim)
              reporter.reports(ccr.messages)
              r = r :+ ((s1, ccr.retVal))
            } else {
              val shouldSplit: B = split match {
                case Split.Default => config.splitAll || config.splitContract
                case Split.Enabled => T
                case Split.Disabled => F
              }
              for (ccr <- okCcrs) {
                reporter.reports(ccr.messages)
              }
              var nextFresh: Z =
                ops.ISZOps(okCcrs).foldLeft((nf: Z, ccr: Logika.ContractCaseResult) =>
                  if (nf < ccr.state.nextFresh) ccr.state.nextFresh else nf, -1)
              if (!isUnit) {
                nextFresh = nextFresh + 1
              }
              if (shouldSplit) {
                for (ccr <- okCcrs) {
                  val cs = ISZ[State.Claim](ccr.requiresClaim,
                    State.Claim.And(ops.ISZOps(ccr.state.claims).slice(root.claims.size, ccr.state.claims.size)))
                  val claims = ops.ISZOps(ccr.state.claims).slice(0, root.claims.size) :+
                    (if (inPfc) State.Claim.Imply(cs) else State.Claim.And(cs))
                  r = r :+ ((ccr.state(nextFresh = nextFresh, claims = claims), ccr.retVal))
                }
              } else {
                var claims = ISZ[State.Claim]()
                for (i <- 0 until root.claims.size) {
                  val rootClaim = root.claims(i)
                  if (ops.ISZOps(okCcrs).forall((ccr: Logika.ContractCaseResult) => ccr.state.claims(i) == rootClaim)) {
                    claims = claims :+ rootClaim
                  } else {
                    claims = claims :+ State.Claim.And(
                      for (ccr <- okCcrs) yield State.Claim.Imply(ISZ(ccr.requiresClaim, ccr.state.claims(i))))
                  }
                }
                claims = claims :+ State.Claim.And(
                  for (ccr <- okCcrs) yield
                    State.Claim.Imply(ISZ(ccr.requiresClaim,
                      State.Claim.And(for (i <- root.claims.size until ccr.state.claims.size) yield ccr.state.claims(i)))))
                claims = claims :+ State.Claim.Or(for (ccr <- okCcrs) yield ccr.requiresClaim)
                s1 = s1(claims = claims)
                if (isUnit) {
                  r = r :+ ((s1(nextFresh = nextFresh), okCcrs(0).retVal))
                } else {
                  val (s7, sym) = s1.freshSym(retType, pos)
                  s1 = s7
                  r = r :+ ((s1(nextFresh = nextFresh).addClaim(State.Claim.And(
                    for (ccr <- okCcrs) yield State.Claim.Imply(ISZ(ccr.requiresClaim,
                      State.Claim.Let.Eq(sym, ccr.retVal))))), sym))
                }
              }
            }
        }
      }

      for (t <- stateSubstMapReceiverOpts) {
        var typeSubstMap = t._2
        val receiverOpt = t._3
        for (p <- evalArgs(split, smt2, rtCheck, t._1, info.sig.params.size, eargs, reporter)) {
          val (s1, vs) = p
          if (s1.status) {
            val argTypes = MSZ.create[AST.Typed](info.sig.params.size, AST.Typed.nothing)
            var paramArgs = ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]()
            eargs match {
              case Either.Left(args) =>
                var i = 0
                for (pArg <- ops.ISZOps(ops.ISZOps(info.sig.params).zip(args)).zip(vs)) {
                  val ((p, arg), vOpt) = pArg
                  val id = p.id.value
                  val argType: AST.Typed = arg.typedOpt.get match {
                    case t: AST.Typed.Method if t.tpe.isByName => t.tpe.ret
                    case t => t
                  }
                  argTypes(i) = argType
                  paramArgs = paramArgs :+
                    ((AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id), argType, arg, vOpt.get))
                  i = i + 1
                }
              case Either.Right(nargs) =>
                var m = HashMap.empty[Z, AST.Exp]
                for (narg <- nargs) {
                  m = m + narg.index ~> narg.arg
                }
                for (i <- 0 until vs.size) {
                  val v = vs(i).get
                  val param = info.sig.params(i)
                  val id = param.id.value
                  val arg = m.get(i).get
                  val argType: AST.Typed = arg.typedOpt.get match {
                    case t: AST.Typed.Method if t.tpe.isByName => t.tpe.ret
                    case t => t
                  }
                  argTypes(i) = argType
                  paramArgs = paramArgs :+
                    ((AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id), argType, arg, v))
                }
            }
            val mType = info.sig.funType
            val invokeType = mType(args = argTypes.toIS, ret = attr.typedOpt.get)
            TypeChecker.unify(th, posOpt, TypeChecker.TypeRelation.Equal, invokeType, mType, reporter) match {
              case Some(sm) =>
                typeSubstMap = typeSubstMap ++ sm.entries
                val retType = info.res.tpeOpt.get.ret.subst(typeSubstMap)
                if (info.strictPureBodyOpt.nonEmpty) {
                  strictPure(s1, typeSubstMap, retType, receiverOpt, paramArgs)
                } else {
                  compositional(s1, typeSubstMap, retType, receiverOpt, paramArgs)
                }
              case _ =>
                r = r :+ ((s1, State.errorValue))
            }
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
      }

      return r
    }

    def evalTupleExp(tuple: AST.Exp.Tuple): ISZ[(State, State.Value)] = {
      if (tuple.args.size == 1) {
        return evalExp(split, smt2, rtCheck, state, tuple.args(0), reporter)
      }
      var r = ISZ[(State, State.Value)]()
      var nextFresh: Z = -1
      for (p <- evalExps(Split.Default, smt2, rtCheck, state, tuple.args.size, (i: Z) => tuple.args(i), reporter)) {
        val (s0, args) = p
        if (s0.status) {
          val (s1, sym) = s0.freshSym(tuple.typedOpt.get, tuple.posOpt.get)
          r = r :+ ((s1.addClaim(State.Claim.Let.TupleLit(sym, args)), sym))
          if (nextFresh < s1.nextFresh) {
            nextFresh = s1.nextFresh
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return if (r.size > 1) r else for (p <- r) yield (p._1(nextFresh = nextFresh), p._2)
    }

    def evalIfExp(sp: Split.Type, ifExp: AST.Exp.If): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      val shouldSplit: B = sp match {
        case Split.Default => config.splitAll || config.splitIf
        case Split.Enabled => T
        case Split.Disabled => F
      }
      val t = ifExp.typedOpt.get
      val pos = ifExp.posOpt.get
      for (p <- evalExp(sp, smt2, rtCheck, state, ifExp.cond, reporter)) {
        val (s0, cond) = p
        if (s0.status) {
          val (s1, sym) = value2Sym(s0, cond, ifExp.cond.posOpt.get)
          val prop = State.Claim.Prop(T, sym)
          val negProp = State.Claim.Prop(F, sym)
          val thenBranch = smt2.sat(config.logVc, config.logVcDirOpt, s"if-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, s1.claims :+ prop, reporter)
          val elseBranch = smt2.sat(config.logVc, config.logVcDirOpt, s"if-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, s1.claims :+ prop, reporter)
          (thenBranch, elseBranch) match {
            case (T, T) =>
              val (s2, re) = s1.freshSym(t, pos)
              val s3vs = evalExp(sp, smt2, rtCheck, s2.addClaim(prop), ifExp.thenExp, reporter)
              val s3NextFresh = maxStateValuesNextFresh(s3vs)
              val s4vs = evalExp(sp, smt2, rtCheck, s2(nextFresh = s3NextFresh).addClaim(negProp), ifExp.elseExp, reporter)
              val s4NextFresh = maxStateValuesNextFresh(s4vs)
              if (shouldSplit) {
                for (s3v <- s3vs) {
                  val (s3t, tv) = s3v
                  val cs = ISZ[State.Claim](prop, State.Claim.And(ops.ISZOps(s3t.claims).
                    slice(s2.claims.size + 1, s3t.claims.size)))
                  val s3 = s3t(nextFresh = s4NextFresh, claims = ops.ISZOps(s3t.claims).slice(0, s2.claims.size) :+
                    (if (inPfc) State.Claim.Imply(cs) else State.Claim.And(cs)))
                  r = r :+ ((s3, tv))
                }
                for (s4v <- s4vs) {
                  val (s4t, ev) = s4v
                  val cs = ISZ[State.Claim](negProp, State.Claim.And(ops.ISZOps(s4t.claims).slice(s2.claims.size + 1, s4t.claims.size)))
                  val s4 = s4t(claims = ops.ISZOps(s4t.claims).slice(0, s2.claims.size) :+
                    (if (inPfc) State.Claim.Imply(cs) else State.Claim.And(cs)))
                  r = r :+ ((s4, ev))
                }
              } else {
                for (s3v <- s3vs; s4v <- s4vs) {
                  val (s3, tv) = s3v
                  val (s4, ev) = s4v
                  val s5 = mergeStates(s1, sym, s3, s4, s4.nextFresh)
                  r = r :+ ((s5.addClaim(State.Claim.If(sym,
                    ISZ(State.Claim.Let.Eq(re, tv)),
                    ISZ(State.Claim.Let.Eq(re, ev)))), re))
                }
              }
            case (T, F) => r = r ++ evalExp(sp, smt2, rtCheck, s1, ifExp.thenExp, reporter)
            case (F, T) => r = r ++ evalExp(sp, smt2, rtCheck, s1, ifExp.elseExp, reporter)
            case (_, _) => r = r :+ ((s0(status = F), State.errorValue))
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return r
    }

    def evalRandomInt(): ISZ[(State, State.Value)] = {
      val pos = e.posOpt.get
      val (s1, sym) = state.freshSym(AST.Typed.z, pos)
      return ISZ((s1.addClaim(State.Claim.Def.Random(sym, pos)), sym))
    }

    def evalSeqIndexValidSize(targ: AST.Type, arg: AST.Exp): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (p <- evalExp(split, smt2, rtCheck, state, arg, reporter)) {
        val (s1, v) = p
        val pos = e.posOpt.get
        val t = targ.typedOpt.get

        def addB(value: B): Unit = {
          if (value) {
            val (s2, sym) = s1.freshSym(AST.Typed.b, pos)
            r = r :+ ((s2.addClaim(State.Claim.Let.Binary(sym, State.Value.Z(0, pos), AST.Exp.BinaryOp.Le,
              v, AST.Typed.z)), sym))
          } else {
            r = r :+ ((s1, State.Value.B(F, pos)))
          }
        }

        def addSize(size: Z): Unit = {
          val (s2, symLo) = s1.freshSym(AST.Typed.b, pos)
          val (s3, symHi) = s2.freshSym(AST.Typed.b, pos)
          val (s4, sym) = s3.freshSym(AST.Typed.b, pos)
          val s5 = s4.addClaims(ISZ(
            State.Claim.Let.Binary(symLo, State.Value.Z(0, pos), AST.Exp.BinaryOp.Le, v, AST.Typed.z),
            State.Claim.Let.Binary(symHi, v, AST.Exp.BinaryOp.Le, State.Value.Z(size, pos), AST.Typed.z),
            State.Claim.Let.Binary(sym, symLo, AST.Exp.BinaryOp.And, symHi, AST.Typed.b)
          ))
          r = r :+ ((s5, sym))
        }

        t match {
          case AST.Typed.z => addB(T)
          case t: AST.Typed.Name =>
            th.typeMap.get(t.ids) match {
              case Some(ti: TypeInfo.SubZ) =>
                if (ti.ast.isZeroIndex) {
                  if (!ti.ast.hasMax) {
                    addB(T)
                  } else {
                    addSize(ti.ast.max + 1)
                  }
                } else {
                  if (!ti.ast.hasMax || !ti.ast.hasMin) {
                    addB(T)
                  } else {
                    addSize(ti.ast.max - ti.ast.min + 1)
                  }
                }
              case _ => addB(F)
            }
          case _ => addB(F)
        }
      }
      return r
    }

    def evalApplyFun(pos: Position, isLocal: B, context: ISZ[String], id: String, t: AST.Typed.Fun, args: ISZ[AST.Exp]): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (p <- evalArgs(split, smt2, rtCheck, state, t.args.size, Either.Left(args), reporter)) {
        val (s0, valueOpts) = p
        if (s0.status && ops.ISZOps(valueOpts).forall((vOpt: Option[State.Value]) => vOpt.nonEmpty)) {
          val (s1, sym) = s0.freshSym(t.ret, pos)
          r = r :+ ((s1.addClaim(State.Claim.Let.Apply(sym, isLocal, context, id, for (vOpt <- valueOpts) yield vOpt.get)), sym))
        } else {
          r = r :+ ((s0(nextFresh = s0.nextFresh + 1), State.errorValue))
        }
      }
      return r
    }

    def evalIsInBound(s0: State, receiver: AST.Exp, index: AST.Exp, attr: AST.ResolvedAttr): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (sv <- evalExp(split, smt2, rtCheck, s0, receiver, reporter)) {
        for (sv2 <- evalExp(split, smt2, rtCheck, sv._1, index, reporter)) {
          val s1 = sv2._1
          val rcv = sv._2
          val idx = sv2._2
          val (s2, sym) = s1.freshSym(AST.Typed.b, attr.posOpt.get)
          r = r :+ ((s2.addClaim(State.Claim.Let.SeqInBound(sym, rcv, idx)), sym))
        }
      }
      return r
    }

    def expH(s0: State): ISZ[(State, State.Value)] = {
      e match {
        case lit: AST.Lit => return ISZ((s0, evalLit(lit)))
        case lit: AST.Exp.StringInterpolate => return ISZ((s0, evalInterpolate(lit)))
        case e: AST.Exp.Ident => return evalIdent(e)
        case e: AST.Exp.Select => return evalSelect(e)
        case e: AST.Exp.Unary => return evalUnaryExp(e)
        case e: AST.Exp.Binary => return evalBinaryExp(e)
        case e: AST.Exp.If => return evalIfExp(split, e)
        case e: AST.Exp.Tuple => return evalTupleExp(e)
        case e: AST.Exp.Invoke =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Select => return evalSeqSelect(e)
                case AST.MethodMode.Constructor =>
                  return evalConstructor(split, F, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
                case AST.MethodMode.Ext if res.id == "randomInt" && res.owner == AST.Typed.sireumName =>
                  return evalRandomInt()
                case AST.MethodMode.Spec if res.id == "seqIndexValidSize" && res.owner == AST.Typed.sireumName =>
                  return evalSeqIndexValidSize(e.targs(0), e.args(0))
                case AST.MethodMode.Method =>
                  if (res.id == "isInBound" && (res.owner == AST.Typed.isName || res.owner == AST.Typed.msName)) {
                    return evalIsInBound(s0, e.receiverOpt.get, e.args(0), e.attr)
                  } else {
                    return evalInvoke(s0, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
                  }
                case AST.MethodMode.Ext =>
                  return evalInvoke(s0, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
                case _ =>
              }
            case res: AST.ResolvedInfo.LocalVar =>
              e.attr.typedOpt.get match {
                case t: AST.Typed.Fun if t.isPureFun => return evalApplyFun(e.posOpt.get, T, res.context, res.id, t, e.args)
                case _ =>
              }
            case _ =>
          }
          halt(s"TODO: $e") // TODO
        case e: AST.Exp.InvokeNamed =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Constructor =>
                  return evalConstructor(split, F, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Copy =>
                  return evalConstructor(split, T, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Spec if res.id == "seqIndexValidSize" && res.owner == AST.Typed.sireumName =>
                  return evalSeqIndexValidSize(e.targs(0), e.args(0).arg)
                case AST.MethodMode.Method =>
                  return evalInvoke(s0, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Ext =>
                  return evalInvoke(s0, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case _ =>
              }
            case _ =>
          }
          halt(s"TODO: $e") // TODO
        case e: AST.Exp.Result => return ISZ(evalResult(e))
        case e: AST.Exp.Input => return ISZ(evalInput(e))
        case e: AST.Exp.QuantType => return ISZ(evalQuantType(e))
        case e: AST.Exp.QuantRange => return evalQuantRange(e)
        case e: AST.Exp.QuantEach =>
          e.seq match {
            case seq: AST.Exp.Select =>
              seq.attr.resOpt.get match {
                case res: AST.ResolvedInfo.Method if
                  (res.owner == AST.Typed.isName || res.owner == AST.Typed.msName) &&
                    res.id == "indices" =>
                  return evalQuantEachIndex(e, seq.receiverOpt.get)
                case _ =>
              }
            case _ =>
          }
          return evalQuantEach(e)
        case e: AST.Exp.This => return ISZ(evalThis(e))
        case _ => halt(s"TODO: $e") // TODO
      }
    }

    def checkSplits(svs: ISZ[(State, State.Value)]): ISZ[(State, State.Value)] = {
      assert(svs.size > 0)
      var nextFresh: Z = -1
      for (sv <- svs if nextFresh == -1) {
        if (sv._1.status) {
          nextFresh = sv._1.nextFresh
        }
      }
      assert(svs.size == 1 || ops.ISZOps(svs).forall((p: (State, State.Value)) => !p._1.status || nextFresh == p._1.nextFresh))
      return svs
    }

    return checkSplits(expH(state))
  }

  def value2Sym(s0: State, v: State.Value, pos: Position): (State, State.Value.Sym) = {
    v match {
      case v: State.Value.Sym => return (s0, v)
      case _ =>
        val (s2, symV) = s0.freshSym(v.tipe, pos)
        return (s2.addClaim(State.Claim.Let.Eq(symV, v)), symV)
    }
  }

  def evalAssumeH(smt2: Smt2, title: String, s0: State, sym: State.Value.Sym, posOpt: Option[Position],
                  reporter: Reporter): State = {
    val s1 = s0(claims = s0.claims :+ State.Claim.Prop(T, sym))
    if (config.sat) {
      val pos = posOpt.get
      val sat = smt2.sat(config.logVc, config.logVcDirOpt, s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims, reporter)
      return s1(status = sat)
    } else {
      return s1
    }
  }

  def evalAssume(smt2: Smt2, rtCheck: B, title: String, s0: State, cond: AST.Exp, posOpt: Option[Position],
                 reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = singleStateValue(evalExp(Split.Disabled, smt2, rtCheck, s0, cond, reporter))
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssumeH(smt2, title, s2, sym, posOpt, reporter), sym)
  }

  def evalAssertH(smt2: Smt2, title: String, s0: State, sym: State.Value.Sym, posOpt: Option[Position],
                  reporter: Reporter): State = {
    val conclusion = State.Claim.Prop(T, sym)
    val pos = posOpt.get
    val r = smt2.valid(config.logVc, config.logVcDirOpt, s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos,
      s0.claims, conclusion, reporter)
    r.kind match {
      case Smt2Query.Result.Kind.Unsat => return s0.addClaim(conclusion)
      case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}", reporter)
      case Smt2Query.Result.Kind.Unknown => error(posOpt, s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds", reporter)
      case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower}", reporter)
      case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower}", reporter)
    }
    return s0(status = F, claims = s0.claims :+ conclusion)
  }

  def evalAssert(smt2: Smt2, rtCheck: B, title: String, s0: State, cond: AST.Exp, posOpt: Option[Position],
                 reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = singleStateValue(evalExp(Split.Disabled, smt2, rtCheck, s0, cond, reporter))
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssertH(smt2, title, s2, sym, posOpt, reporter), sym)
  }

  def evalAssignExp(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State, ae: AST.AssignExp, reporter: Reporter): ISZ[State] = {
    ae match {
      case ae: AST.Stmt.Expr =>
        ae.exp match {
          case e: AST.Exp.Invoke =>
            var r = ISZ[State]()
            for (p <- evalExprInvoke(split, smt2, rtCheck, s0, ae, e, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.status => r = r :+ s1.addClaim(State.Claim.Let.Eq(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
          case _ =>
            var r = ISZ[State]()
            for (p <- evalExp(split, smt2, rtCheck, s0, ae.exp, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.status => r = r :+ s1.addClaim(State.Claim.Let.Eq(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
        }
      case ae: AST.Stmt.Block => return evalBlock(split, smt2, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.If => return evalIf(split, smt2, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Match => return evalMatch(split, smt2, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Return => return evalStmt(split, smt2, rtCheck, s0, ae, reporter)
    }
  }

  def evalAssignExpValue(split: Split.Type, smt2: Smt2, t: AST.Typed, rtCheck: B, s0: State, ae: AST.AssignExp,
                         reporter: Reporter): ISZ[(State, State.Value)] = {
    ae match {
      case ae: AST.Stmt.Expr => return evalExp(split, smt2, rtCheck, s0, ae.exp, reporter)
      case _ =>
        val (s1, sym) = s0.freshSym(t, ae.asStmt.posOpt.get)
        return for (s2 <- evalAssignExp(split, smt2, Some(sym), rtCheck, s1, ae, reporter)) yield (s2, sym)
    }
  }

  def evalAssignLocalH(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: State.Value.Sym,
                       idPosOpt: Option[Position], reporter: Reporter): State = {
    val s1: State = if (decl) s0 else Logika.rewriteLocal(th, s0, F, lcontext, id, idPosOpt, reporter)
    return s1(claims = s1.claims :+ State.Claim.Let.CurrentId(F, rhs, lcontext, id, idPosOpt))
  }

  def evalAssignObjectVarH(s0: State, ids: ISZ[String], rhs: State.Value.Sym, namePosOpt: Option[Position],
                           reporter: Reporter): State = {
    val poss = StateTransformer(CurrentNamePossCollector(ids)).transformState(ISZ(), s0).ctx
    if (poss.isEmpty) {
      reporter.error(namePosOpt, Logika.kind, s"Missing Modifies clause for ${(ids, ".")}.")
      return s0(status = F)
    }
    val (s1, num) = s0.fresh
    val objectVars = HashMap.empty[ISZ[String], (ISZ[Position], Z)] + ids ~> ((poss, num))
    val rt = StateTransformer(CurrentNameRewriter(objectVars)).transformState(HashMap.empty, s1)
    val s2 = rt.resultOpt.get
    val pos = namePosOpt.get
    val s3 = s2(claims = s2.claims :+ State.Claim.Let.CurrentName(rhs, ids, namePosOpt))
    val tipe = rhs.tipe
    if (!th.isMutable(tipe, T)) {
      val (s4, cond) = s3.freshSym(AST.Typed.b, pos)
      return s4.addClaims(ISZ(State.Claim.Let.Binary(cond, rhs, AST.Exp.BinaryOp.Eq, rt.ctx.get(ids).get, tipe),
        State.Claim.Prop(T, cond)))
    } else if (AST.Util.isSeq(tipe)) {
      val (s4, size1) = s3.freshSym(AST.Typed.z, pos)
      val (s5, size2) = s4.freshSym(AST.Typed.z, pos)
      val (s6, cond) = s5.freshSym(AST.Typed.b, pos)
      val o1 = rt.ctx.get(ids).get
      return s6.addClaims(ISZ(
        State.Claim.Let.FieldLookup(size1, o1, "size"),
        State.Claim.Let.FieldLookup(size2, rhs, "size"),
        State.Claim.Let.Binary(cond, size2, AST.Exp.BinaryOp.Eq, size1, AST.Typed.z),
        State.Claim.Prop(T, cond)
      ))
    } else {
      return s3
    }
  }

  def evalAssignThisVarH(s0: State, id: String, rhs: State.Value, pos: Position, reporter: Reporter): State = {
    val lcontext = context.methodOpt.get.name
    val receiverType = context.methodOpt.get.receiverTypeOpt.get
    val (s1, o) = Logika.idIntro(pos, s0, lcontext, "this", receiverType, None())
    val (s2, newSym) = s1.freshSym(receiverType, pos)
    return evalAssignLocalH(F, s2.addClaim(State.Claim.Def.FieldStore(newSym, o, id, rhs)), lcontext, "this",
      newSym, Some(pos), reporter)
  }

  def assignRec(split: Split.Type, smt2: Smt2, s0: State, lhs: AST.Exp, rhs: State.Value.Sym, reporter: Reporter): ISZ[State] = {
    lhs match {
      case lhs: AST.Exp.Ident =>
        lhs.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar =>
            return ISZ(evalAssignLocalH(F, s0, res.context, res.id, rhs, lhs.posOpt, reporter))
          case res: AST.ResolvedInfo.Var =>
            if (res.isInObject) {
              return ISZ(evalAssignObjectVarH(s0, res.owner :+ res.id, rhs, lhs.posOpt, reporter))
            } else {
              return ISZ(evalAssignThisVarH(s0, lhs.id.value, rhs, lhs.posOpt.get, reporter))
            }
          case _ => halt(s"Infeasible: $lhs")
        }
      case lhs: AST.Exp.Invoke =>
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        var r = ISZ[State]()
        for (p1 <- evalExp(split, smt2, T, s0, receiver, reporter);
             p2 <- evalExp(split, smt2, T, p1._1, lhs.args(0), reporter)) {
          val (_, a) = p1
          val (s2, i) = p2
          val s3 = checkSeqIndexing(smt2, T, s2, a, i, lhs.args(0).posOpt, reporter)
          if (s3.status) {
            val (s4, newSym) = s3.freshSym(t, receiverPos)
            r = r ++ assignRec(split, smt2, s4.addClaim(State.Claim.Def.SeqStore(newSym, a, i, rhs)), receiver,
              newSym, reporter)
          } else {
            r = r :+ s3
          }
        }
        return r
      case lhs: AST.Exp.Select =>
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        var r = ISZ[State]()
        for (p <- evalExp(split, smt2, T, s0, receiver, reporter)) {
          val (s1, o) = p
          if (s1.status) {
            val (s2, newSym) = s1.freshSym(t, receiverPos)
            val id = lhs.id.value
            r = r ++ assignRec(split, smt2, s2.addClaim(State.Claim.Def.FieldStore(newSym, o, id, rhs)),
              receiver, newSym, reporter)
          } else {
            r = r :+ s1
          }
        }
        return r
      case _ => halt(s"Infeasible: $lhs")
    }

  }

  def evalPattern(s0: State, v: State.Value, pattern: AST.Pattern, reporter: Reporter): (State, State.Value, Map[String, (State.Value, AST.Typed, Position)]) = {
    val posOpt = pattern.posOpt
    val pos = posOpt.get
    pattern match {
      case pattern: AST.Pattern.Literal =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==", evalLit(pattern.lit), v.tipe)), cond, Map.empty)
      case pattern: AST.Pattern.LitInterpolate =>
        val lit = evalInterpolate(AST.Exp.StringInterpolate(pattern.prefix,
          ISZ(AST.Exp.LitString(pattern.value, AST.Attr(pattern.posOpt))), ISZ(), pattern.attr))
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==", lit, v.tipe)), cond, Map.empty)
      case pattern: AST.Pattern.VarBinding =>
        pattern.tipeOpt match {
          case Some(tipe) =>
            val t = tipe.typedOpt.get
            val (s1, cond) = evalTypeTestH(s0, v, t, tipe.posOpt.get)
            return (s1, cond, Map.empty[String, (State.Value, AST.Typed, Position)] + pattern.id.value ~> ((v, t, pos)))
          case _ =>
            val t = pattern.attr.typedOpt.get
            return (s0, State.Value.B(T, pos),
              Map.empty[String, (State.Value, AST.Typed, Position)] + pattern.id.value ~> ((v, t, pos)))
        }
      case pattern: AST.Pattern.Wildcard =>
        pattern.typeOpt match {
          case Some(tipe) =>
            val (s1, cond) = evalTypeTestH(s0, v, tipe.typedOpt.get, tipe.posOpt.get)
            return (s1, cond, Map.empty)
          case _ =>
            return (s0, State.Value.B(T, pos), Map.empty)
        }
      case pattern: AST.Pattern.Structure =>
        var m = Map.empty[String, (State.Value, AST.Typed, Position)]
        pattern.idOpt match {
          case Some(id) => m = m + id.value ~> ((v, pattern.attr.typedOpt.get, id.attr.posOpt.get))
          case _ =>
        }
        if (pattern.nameOpt.nonEmpty) {
          val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
          if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
            val it = t.args(0).asInstanceOf[AST.Typed.Name]
            val et = t.args(1)
            val hasWildcard = ops.ISZOps(pattern.patterns).exists(
              (p: AST.Pattern) => p.isInstanceOf[AST.Pattern.SeqWildcard])
            val (s1, sizeSym) = s0.freshSym(AST.Typed.z, pos)
            val s2 = s1.addClaim(State.Claim.Let.FieldLookup(sizeSym, v, "size"))
            val (s3, cond) = s2.freshSym(AST.Typed.b, pos)
            val (op, size): (String, Z) =
              if (hasWildcard) (">=", pattern.patterns.size - 1) else ("==", pattern.patterns.size)
            var s4 = s3.addClaim(State.Claim.Let.Binary(cond, sizeSym, op, State.Value.Z(size, pos), AST.Typed.z))
            var conds = ISZ[State.Value](cond)
            val offset: Z = if (it == AST.Typed.z) 0 else th.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ].ast.index
            for (i <- 0 until size) {
              val sub = pattern.patterns(i)
              val subPos = sub.posOpt.get
              val (s5, sym) = s4.freshSym(et, subPos)
              val (s6, cond, subM) = evalPattern(s5.addClaim(
                State.Claim.Let.SeqLookup(sym, v, State.Value.Z(offset + i, subPos))), sym, sub, reporter)
              conds = conds :+ cond
              s4 = s6
              m = m ++ subM.entries
            }
            val (s7, aconds) = s4.freshSym(AST.Typed.b, pos)
            return (s7.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
          } else {
            val (s1, tcond) = evalTypeTestH(s0, v, t, pos)
            val ti = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
            val sm = TypeChecker.buildTypeSubstMap(t.ids, posOpt, ti.ast.typeParams, t.args, reporter).get
            val (s2, o) = s1.freshSym(t, pos)
            var s3 = s2.addClaim(State.Claim.Let.Eq(o, v))
            var conds = ISZ[State.Value](tcond)
            for (p <- ops.ISZOps(ti.extractorTypeMap.entries).zip(pattern.patterns)) {
              val f = p._1._1
              val ft = p._1._2.subst(sm)
              val sub = p._2
              val (s4, sym) = s3.freshSym(ft, sub.posOpt.get)
              s3 = s4.addClaim(State.Claim.Let.FieldLookup(sym, o, f))
              val (s5, cond, subM) = evalPattern(s3, sym, sub, reporter)
              s3 = s5
              conds = conds :+ cond
              m = m ++ subM.entries
            }
            val (s6, aconds) = s3.freshSym(AST.Typed.b, pos)
            return (s6.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
          }
        } else {
          val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Tuple]
          var s1 = s0
          var conds = ISZ[State.Value]()
          for (i <- 1 to pattern.patterns.size) {
            val sub = pattern.patterns(i - 1)
            val (s2, sym) = s1.freshSym(t.args(i - 1), sub.posOpt.get)
            val s3 = s2.addClaim(State.Claim.Let.FieldLookup(sym, v, s"_$i"))
            val (s4, cond, subM) = evalPattern(s3, sym, sub, reporter)
            s1 = s4
            conds = conds :+ cond
            m = m ++ subM.entries
          }
          val (s5, aconds) = s1.freshSym(AST.Typed.b, pos)
          return (s5.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
        }
      case pattern: AST.Pattern.Ref =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        pattern.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var =>
            if (res.owner == AST.Typed.sireumName && res.id == "T" || res.id == "F") {
              return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==",
                State.Value.B(res.id == "T", pos), AST.Typed.b)), cond, Map.empty)
            }
            val t = pattern.attr.typedOpt.get
            val (s2, sym): (State, State.Value.Sym) =
              if (res.isInObject) Logika.nameIntro(pos, s1, res.owner :+ res.id, t, None())
              else evalThisIdH(s1, res.id, t, pos)
            return (s2.addClaim(State.Claim.Let.Binary(cond, v, "==", sym, t)), cond, Map.empty)
          case res: AST.ResolvedInfo.EnumElement =>
            val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
            return (s1.addClaim(State.Claim.Let.Binary(cond, v, "==",
              State.Value.Enum(t, res.owner, res.name, res.ordinal, pos), t)), cond, Map.empty)
          case _ => halt(s"Infeasible: $pattern")
        }
      case _: AST.Pattern.SeqWildcard => halt(s"Infeasible")
    }
  }

  def evalMatch(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
                stmt: AST.Stmt.Match, reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    val shouldSplit: B = split match {
      case Split.Default => config.splitAll || config.splitMatch
      case Split.Enabled => T
      case Split.Disabled => F
    }

    def addPatternVars(s0: State, lcontext: ISZ[String],
                       m: Map[String, (State.Value, AST.Typed, Position)]): (State, ISZ[State.Claim], ISZ[State.Value]) = {
      val ids = m.keys
      val (s1, oldIds) = Logika.rewriteLocals(th, s0, lcontext, ids)
      var s2 = s1
      var bindings = ISZ[State.Value]()
      for (p <- m.entries) {
        val (id, (v, t, pos)) = p
        val (s3, x) = Logika.idIntro(pos, s2, lcontext, id, t, Some(pos))
        val (s4, sym) = s3.freshSym(AST.Typed.b, pos)
        s2 = s4.addClaim(State.Claim.Let.Binary(sym, x, "==", v, t))
        bindings = bindings :+ sym
      }
      return (s2, oldIds, bindings)
    }

    for (p <- evalExp(split, smt2, rtCheck, state, stmt.exp, reporter)) {
      val (s0, v) = p
      if (s0.status) {
        var caseSyms = ISZ[(AST.Case, State.Value.Sym, Map[String, (State.Value, AST.Typed, Position)])]()
        val lcontext: ISZ[String] = context.methodOpt match {
          case Some(mctx) => mctx.name
          case _ => ISZ()
        }
        var s1 = s0
        for (c <- stmt.cases) {
          val (s2, pcond, m) = evalPattern(s1, v, c.pattern, reporter)
          val (s3, oldIds, bindings) = addPatternVars(s2, lcontext, m)
          var conds = ISZ(pcond)
          val s6: State = c.condOpt match {
            case Some(cond) =>
              val (s4, ccond) = singleStateValue(evalExp(Split.Disabled, smt2, rtCheck, s3, cond, reporter))
              if (bindings.nonEmpty) {
                val (s5, icond) = s4.freshSym(AST.Typed.b, c.pattern.posOpt.get)
                conds = conds :+ icond
                s5.addClaim(State.Claim.Let.Imply(icond, bindings :+ ccond))
              } else {
                conds = conds :+ ccond
                s4
              }
            case _ =>
              s3
          }
          val pos = c.pattern.posOpt.get
          val (s7, sym) = s6.freshSym(AST.Typed.b, pos)
          val s8 = s7.addClaim(State.Claim.Let.And(sym, conds))
          val s9 = Logika.rewriteLocals(th, s8, lcontext, m.keys)._1
          val s10 = s9.addClaims(oldIds)
          s1 = s1(nextFresh = s10.nextFresh).
            addClaim(State.Claim.And(for (i <- s1.claims.size until s10.claims.size) yield s10.claims(i)))
          caseSyms = caseSyms :+ ((c, sym, m))
        }
        val stmtPos = stmt.posOpt.get
        if (smt2.sat(config.logVc, config.logVcDirOpt, s"pattern match inexhaustiveness at [${stmtPos.beginLine}, ${stmtPos.beginColumn}]",
          stmtPos, s1.claims :+ State.Claim.And(for (p <- caseSyms) yield State.Claim.Prop(F, p._2)), reporter)) {
          error(stmt.posOpt, "Inexhaustive pattern match", reporter)
          r = r :+ s1(status = F)
        } else {
          var leafClaims = ISZ[(State.Claim, ISZ[State.Claim])]()
          var possibleCases = F
          for (i <- 0 until caseSyms.size) {
            val (c, sym, m) = caseSyms(i)
            val cond = State.Claim.And(
              (for (j <- 0 until i) yield State.Claim.Prop(F, caseSyms(j)._2).asInstanceOf[State.Claim]) :+
                State.Claim.Prop(T, sym))
            val posOpt = c.pattern.posOpt
            val pos = posOpt.get
            val s10 = s1.addClaim(cond)
            if (smt2.sat(config.logVc, config.logVcDirOpt, s"match case pattern at [${pos.beginLine}, ${pos.beginColumn}]",
              pos, s10.claims, reporter)) {
              possibleCases = T
              val (s11, _, bindings) = addPatternVars(s10, lcontext, m)
              var claims = ISZ[State.Claim]()
              for (s12 <- evalBody(split, smt2, rOpt, rtCheck, s11.addClaim(State.Claim.And(for (b <- bindings) yield
                State.Claim.Prop(T, b.asInstanceOf[State.Value.Sym]))), c.body, c.pattern.posOpt, reporter)) {
                s1 = s1(nextFresh = s12.nextFresh)
                if (s12.status) {
                  claims = claims :+ State.Claim.And(
                    ops.ISZOps(s12.claims).slice(s1.claims.size + 1, s12.claims.size
                    ))
                }
              }
              if (claims.nonEmpty) {
                leafClaims = leafClaims :+ ((cond, claims))
              }
            } else {
              if (!shouldSplit) {
                error(posOpt, "Infeasible pattern matching case", reporter)
              }
            }
          }
          if (leafClaims.isEmpty) {
            if (!possibleCases) {
              error(stmt.posOpt, "Infeasible pattern matching cases", reporter)
            }
            r = r :+ s1(status = F)
          }
          if (shouldSplit) {
            r = r ++ (for (p <- leafClaims; c <- p._2) yield s1.addClaims(ISZ(p._1, c)))
          } else {
            r = r :+ s1.addClaim(State.Claim.And(for (p <- leafClaims) yield State.Claim.Imply(ISZ(p._1, State.Claim.Or(p._2)))))
          }
        }
      } else {
        r = r :+ s0
      }
    }
    if (r.size > 1) {
      val nextFresh = maxStatesNextFresh(r)
      return for (s <- r) yield s(nextFresh = nextFresh)
    } else {
      return r
    }
  }

  def evalBlock(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State, block: AST.Stmt.Block,
                reporter: Reporter): ISZ[State] = {
    return evalBody(split, smt2, rOpt, rtCheck, s0, block.body, block.attr.posOpt, reporter)
  }

  def evalIf(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State, ifStmt: AST.Stmt.If,
             reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    val shouldSplit: B = split match {
      case Split.Default => config.splitAll || config.splitIf
      case Split.Enabled => T
      case Split.Disabled => F
    }
    for (p <- evalExp(split, smt2, rtCheck, s0, ifStmt.cond, reporter)) {
      val (s1, v) = p
      if (s1.status) {
        val pos = ifStmt.cond.posOpt.get
        val (s1c, cond) = value2Sym(s1, v, pos)
        if (!s1c.status) {
          r = r :+ s1c
        } else {
          val s2 = Logika.conjunctClaimSuffix(s0, s1c)
          val prop = State.Claim.Prop(T, cond)
          val thenClaims = s2.claims :+ prop
          val thenSat = smt2.sat(config.logVc, config.logVcDirOpt, s"if-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, thenClaims, reporter)
          val s4s: ISZ[State] = if (thenSat) {
            val s3s = evalBody(split, smt2, rOpt, rtCheck, s2(claims = thenClaims), ifStmt.thenBody, ifStmt.posOpt, reporter)
            s3s
          } else {
            ISZ(s2(status = F, claims = thenClaims))
          }
          val s4NextFresh = maxStatesNextFresh(s4s)
          val negProp = State.Claim.Prop(F, cond)
          val elseClaims = s2.claims :+ negProp
          val elseSat = smt2.sat(config.logVc, config.logVcDirOpt, s"if-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
            pos, elseClaims, reporter)
          val s6s: ISZ[State] = if (elseSat) {
            val s5s = evalBody(split, smt2, rOpt, rtCheck, s2(claims = elseClaims, nextFresh = s4NextFresh), ifStmt.elseBody, ifStmt.posOpt, reporter)
            s5s
          } else {
            ISZ(s2(status = F, claims = elseClaims, nextFresh = s4NextFresh))
          }
          val s6NextFresh = maxStatesNextFresh(s6s)
          (thenSat, elseSat) match {
            case (T, T) =>
              if (shouldSplit) {
                for (s4t <- s4s) {
                  val cs = ISZ[State.Claim](prop, State.Claim.And(ops.ISZOps(s4t.claims).slice(s2.claims.size + 1, s4t.claims.size)))
                  val s4 = s4t(nextFresh = s6NextFresh, claims = ops.ISZOps(s4t.claims).slice(0, s2.claims.size) :+
                    (if (inPfc) State.Claim.Imply(cs) else State.Claim.And(cs)))
                  r = r :+ s4
                }
                for (s6t <- s6s) {
                  val cs = ISZ[State.Claim](negProp, State.Claim.And(ops.ISZOps(s6t.claims).slice(s2.claims.size + 1, s6t.claims.size)))
                  val s6 = s6t(claims = ops.ISZOps(s6t.claims).slice(0, s2.claims.size) :+
                    (if (inPfc) State.Claim.Imply(cs) else State.Claim.And(cs)))
                  r = r :+ s6
                }
              } else {
                for (s4 <- s4s; s6 <- s6s) {
                  r = r :+ mergeStates(s2, cond, s4, s6, s6NextFresh)
                }
              }
            case (T, F) =>
              for (s4 <- s4s) {
                r = r :+ s4(status = s4.status && !reporter.hasError, nextFresh = s6NextFresh)
              }
            case (F, T) =>
              for (s6 <- s6s) {
                r = r :+ s6(status = s6.status && !reporter.hasError)
              }
            case _ =>
              for (s4 <- s4s; s6 <- s6s) {
                val s7 = mergeStates(s2, cond, s4, s6, s6NextFresh)
                r = r :+ s7(status = F)
              }
          }
        }
      } else {
        r = r :+ s1
      }
    }
    return r
  }

  def evalExprInvoke(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, stmt: AST.Stmt, e: AST.Exp.Invoke, reporter: Reporter): ISZ[(State, State.Value)] = {
    def printH(): ISZ[(State, State.Value)] = {
      val pos = e.posOpt.get
      var ss = ISZ[State](state)
      var nextFresh: Z = -1
      for (arg <- e.args) {
        var newSS = ISZ[State]()
        for (s <- ss) {
          if (s.status) {
            val svs = evalExp(split, smt2, rtCheck, s, arg, reporter)
            for (sv <- svs) {
              val s2 = sv._1
              newSS = newSS :+ s2
              if (nextFresh < s2.nextFresh) {
                nextFresh = s2.nextFresh
              }
            }
          } else {
            newSS = newSS :+ s
            if (nextFresh < s.nextFresh) {
              nextFresh = s.nextFresh
            }
          }
        }
        ss = for (s2 <- newSS) yield s2(nextFresh = nextFresh)
      }
      val r = State.Value.Unit(pos)
      return for (s <- ss) yield (s, r)
    }

    e.attr.resOpt.get match {
      case AST.ResolvedInfo.BuiltIn(kind) =>
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.Assert =>
            val exp = e.args(0)
            val (s0, v) = evalAssert(smt2, T, "Assertion", state, exp, exp.posOpt, reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.AssertMsg =>
            val exp = e.args(0)
            val (s0, v) = evalAssert(smt2, T, "Assertion", state, exp, exp.posOpt, reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.Assume =>
            val exp = e.args(0)
            val (s0, v) = evalAssume(smt2, T, "Assumption", state, exp, exp.posOpt, reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.AssumeMsg =>
            val exp = e.args(0)
            val (s0, v) = evalAssume(smt2, T, "Assumption", state, exp, exp.posOpt, reporter)
            return ISZ((Logika.conjunctClaimSuffix(state, s0), v))
          case AST.ResolvedInfo.BuiltIn.Kind.Print => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Println => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Cprint => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Cprintln => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Eprint => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Eprintln => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Halt =>
            val s0 = state(status = F)
            return ISZ((s0, State.errorValue))
          case _ => halt(s"TODO: $stmt") // TODO
        }
      case _ =>
        return for (p <- evalExp(split, smt2, rtCheck, state, e, reporter)) yield (Logika.conjunctClaimSuffix(state, p._1), p._2)
    }
  }

  def evalProofStep(smt2: Smt2,
                    stateMap: (State, HashSMap[Z, StepProofContext]),
                    step: AST.ProofAst.Step,
                    reporter: Reporter): (State, HashSMap[Z, StepProofContext]) = {
    @pure def extractClaims(steps: ISZ[AST.ProofAst.Step]): ISZ[AST.Exp] = {
      var r = ISZ[AST.Exp]()
      for (stp <- steps) {
        stp match {
          case stp: AST.ProofAst.Step.Regular => r = r :+ AST.Util.deBruijn(stp.claim)
          case stp: AST.ProofAst.Step.Assert => r = r :+ AST.Util.deBruijn(stp.claim)
          case stp: AST.ProofAst.Step.Assume => r = r :+ AST.Util.deBruijn(stp.claim)
          case _ =>
        }
      }
      return r
    }
    val stepNo = step.no.value
    var (s0, m) = stateMap
    step match {
      case step: AST.ProofAst.Step.Regular =>
        for (plugin <- plugins if plugin.canHandle(this, step.just)) {
          val Plugin.Result(r, nextFresh, claims) =
            plugin.handle(this, smt2, config.logVc, config.logVcDirOpt, m, s0, step, reporter)
          return (s0(status = r, nextFresh = nextFresh).addClaim(State.Claim.And(claims)),
            m + stepNo ~> StepProofContext.Regular(stepNo, step.claim, claims))
        }
        reporter.error(step.just.posOpt, Logika.kind, "Could not recognize justification form")
        return (s0(status = F), m)
      case step: AST.ProofAst.Step.Assume =>
        val (status, nextFresh, claims, claim) = evalRegularStepClaim(smt2, s0, step.claim, step.no.posOpt, reporter)
        return (s0(status = status, nextFresh = nextFresh, claims = (s0.claims ++ claims) :+ claim),
          m + stepNo ~> StepProofContext.Regular(stepNo, step.claim, claims :+ claim))
      case step: AST.ProofAst.Step.SubProof =>
        for (sub <- step.steps if s0.status) {
          val p = evalProofStep(smt2, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
        }
        s0 = stateMap._1(status = s0.status, nextFresh = s0.nextFresh)
        if (s0.status) {
          m = stateMap._2 + stepNo ~> StepProofContext.SubProof(stepNo,
            AST.Util.deBruijn(step.steps(0).asInstanceOf[AST.ProofAst.Step.Assume].claim), extractClaims(step.steps))
          return (s0, m)
        } else {
          return (s0, stateMap._2)
        }
      case step: AST.ProofAst.Step.Assert =>
        var provenClaims = HashSet.empty[AST.Exp]
        for (sub <- step.steps if s0.status) {
          val p = evalProofStep(smt2, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
          sub match {
            case sub: AST.ProofAst.Step.Regular if s0.status => provenClaims = provenClaims + sub.claimDeBruijn
            case _ =>
          }
        }
        s0 = stateMap._1(nextFresh = s0.nextFresh)
        if (!s0.status) {
          return (s0(status = F), stateMap._2)
        }
        if (!provenClaims.contains(step.claimDeBruijn)) {
          reporter.error(step.claim.posOpt, Logika.kind, "The claim is not proven in the assertion's sub-proof")
          return (s0(status = F), stateMap._2)
        }
        val (status, nextFresh, claims, claim) = evalRegularStepClaim(smt2, s0, step.claim, step.no.posOpt, reporter)
        return (s0(status = status, nextFresh = nextFresh, claims = (s0.claims ++ claims) :+ claim),
          m + stepNo ~> StepProofContext.Regular(stepNo, step.claim, claims :+ claim))
      case step: AST.ProofAst.Step.Let =>
        for (sub <- step.steps if s0.status) {
          val p = evalProofStep(smt2, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
        }
        s0 = stateMap._1(status = s0.status, nextFresh = s0.nextFresh)
        if (s0.status) {
          if (step.steps.nonEmpty && step.steps(0).isInstanceOf[AST.ProofAst.Step.Assume]) {
            return (s0,
              stateMap._2 + stepNo ~> StepProofContext.FreshAssumeSubProof(stepNo, step.params,
                AST.Util.deBruijn(step.steps(0).asInstanceOf[AST.ProofAst.Step.Assume].claim),
                extractClaims(step.steps)))
          } else {
            return (s0,
              stateMap._2 + stepNo ~> StepProofContext.FreshSubProof(stepNo, step.params, extractClaims(step.steps)))
          }
        } else {
          return (s0, stateMap._2)
        }
      case step: AST.ProofAst.Step.StructInduction => halt(s"TODO: $step")
    }
  }

  def evalRegularStepClaim(smt2: Smt2, s0: State, claim: AST.Exp, posOpt: Option[Position], reporter: Reporter): (B, Z, ISZ[State.Claim], State.Claim) = {
    val svs = evalExp(Logika.Split.Disabled, smt2, T, s0, claim, reporter)
    for (sv <- svs) {
      val (s1, v) = sv
      val (s2, sym) = value2Sym(s1, v, posOpt.get)
      val vProp = State.Claim.Prop(T, sym)
      return (s2.status, s2.nextFresh, ops.ISZOps(s2.claims).slice(s0.claims.size, s2.claims.size), vProp)
    }
    return (F, s0.nextFresh, s0.claims, State.Claim.And(ISZ()))
  }

  def evalStmt(split: Split.Type, smt2: Smt2, rtCheck: B, state: State, stmt: AST.Stmt, reporter: Reporter): ISZ[State] = {
    if (!state.status) {
      return ISZ(state)
    }

    def evalAssignLocal(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: AST.AssignExp, lhsType: AST.Typed,
                        idPosOpt: Option[Position]): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, lhsType, rtCheck, s0, rhs, reporter)) {
        val (s1, init) = p
        if (s1.status) {
          val (s2, sym) = value2Sym(s1, init, rhs.asStmt.posOpt.get)
          r = r :+ Logika.conjunctClaimSuffix(s0, evalAssignLocalH(decl, s2, lcontext, id, sym, idPosOpt, reporter))
        } else {
          r = r :+ s1
        }
      }
      return r
    }

    def evalAssign(s0: State, assignStmt: AST.Stmt.Assign): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, assignStmt.lhs.typedOpt.get, rtCheck, s0, assignStmt.rhs, reporter)) {
        val (s1, init) = p
        if (s1.status) {
          val (s2, sym) = value2Sym(s1, init, assignStmt.rhs.asStmt.posOpt.get)
          r = r ++ (for (s3 <- assignRec(split, smt2, s2, assignStmt.lhs, sym, reporter)) yield Logika.conjunctClaimSuffix(s0, s3))
        } else {
          r = r :+ s1
        }
      }
      return r
    }

    def evalFor(s0: State, forStmt: AST.Stmt.For): ISZ[State] = {
      var r = ISZ[State]()

      def evalStep(s1: State, idSym: State.Value.Sym, step: AST.EnumGen.Range.Step): (ISZ[State], ISZ[State]) = {
        var done = ISZ[State]()
        var loop = ISZ[State]()
        for (p1 <- evalExp(split, smt2, rtCheck, s1, step.start, reporter);
             p2 <- evalExp(split, smt2, rtCheck, p1._1, step.end, reporter)) {
          val (_, start) = p1
          val (s3, end) = p2
          val s4vs: ISZ[(State, Option[State.Value])] = step.byOpt match {
            case Some(e) => for (p3 <- evalExp(split, smt2, rtCheck, s3, e, reporter)) yield (p3._1, Some(p3._2))
            case _ => ISZ((s3, None()))
          }
          for (p3 <- s4vs) {
            val (s4, _) = p3
            val (s5, lb) = s4.freshSym(AST.Typed.b, step.start.posOpt.get)
            val (s6, ub) = s5.freshSym(AST.Typed.b, step.end.posOpt.get)
            val (s7, lub) = s6.freshSym(AST.Typed.b, step.attr.posOpt.get)
            val s8 = s7.addClaim(State.Claim.Let.Binary(lb, start, AST.Exp.BinaryOp.Le, idSym, start.tipe))
            val s9 = s8.addClaim(State.Claim.Let.Binary(lb, idSym,
              if (step.isInclusive) AST.Exp.BinaryOp.Le else AST.Exp.BinaryOp.Lt, end, start.tipe))
            val s10 = s9.addClaim(State.Claim.Let.Binary(lub, lb, AST.Exp.BinaryOp.And, ub, AST.Typed.b))
            done = done :+ s10.addClaim(State.Claim.Prop(F, lub))
            loop = loop :+ s10.addClaim(State.Claim.Prop(T, lub))
          }
        }
        return (loop, done)
      }

      def evalEach(s1: State, enumGen: AST.EnumGen.Range.Expr): (ISZ[State], ISZ[State]) = {
        halt("TODO") // TODO
      }

      def evalEnumGen(s1: State, enumGen: AST.EnumGen.For): (ISZ[State], ISZ[State]) = {
        var done = ISZ[State]()
        var loop = ISZ[State]()
        enumGen.range match {
          case range: AST.EnumGen.Range.Step =>
            val pos: Position = enumGen.idOpt match {
              case Some(id) => id.attr.posOpt.get
              case _ => range.attr.posOpt.get
            }
            val (s2, idSym) = s1.freshSym(range.start.typedOpt.get, pos)
            val (s3, num) = s2.fresh
            val (ds, ls) = evalStep(s3, idSym, range)
            val ctx = context.methodOpt.get.name
            enumGen.idOpt match {
              case Some(id) =>
                for (d <- ds) {
                  done = done :+ d.addClaim(State.Claim.Let.Id(idSym, ctx, id.value, num, ISZ(pos)))
                }
                for (l <- ls) {
                  loop = loop :+ l.addClaim(State.Claim.Let.CurrentId(F, idSym, ctx, id.value, Some(pos)))
                }
              case _ =>
                done = done ++ ds
                loop = loop ++ ls
            }
          case range: AST.EnumGen.Range.Expr =>
            halt("TODO") // TODO
        }
        return (loop, done)
      }

      halt("TODO") // TODO

      //return r
    }

    def evalWhile(s0: State, whileStmt: AST.Stmt.While): ISZ[State] = {
      var r = ISZ[State]()
      for (s0w <- checkExps(split, smt2, F, "Loop invariant", " at the beginning of while-loop", s0,
        whileStmt.invariants, reporter)) {
        if (s0w.status) {
          val s1 = Logika.conjunctClaimSuffix(s0, s0w)
          val modLocalVars = whileStmt.modifiedLocalVars
          if (whileStmt.modifiedObjectVars.nonEmpty || whileStmt.modifiedRecordVars.nonEmpty) {
            halt("TODO: rewrite Vars/fields as well") // TODO
          }
          val s0R: State = {
            var srw = Logika.rewriteLocalVars(th, F, s0(nextFresh = s1.nextFresh), modLocalVars.keys, whileStmt.posOpt, reporter)
            for (p <- modLocalVars.entries) {
              val (res, (tipe, pos)) = p
              val (srw1, sym) = srw.freshSym(tipe, pos)
              srw = srw1(claims = srw1.claims :+ State.Claim.Let.CurrentId(F, sym, res.context, res.id, Some(pos)))
            }
            srw
          }
          val s2 = State(T, s0R.claims ++ (for (i <- s0.claims.size until s1.claims.size) yield s1.claims(i)), s0R.nextFresh)
          for (p <- evalExp(split, smt2, rtCheck, s2, whileStmt.cond, reporter)) {
            val (s3, v) = p
            val pos = whileStmt.cond.posOpt.get
            val (s4, cond) = value2Sym(s3, v, pos)
            val prop = State.Claim.Prop(T, cond)
            val thenClaims = s4.claims :+ prop
            val thenSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
              pos, thenClaims, reporter)
            var nextFresh: Z = s4.nextFresh
            if (thenSat) {
              for (s5 <- evalStmts(split, smt2, None(), rtCheck, s4(claims = thenClaims), whileStmt.body.stmts, reporter)) {
                if (s5.status) {
                  for (s6 <- checkExps(split, smt2, F, "Loop invariant", " at the end of while-loop",
                    s5, whileStmt.invariants, reporter)) {
                    if (nextFresh < s6.nextFresh) {
                      nextFresh = s6.nextFresh
                    }
                  }
                } else {
                  if (nextFresh < s5.nextFresh) {
                    nextFresh = s5.nextFresh
                  }
                }
              }
            }
            val negProp = State.Claim.Prop(F, cond)
            val elseClaims = s4.claims :+ negProp
            val elseSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
              pos, elseClaims, reporter)
            r = r :+ State(status = elseSat, claims = elseClaims, nextFresh = nextFresh)
          }
        } else {
          r = r :+ s0w
        }
      }
      return r
    }

    @pure def loopBound(ids: ISZ[String]): Z = {
      return config.loopBounds.get(LoopId(ids)).getOrElse(config.defaultLoopBound)
    }

    def evalWhileUnroll(sp: Split.Type, s0: State, whileStmt: AST.Stmt.While): ISZ[State] = {
      val loopId: ISZ[String] = whileStmt.context

      def whileRec(current: State, numLoops: Z): ISZ[State] = {
        if (!current.status) {
          return ISZ(current)
        }
        var r = ISZ[State]()
        for (s1 <- checkExps(sp, smt2, F, "Loop invariant", " at the beginning of while-loop", current,
          whileStmt.invariants, reporter)) {
          if (s1.status) {
            for (p <- evalExp(sp, smt2, rtCheck, s1, whileStmt.cond, reporter)) {
              val (s2, v) = p
              val pos = whileStmt.cond.posOpt.get
              val (s2w, cond) = value2Sym(s2, v, pos)
              val s3 = Logika.conjunctClaimSuffix(current, s2w)
              val prop = State.Claim.Prop(T, cond)
              val thenClaims = s3.claims :+ prop
              val thenSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]",
                pos, thenClaims, reporter)
              for (s4 <- evalStmts(sp, smt2, None(), rtCheck, s3(claims = thenClaims), whileStmt.body.stmts, reporter)) {
                val s6s: ISZ[State] = if (s4.status) {
                  val bound = loopBound(loopId)
                  if (bound <= 0 || numLoops + 1 < loopBound(loopId)) {
                    whileRec(s4(status = thenSat), numLoops + 1)
                  } else {
                    if (bound > 0) {
                      warn(whileStmt.cond.posOpt, s"Under-approximation due to loop unrolling capped with bound $bound",
                        reporter)
                      ISZ(s4(status = F))
                    } else {
                      ISZ(s4)
                    }
                  }
                } else {
                  ISZ(s4)
                }
                val nextFresh = maxStatesNextFresh(s6s)
                for (s6 <- s6s) {
                  val negProp = State.Claim.Prop(F, cond)
                  val elseClaims = s3.claims :+ negProp
                  val elseSat = smt2.sat(config.logVc, config.logVcDirOpt, s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]",
                    pos, elseClaims, reporter)
                  (thenSat, elseSat) match {
                    case (T, T) =>
                      if (s6.status) {
                        r = r :+ mergeStates(s3, cond, s6, s3, nextFresh)
                      } else {
                        val claimsOps = ops.ISZOps(s3.claims)
                        r = r :+ s3(status = s3.status && !reporter.hasError, nextFresh = nextFresh,
                          claims = claimsOps.slice(0, s3.claims.size - 1) :+
                            State.Claim.Imply(ISZ(negProp, s3.claims(s3.claims.size - 1))))
                      }
                    case (T, F) => r = r :+ s6(status = s6.status && !reporter.hasError, nextFresh = nextFresh)
                    case (F, T) => r = r :+ s3(status = s3.status && !reporter.hasError, nextFresh = nextFresh)
                    case _ =>
                      val s7 = mergeStates(s3, cond, s6, s3, nextFresh)
                      r = r :+ s7(status = F)
                  }
                }
              }
            }
          } else {
            r = r :+ s1
          }
        }
        return r
      }

      return whileRec(s0, 0)
    }

    def evalReturn(s0: State, returnStmt: AST.Stmt.Return): ISZ[State] = {
      returnStmt.expOpt match {
        case Some(exp) =>
          var r = ISZ[State]()
          for (p <- evalExp(split, smt2, rtCheck, s0, exp, reporter)) {
            val (s1, v) = p
            val pos = exp.posOpt.get
            val (s2, sym) = value2Sym(s1, v, pos)
            r = r :+ Logika.conjunctClaimSuffix(s0,
              s2.addClaim(State.Claim.Let.CurrentId(F, sym, context.methodOpt.get.name, "Res", Some(pos))))
          }
          return r
        case _ => return ISZ(state)
      }
    }

    def evalSpecBlock(sp: Split.Type, s0: State, block: AST.Stmt.SpecBlock): ISZ[State] = {
      return evalBlock(sp, smt2, None(), rtCheck, s0, block.block, reporter)
    }

    def evalInv(s0: State, invStmt: AST.Stmt.Inv): ISZ[State] = {
      var r = ISZ[State]()
      var ss = ISZ(s0)
      var i = 0
      val isSingle = invStmt.claims.size == 1
      val id = invStmt.id.value
      var nextFresh: Z = -1
      for (claim <- invStmt.claims) {
        val sst = ss
        ss = ISZ[State]()
        for (s1 <- sst) {
          val title: String = if (isSingle) s"Invariant $id" else s"Invariant $id#$i"
          val s2 = evalAssert(smt2, rtCheck, title, s1, claim, claim.posOpt, reporter)._1
          if (s2.status) {
            ss = ss :+ s2
            if (nextFresh < s2.nextFresh) {
              nextFresh = s2.nextFresh
            }
          } else {
            r = r :+ s2
          }
        }
        ss = for (s3 <- ss) yield s3(nextFresh = nextFresh)
        i = i + 1
      }
      return ss ++ r
    }

    def evalDeduceSteps(s0: State, deduceStmt: AST.Stmt.DeduceSteps): ISZ[State] = {
      var p = (s0, HashSMap.empty[Z, StepProofContext])
      for (step <- deduceStmt.steps if p._1.status) {
        p = evalProofStep(smt2, p, step, reporter)
      }
      return ISZ(p._1)
    }

    def evalDeduceSequent(s0: State, deduceStmt: AST.Stmt.DeduceSequent): ISZ[State] = {
      @pure def premises(st: State, sequent: AST.Sequent): (State, HashSMap[Z, StepProofContext]) = {
        var r = HashSMap.empty[Z, StepProofContext]
        var no: Z = -1
        var st0 = st
        for (premise <- sequent.premises if st0.status) {
          val (status, nextFresh, claims, claim) = evalRegularStepClaim(smt2, st0, premise, premise.posOpt, reporter)
          r = r + no ~> StepProofContext.Regular(no, AST.Util.deBruijn(premise), claims :+ claim)
          no = no - 1
          st0 = st0(status = status, nextFresh = nextFresh, claims = (st0.claims ++ claims) :+ claim)
        }
        return (st0, r)
      }
      var st0 = s0
      for (sequent <- deduceStmt.sequents if st0.status) {
        if (deduceStmt.justOpt.isEmpty && sequent.steps.isEmpty) {
          var i = 0
          for (premise <- sequent.premises if st0.status) {
            st0 = evalAssume(smt2, rtCheck, s"Premise #$i", st0, premise, premise.posOpt, reporter)._1
            i = i + 1
          }
          if (st0.status) {
            st0 = evalAssert(smt2, rtCheck, "Conclusion", st0, sequent.conclusion, sequent.conclusion.posOpt, reporter)._1
          }
        } else {
          var p = premises(st0, sequent)
          for (step <- sequent.steps if p._1.status) {
            p = evalProofStep(smt2, p, step, reporter)
          }
          st0 = s0(status = p._1.status, nextFresh = p._1.nextFresh, claims = s0.claims)
          val provenClaims = HashSet ++ (for (spc <- p._2.values if spc.isInstanceOf[StepProofContext.Regular]) yield
            AST.Util.deBruijn(spc.asInstanceOf[StepProofContext.Regular].exp))
          if (st0.status && !provenClaims.contains(AST.Util.deBruijn(sequent.conclusion))) {
            reporter.error(sequent.conclusion.posOpt, Logika.kind, "The sequent's conclusion has not been proven")
            st0 = st0(status = F)
          }
        }
      }
      return ISZ(s0(status = st0.status, nextFresh = st0.nextFresh))
    }

    def evalVarPattern(varPattern: AST.Stmt.VarPattern): ISZ[State] = {
      var r = ISZ[State]()
      var nextFresh = state.nextFresh
      for (p <- evalAssignExpValue(split, smt2, varPattern.pattern.typedOpt.get, rtCheck, state, varPattern.init, reporter)) {
        val (s1, init) = p
        val s7: State = if (s1.status) {
          val (s2, sym) = value2Sym(s1, init, varPattern.init.asStmt.posOpt.get)
          val (s3, cond, m) = evalPattern(s2, sym, varPattern.pattern, reporter)
          var s4 = s3
          for (p <- m.entries) {
            val (id, (v, _, pos)) = p
            val (s5, vSym) = value2Sym(s4, v, pos)
            s4 = s5.addClaim(State.Claim.Let.CurrentId(T, vSym, context.methodName, id, Some(pos)))
          }
          val (s6, condSym) = value2Sym(s4, cond, varPattern.pattern.posOpt.get)
          evalAssertH(smt2, "Variable Pattern Matching", s6, condSym, varPattern.pattern.posOpt, reporter)
        } else {
          s1
        }
        r = r :+ s7
        if (nextFresh < s7.nextFresh) {
          nextFresh = s7.nextFresh
        }

      }
      return for (s <- r) yield s(nextFresh = nextFresh)
    }

    def evalStmtH(): ISZ[State] = {
      stmt match {
        case stmt@AST.Stmt.Expr(e: AST.Exp.Invoke) =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return for (p <- evalExprInvoke(split, smt2, rtCheck, state, stmt, e, reporter)) yield p._1
        case stmt: AST.Stmt.Var if stmt.initOpt.nonEmpty =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          stmt.attr.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              return evalAssignLocal(T, state, res.context, res.id, stmt.initOpt.get, stmt.attr.typedOpt.get,
                stmt.id.attr.posOpt)
            case _ => halt(s"TODO: $stmt") // TODO
          }
        case stmt: AST.Stmt.VarPattern =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalVarPattern(stmt)
        case stmt: AST.Stmt.Assign =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalAssign(state, stmt)
        case stmt: AST.Stmt.If =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalIf(split, smt2, None(), rtCheck, state, stmt, reporter)
        case stmt: AST.Stmt.While =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          if (stmt.modifies.nonEmpty) {
            return evalWhile(state, stmt)
          } else {
            if (!config.unroll) {
              error(stmt.posOpt, "Modifies clause is required when loop unrolling is disabled", reporter)
              return ISZ(state(status = F))
            }
            return evalWhileUnroll(split, state, stmt)
          }
        case stmt: AST.Stmt.For =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          if (stmt.modifies.nonEmpty) {
            return evalFor(state, stmt)
          } else {
            halt("TODO") // TODO
          }
        case stmt: AST.Stmt.Return =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalReturn(state, stmt)
        case stmt: AST.Stmt.Block => return evalBlock(split, smt2, None(), rtCheck, state, stmt, reporter)
        case stmt: AST.Stmt.SpecBlock => return evalSpecBlock(split, state, stmt)
        case stmt: AST.Stmt.Match => return evalMatch(split, smt2, None(), rtCheck, state, stmt, reporter)
        case stmt: AST.Stmt.Inv => return evalInv(state, stmt)
        case stmt: AST.Stmt.DeduceSteps => return evalDeduceSteps(state, stmt)
        case stmt: AST.Stmt.DeduceSequent if stmt.justOpt.isEmpty => return evalDeduceSequent(state, stmt)
        case _: AST.Stmt.Object => return ISZ(state)
        case _: AST.Stmt.Import => return ISZ(state)
        case _: AST.Stmt.Method => return ISZ(state)
        case _: AST.Stmt.SpecMethod => return ISZ(state)
        case stmt: AST.Stmt.Var if stmt.isSpec => return ISZ(state)
        case _: AST.Stmt.SpecVar => return ISZ(state)
        case _: AST.Stmt.Enum => return ISZ(state)
        case _: AST.Stmt.Adt => return ISZ(state)
        case _: AST.Stmt.Sig => return ISZ(state)
        case _: AST.Stmt.TypeAlias => return ISZ(state)
        case _ =>
          halt(s"TODO: $stmt") // TODO
      }
    }

    def checkSplits(): ISZ[State] = {
      val ss = evalStmtH()
      assert(ss.size > 0)
      var nextFresh: Z = -1
      for (s <- ss if nextFresh == -1) {
        if (s.status) {
          nextFresh = s.nextFresh
        }
      }
      assert(ss.size == 1 || ops.ISZOps(ss).forall((s: State) => !s.status || nextFresh == s.nextFresh))
      return ss
    }

    return extension.Cancel.cancellable(checkSplits _)
  }

  def logPc(enabled: B, raw: B, state: State, reporter: Reporter, posOpt: Option[Position]): Unit = {
    reporter.state(posOpt, state)
    if (enabled || raw) {
      val sts: ISZ[ST] =
        if (raw) State.Claim.claimsRawSTs(state.claims)
        else State.Claim.claimsSTs(state.claims, ClaimDefs.empty)
      if (sts.isEmpty) {
        reporter.info(posOpt, Logika.kind, "Path conditions = {}")
      } else {
        reporter.info(posOpt, Logika.kind,
          st"""Path conditions = {
              |      ${(sts, ",\n")}
              |    }""".
            render
        )
      }
    }
  }

  def evalTypeTestH(s0: State, v: State.Value, t: AST.Typed, pos: Position): (State, State.Value) = {
    t match {
      case t: AST.Typed.Name if t.ids != AST.Typed.isName && t.ids != AST.Typed.msName =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        th.typeMap.get(t.ids).get match {
          case ti: TypeInfo.Adt => return (s1.addClaim(State.Claim.Let.TypeTest(cond, !ti.ast.isRoot, v, t)), cond)
          case _: TypeInfo.Sig => return (s1.addClaim(State.Claim.Let.TypeTest(cond, F, v, t)), cond)
          case _ =>
        }
      case _ =>
    }
    assert(v.tipe == t)
    return (s0, State.Value.B(T, pos))
  }

  def checkExp(split: Split.Type, smt2: Smt2, rtCheck: B, title: String, titleSuffix: String, s0: State, exp: AST.Exp, reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    for (p <- evalExp(split, smt2, rtCheck, s0, exp, reporter)) {
      val (s1, v) = p
      val pos = exp.posOpt.get
      val (s2, sym) = value2Sym(s1, v, pos)
      val prop = State.Claim.Prop(T, sym)
      val rvalid = smt2.valid(config.logVc, config.logVcDirOpt, s"$title$titleSuffix at [${pos.beginLine}, ${pos.beginColumn}]",
        pos, s2.claims, prop, reporter)
      var ok = F
      rvalid.kind match {
        case Smt2Query.Result.Kind.Unsat => ok = T
        case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
        case Smt2Query.Result.Kind.Unknown => error(Some(pos), s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds$titleSuffix", reporter)
        case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
        case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
      }
      if (ok) {
        r = r :+ s2.addClaim(prop)
      } else {
        r = r :+ s2(status = F, claims = s2.claims :+ prop)
      }
    }
    return r
  }

  def checkExps(split: Split.Type, smt2: Smt2, rtCheck: B, title: String, titleSuffix: String, s0: State, exps: ISZ[AST.Exp], reporter: Reporter): ISZ[State] = {
    var currents = ISZ(s0)
    var done = ISZ[State]()
    for (exp <- exps) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.status) {
          currents = currents ++ checkExp(split, smt2, rtCheck, title, titleSuffix, current, exp, reporter)
        } else {
          done = done :+ current
        }
      }
    }
    return currents ++ done
  }

  def mergeStates(s0: State, cond: State.Value.Sym, sT: State, sF: State, nextFresh: Z): State = {
    @pure def mergeClaimPrefix(tClaim: State.Claim, fClaim: State.Claim): State.Claim = {
      return if (tClaim == fClaim) tClaim else State.Claim.If(cond, ISZ(tClaim), ISZ(fClaim))
    }

    val size = s0.claims.size
    val prefixClaims: ISZ[State.Claim] =
      for (i <- 0 until size) yield mergeClaimPrefix(sT.claims(i), sF.claims(i))
    return State(s0.status, prefixClaims :+
      State.Claim.If(cond, ops.ISZOps(sT.claims).drop(size + 1),
        ops.ISZOps(sF.claims).drop(size + 1)), nextFresh)
  }

  def evalStmts(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, state: State, stmts: ISZ[AST.Stmt],
                reporter: Reporter): ISZ[State] = {
    var currents = ISZ(state)
    var done = ISZ[State]()

    val size: Z = if (rOpt.nonEmpty) stmts.size - 1 else stmts.size
    for (i <- 0 until size) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.status) {
          currents = currents ++ evalStmt(split, smt2, rtCheck, current, stmts(i), reporter)
        } else {
          done = done :+ current
        }
      }
    }

    if (rOpt.nonEmpty) {
      return (for (current <- currents;
                   s <- evalAssignExp(split, smt2, rOpt, rtCheck, current, stmts(stmts.size - 1).asAssignExp, reporter))
      yield s) ++ done
    } else {
      return currents ++ done
    }
  }

  def evalBody(split: Split.Type, smt2: Smt2, rOpt: Option[State.Value.Sym], rtCheck: B, state: State, body: AST.Body,
               posOpt: Option[Position], reporter: Reporter): ISZ[State] = {
    val s0 = state
    var r = ISZ[State]()
    for (s1 <- evalStmts(split, smt2, rOpt, rtCheck, s0, body.stmts, reporter)) {
      if (s1.status) {
        r = r :+ Logika.rewriteLocalVars(th, F, s1, body.undecls, posOpt, reporter)
      } else {
        r = r :+ s1
      }
    }
    return r
  }

  @pure def singleStateValue(ps: ISZ[(State, State.Value)]): (State, State.Value) = {
    assert(ps.size == 1)
    return ps(0)
  }

  @pure def singleState(ss: ISZ[State]): State = {
    assert(ss.size == 1)
    return ss(0)
  }

  @pure def maxStatesNextFresh(ss: ISZ[State]): Z = {
    var r = ss(0).nextFresh
    if (ss.size > 1) {
      for (i <- 1 until ss.size) {
        val nf = ss(i).nextFresh
        if (r < nf) {
          r = nf
        }
      }
    }
    return r
  }

  @pure def maxStateValuesNextFresh(svs: ISZ[(State, State.Value)]): Z = {
    var r = svs(0)._1.nextFresh
    if (svs.size > 1) {
      for (i <- 1 until svs.size) {
        val nf = svs(i)._1.nextFresh
        if (r < nf) {
          r = nf
        }
      }
    }
    return r
  }

  def error(posOpt: Option[Position], msg: String, reporter: Reporter): Unit = {
    if (context.caseLabels.nonEmpty) {
      reporter.error(posOpt, Logika.kind, st"[${(for (l <- context.caseLabels) yield l.value, "; ")}] $msg".render)
    } else {
      reporter.error(posOpt, Logika.kind, msg)
    }
  }

  def warn(posOpt: Option[Position], msg: String, reporter: Reporter): Unit = {
    if (context.caseLabels.nonEmpty) {
      reporter.warn(posOpt, Logika.kind, st"[${(for (l <- context.caseLabels) yield l.value, "; ")}] $msg".render)
    } else {
      reporter.warn(posOpt, Logika.kind, msg)
    }
  }

}
