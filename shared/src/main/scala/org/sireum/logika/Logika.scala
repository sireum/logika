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

package org.sireum.logika

import org.sireum._
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.symbol.Resolver.{NameMap, QName, TypeMap}
import org.sireum.lang.{ast => AST}
import org.sireum.message.Position
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.plugin._
import org.sireum.lang.tipe.TypeOutliner.ExpTypedSubst
import org.sireum.logika.options.OptionsUtil

object Logika {

  @enum object Split {
    "Default"
    "Enabled"
    "Disabled"
  }

  type Bindings = Map[String, (State.Value.Sym, AST.Typed, Position)]

  type LeafClaims = ISZ[(State.Claim, ISZ[(State.Status.Type, ISZ[State.Claim])])]

  type Assignment = ISZ[B]

  @datatype class Branch(val title: String,
                         val sym: State.Value.Sym,
                         val body: AST.Body,
                         val bindings: Bindings,
                         val bindingIdMap: HashMap[String, (Z, ISZ[Position])])

  @datatype class PathConditions(val th: TypeHierarchy, val value: ISZ[AST.Exp]) {
    @memoize def normalize: ISZ[AST.Exp] = {
      return for (e <- value) yield th.normalizeExp(e)
    }
  }


  @msig trait Cache {
    def clearTransition(): Unit

    def getTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, transition: Cache.Transition, context: ISZ[String], state: State, smt2: Smt2): Option[(ISZ[State], U64)]

    def setTransition(th: TypeHierarchy, config: Config, transition: Cache.Transition, context: ISZ[String], state: State, nextStates: ISZ[State], smt2: Smt2): U64

    def getAssignExpTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, exp: AST.AssignExp, context: ISZ[String], state: State, smt2: Smt2): Option[(ISZ[(State, State.Value)], U64)]

    def setAssignExpTransition(th: TypeHierarchy, config: Config, exp: AST.AssignExp, context: ISZ[String], state: State, nextStatesValues: ISZ[(State, State.Value)], smt2: Smt2): U64

    def getSmt2(isSat: B, th: TypeHierarchy, config: Config, timeoutInMs: Z, claims: ISZ[State.Claim]): Option[Smt2Query.Result]

    def setSmt2(isSat: B, th: TypeHierarchy, config: Config, timeoutInMs: Z, claims: ISZ[State.Claim], result: Smt2Query.Result): Unit

    def getPatterns(th: TypeHierarchy, isInObject: B, name: ISZ[String]): Option[ISZ[RewritingSystem.Rewriter.Pattern]]

    def setPatterns(th: TypeHierarchy, isInObject: B, name: ISZ[String], patterns: ISZ[RewritingSystem.Rewriter.Pattern]): Unit

    def keys: ISZ[Cache.Key]

    def getValue(key: Cache.Key): Option[Cache.Value]

    def setValue(key: Cache.Key, value: Cache.Value): Unit

    def clearValue(key: Cache.Key): Unit

    def taskKeys: ISZ[Cache.Key]

    def getTaskValue(key: Cache.Key): Option[Cache.Value]

    def setTaskValue(key: Cache.Key, value: Cache.Value): Unit

    def clearTaskValue(key: Cache.Key): Unit

  }

  object Cache {
    @sig trait Transition {
      @strictpure def toST: ST
    }

    object Transition {

      @datatype class Stmt(stmt: AST.Stmt) extends Transition {
        @strictpure override def toST: ST = stmt.prettyST
      }

      @datatype class Stmts(stmts: ISZ[AST.Stmt]) extends Transition {
        @strictpure override def toST: ST = st"{ ${(for (stmt <- stmts) yield stmt.prettyST, "; ")} }"
      }

      @datatype class ProofStep(step: AST.ProofAst.Step.Regular, spcs: ISZ[StepProofContext]) extends Transition {
        @strictpure override def toST: ST = st"${step.prettyST}"
      }

      @datatype class Sequent(sequent: AST.Sequent) extends Transition {
        @strictpure override def toST: ST = sequent.prettyST
      }

      @datatype class Exp(exp: AST.Exp) extends Transition {
        @strictpure override def toST: ST = exp.prettyST
      }

      @datatype class Exps(exps: ISZ[AST.Exp]) extends Transition {
        @strictpure override def toST: ST = st"{ ${(for (exp <- exps) yield exp.prettyST, "; ")} }"
      }

      @datatype class StmtExps(stmt: AST.Stmt, exps: ISZ[AST.Exp]) extends Transition {
        @strictpure override def toST: ST = st"{ ${stmt.prettyST}; ${(for (exp <- exps) yield exp.prettyST, "; ")} }"
      }
    }

    @sig trait Key

    @sig trait Value
  }

  object Reporter {
    object Info {
      @enum object Kind {
        "Verified"
        "Error"
      }
    }
  }

  @msig trait Reporter extends message.Reporter {
    def numOfVCs: Z
    def numOfSats: Z
    def vcMillis: Z
    def satMillis: Z

    def state(plugins: ISZ[logika.plugin.ClaimPlugin], posOpt: Option[Position], context: ISZ[String],
              th: TypeHierarchy, s: State, atLinesFresh: B, atRewrite: B): Unit

    def query(pos: Position, title: String, isSat: B, time: Z, forceReport: B, detailElided:B, r: Smt2Query.Result): Unit

    def inform(pos: Position, kind: Reporter.Info.Kind.Type, message: String): Unit

    def coverage(setCache: B, cached: U64, pos: Position): Unit

    def empty: Reporter

    def combine(other: Reporter): Reporter

    def illFormed(): Unit
  }

  val kind: String = "Logika"
  val parsingDesc: String = "Parsing"
  val libraryDesc: String = "Library"
  val typeCheckingDesc: String = "Type Checking"
  val verifyingDesc: String = "Verifying"
  val defaultPlugins: ISZ[Plugin] = ISZ(AutoPlugin(), RewritePlugin(), PropNatDedPlugin(), PredNatDedPlugin(),
    SubstitutionPlugin(), ClaimOfPlugin(), FoldUnfoldPlugin(), SameDiffPlugin(), Smt2Plugin(), ValIntroElimPlugin(),
    LiftPlugin(), AdmitPlugin(), InceptionPlugin()
  )
  val builtInByNameMethods: HashSet[(B, QName, String)] = HashSet ++ ISZ(
    (F, AST.Typed.isName, "size"), (F, AST.Typed.msName, "size"),
    (F, AST.Typed.isName, "firstIndex"), (F, AST.Typed.msName, "firstIndex"),
    (F, AST.Typed.isName, "lastIndex"), (F, AST.Typed.msName, "lastIndex"),
    (F, AST.Typed.f32Name, "isNaN"), (F, AST.Typed.f32Name, "isInfinite"),
    (F, AST.Typed.f64Name, "isNaN"), (F, AST.Typed.f64Name, "isInfinite")
  )
  val indexingFields: HashSet[String] = HashSet ++ ISZ[String]("firstIndex", "lastIndex")
  val emptyBindings: Bindings = Map.empty[String, (State.Value.Sym, AST.Typed, Position)]
  val trueClaim: State.Claim = State.Claim.And(ISZ())
  val idxSuffix: String = "$Idx"
  val zeroU64: U64 = org.sireum.U64.fromZ(0)

  def checkStmts(nameExePathMap: HashMap[String, String], maxCores: Z, fileOptions: LibUtil.FileOptionMap,
                 initStmts: ISZ[AST.Stmt], typeStmts: ISZ[(ISZ[String], AST.Stmt)], defaultConfig: Config,
                 th: TypeHierarchy, smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Logika.Cache, reporter: Reporter,
                 par: Z, plugins: ISZ[Plugin], verifyingStartTime: Z, includeInit: B, line: Z, skipMethods: ISZ[String],
                 skipTypes: ISZ[String]): Unit = {
    var sourceConfigMap = HashMap.empty[Option[String], Config]
    for (p <- fileOptions.entries) {
      val (fileUriOpt, m) = p
      m.get(OptionsUtil.logika) match {
        case Some(options) =>
          OptionsUtil.toConfig(defaultConfig, maxCores, "file", nameExePathMap, options) match {
            case Either.Left(c) => sourceConfigMap = sourceConfigMap + fileUriOpt ~> c
            case Either.Right(msgs) =>
              for (msg <- msgs) {
                reporter.error(None(), Logika.kind, msg)
              }
          }
        case _ =>
      }
    }
    if (reporter.hasError) {
      return
    }

    var noMethodIds = HashSet.empty[String]
    var noMethodNames = HashSet.empty[String]
    var noTypeIds = HashSet.empty[String]
    var noTypeNames = HashSet.empty[String]
    for (m <- skipMethods) {
      if (ops.StringOps(m).contains(".")) {
        noMethodNames = noMethodNames + m
      } else {
        noMethodIds = noMethodIds + m
      }
    }
    for (t <- skipTypes) {
      if (ops.StringOps(t).contains(".")) {
        noTypeNames = noTypeNames + t
      } else {
        noTypeIds = noTypeIds + t
      }
    }
    def noMethods(owner: ISZ[String], id: String): B = {
      return noMethodIds.contains(id) || noMethodNames.contains(st"${(owner :+ id, ".")}".render)
    }
    def noTypes(owner: ISZ[String], id: String): B = {
      return noTypeIds.contains(id) || noTypeNames.contains(st"${(owner :+ id, ".")}".render)
    }
    var taskMap = HashSMap.empty[(Z, Z), ISZ[Task]]
    def rec(ownerPosOpt: Option[(Z, Z)], owner: ISZ[String], stmts: ISZ[AST.Stmt]): Unit = {
      var ownerTasks = ISZ[Task]()
      var config = defaultConfig
      var configInit = F
      for (stmt <- stmts) {
        if (!configInit) {
          configInit = T
          stmt.posOpt match {
            case Some(pos) =>
              sourceConfigMap.get(pos.uriOpt) match {
                case Some(c) => config = c
                case _ =>
              }
            case _ =>
          }
        }
        stmt match {
          case stmt: AST.Stmt.Fact if config.sat =>
            if (ownerPosOpt.nonEmpty) {
              ownerTasks = ownerTasks :+ Task.Fact(th, config, stmt, plugins)
            } else {
              val pos = stmt.posOpt.get
              val ownerPos = (pos.beginLine, pos.beginColumn)
              val tasks: ISZ[Task] = taskMap.get(ownerPos) match {
                case Some(ts) => ts
                case _ => ISZ()
              }
              taskMap = taskMap + ownerPos ~> (tasks :+ Task.Fact(th, config, stmt, plugins))
            }
          case stmt: AST.Stmt.Theorem =>
            if (ownerPosOpt.nonEmpty) {
              ownerTasks = ownerTasks :+ Task.Theorem(th, config, stmt, plugins)
            } else {
              val pos = stmt.posOpt.get
              val ownerPos = (pos.beginLine, pos.beginColumn)
              val tasks: ISZ[Task] = taskMap.get(ownerPos) match {
                case Some(ts) => ts
                case _ => ISZ()
              }
              taskMap = taskMap + ownerPos ~> (tasks :+ Task.Theorem(th, config, stmt, plugins))
            }
          case stmt: AST.Stmt.Method if stmt.bodyOpt.nonEmpty && !noMethods(owner, stmt.sig.id.value) &&
            !(stmt.isHelper && stmt.contract.isEmpty) =>
            if (ownerPosOpt.nonEmpty) {
              stmt.mcontract match {
                case contract: AST.MethodContract.Cases if contract.cases.size > 1 =>
                  ownerTasks = ownerTasks ++
                    (for (i <- 0 until contract.cases.size) yield Task.Method(par, th, config, stmt, i, plugins).
                      asInstanceOf[Task])
                case _ =>
                  ownerTasks = ownerTasks :+ Task.Method(par, th, config, stmt, -1, plugins)
              }
            } else {
              val pos = stmt.posOpt.get
              val ownerPos = (pos.beginLine, pos.beginColumn)
              val tasks: ISZ[Task] = taskMap.get(ownerPos) match {
                case Some(ts) => ts
                case _ => ISZ()
              }
              stmt.mcontract match {
                case contract: AST.MethodContract.Cases if contract.cases.size > 1 =>
                  taskMap = taskMap + ownerPos ~> (tasks ++
                    (for (i <- 0 until contract.cases.size) yield Task.Method(par, th, config, stmt, i, plugins).
                      asInstanceOf[Task]))
                case _ =>
                  taskMap = taskMap + ownerPos ~> (tasks :+ Task.Method(par, th, config, stmt, -1, plugins))
              }
            }
          case stmt: AST.Stmt.Object if !noTypes(owner, stmt.id.value) =>
            val pos = stmt.posOpt.get
            rec(Some((pos.beginLine, pos.endLine)), owner :+ stmt.id.value, stmt.stmts)
          case stmt: AST.Stmt.Adt if !noTypes(owner, stmt.id.value) =>
            val pos = stmt.posOpt.get
            rec(Some((pos.beginLine, pos.endLine)), owner :+ stmt.id.value, stmt.stmts)
          case stmt: AST.Stmt.Sig if !noTypes(owner, stmt.id.value) =>
            val pos = stmt.posOpt.get
            rec(Some((pos.beginLine, pos.endLine)), owner :+ stmt.id.value, stmt.stmts)
          case _ =>
        }
      }
      if (ownerTasks.nonEmpty) {
        taskMap = taskMap + ownerPosOpt.get ~> ownerTasks
      }
    }

    rec(None(), ISZ(), initStmts)
    for (p <- typeStmts) {
      rec(None(), p._1, ISZ(p._2))
    }

    def findTasks(): ISZ[Task] = {
      def findMethodFactTasks(): ISZ[Task] = {
        var r = ISZ[Task]()
        if (line <= 0) {
          return r
        }
        for (ts <- taskMap.values; t <- ts) {
          t match {
            case t: Task.Method =>
              val pos = t.method.posOpt.get
              if (pos.beginLine <= line && line <= pos.endLine) {
                r = r :+ t
              }
            case t: Task.Fact =>
              val pos = t.fact.posOpt.get
              if (pos.beginLine <= line && line <= pos.endLine) {
                r = r :+ t
              }
            case t: Task.Theorem =>
              val pos = t.theorem.posOpt.get
              if (pos.beginLine <= line && line <= pos.endLine) {
                r = r :+ t
              }
            case _ =>
          }
        }
        return r
      }
      def findOwnerTasks(): ISZ[Task] = {
        if (line <= 0) {
          return ISZ()
        }
        for (p <- taskMap.entries) {
          val (pos, ts) = p
          if (pos._1 <= line && line <= pos._2) {
            return ts
          }
        }
        return ISZ()
      }
      var r = findMethodFactTasks()
      if (r.nonEmpty) {
        return r
      }
      r = findOwnerTasks()
      if (r.nonEmpty) {
        return r
      }
      r = for (ts <- taskMap.values; t <- ts) yield t
      if (includeInit) {
        var config = defaultConfig
        if (initStmts.nonEmpty) {
          initStmts(0).posOpt match {
            case Some(pos) =>
              sourceConfigMap.get(pos.uriOpt) match {
                case Some(c) => config = c
                case _ =>
              }
            case _ =>
          }
        }
        r = Task.Stmts(th, config, initStmts, plugins) +: r
      }
      return r
    }

    val tasks = findTasks()

    val smt2 = smt2f(th)

    def compute(task: Task): B = {
      val r = reporter.empty
      val csmt2 = smt2
      task.compute(nameExePathMap, maxCores, fileOptions, csmt2, cache, r)
      reporter.combine(r)
      return T
    }

    extension.Cancel.cancellable { () =>
      ops.ISZOps(tasks).mParMapCores[B](compute _, par)
    }
    if (verifyingStartTime != 0) {
      reporter.timing(verifyingDesc, extension.Time.currentMillis - verifyingStartTime)
    }
  }

  def checkScript(fileUriOpt: Option[String], input: String, config: Config, nameExePathMap: HashMap[String, String],
                  maxCores: Z, smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Logika.Cache, reporter: Reporter,
                  hasLogika: B, plugins: ISZ[Plugin], line: Z,
                  skipMethods: ISZ[String], skipTypes: ISZ[String]): Unit = {
    val parsingStartTime = extension.Time.currentMillis
    val isWorksheet: B = fileUriOpt match {
      case Some(p) => !ops.StringOps(p).endsWith(".scala") && !ops.StringOps(p).endsWith(".slang")
      case _ => T
    }

    def checkScriptH(): Unit = {
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
            lang.FrontEnd.checkWorksheet(config.parCores, Some(tc.typeHierarchy), program, reporter))
          if (!reporter.hasError) {
            lang.tipe.PostTipeAttrChecker.checkProgram(p, reporter)
          }
          val verifyingStartTime = extension.Time.currentMillis
          reporter.timing(typeCheckingDesc, verifyingStartTime - typeCheckingStartTime)

          if (!reporter.hasError) {
            if (hasLogika) {
              if (config.transitionCache || config.smt2Caching) {
                val dummy: U64 = if (config.interp) th.fingerprintKeepMethodBody else th.fingerprintNoMethodBody // init fingerprint
                val dummy2 = config.fingerprint
              }

              var fileOptions: LibUtil.FileOptionMap = HashMap.empty
              fileOptions = fileOptions + fileUriOpt ~> LibUtil.mineOptions(input)
              checkStmts(nameExePathMap, maxCores, fileOptions, p.body.stmts, ISZ(), config, th, smt2f, cache, reporter,
                config.parCores, plugins, verifyingStartTime, T, line, skipMethods, skipTypes)
              if (reporter.hasError) {
                reporter.illFormed()
              }
            }
          } else {
            reporter.illFormed()
          }
        case Some(tt: AST.TopUnit.TruthTableUnit) =>
          Logika.checkTruthTable(tt, reporter)
          if (reporter.hasError) {
            reporter.illFormed()
          }
        case _ =>
      }
    }

    extension.Cancel.cancellable(checkScriptH _)
  }

  @pure def shouldCheck(fileSet: HashSSet[String], line: Z, posOpt: Option[Position]): B = {
    posOpt match {
      case Some(pos) => pos.uriOpt match {
        case Some(uri) if fileSet.contains(uri) =>
          if (line > 0) {
            return pos.beginLine <= line && line <= pos.endLine
          } else {
            return T
          }
        case _ =>
      }
      case _ =>
    }
    return F
  }

  def checkPrograms(sources: ISZ[(Option[String], String)], files: ISZ[String], config: Config,
                    nameExePathMap: HashMap[String, String], maxCores: Z, th: TypeHierarchy,
                    smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Logika.Cache, reporter: Reporter,
                    strictAliasing: B, sanityCheck: B, plugins: ISZ[Plugin], line: Z, skipMethods: ISZ[String],
                    skipTypes: ISZ[String]): Unit = {
    val parsingStartTime = extension.Time.currentMillis
    val (rep, _, nameMap, typeMap) = extension.Cancel.cancellable(() =>
      lang.FrontEnd.parseProgramAndGloballyResolve(config.parCores, for (p <- sources) yield lang.FrontEnd.Input(p._2, p._1),
        th.nameMap, th.typeMap))
    reporter.reports(rep.messages)
    val typeCheckingStartTime = extension.Time.currentMillis
    reporter.timing(parsingDesc, typeCheckingStartTime - parsingStartTime)
    if (reporter.hasError) {
      reporter.illFormed()
      return
    }
    val th2 = extension.Cancel.cancellable(() =>
      TypeHierarchy.build(F, th(nameMap = nameMap, typeMap = typeMap), reporter))
    if (reporter.hasError) {
      reporter.illFormed()
      return
    }
    val th3 = extension.Cancel.cancellable(() =>
      lang.tipe.TypeOutliner.checkOutline(config.parCores, strictAliasing, th2, reporter))
    if (reporter.hasError) {
      reporter.illFormed()
      return
    }
    val fileSet: HashSSet[String] = HashSSet ++ files
    @pure def filterNameMap(map: lang.symbol.Resolver.NameMap): lang.symbol.Resolver.NameMap = {
      var r: NameMap = HashSMap.empty
      for (info <- map.values) {
        info match {
          case info: Info.Object if shouldCheck(fileSet, line, info.posOpt) => r = r + info.name ~> info
          case _ =>
        }
      }
      return r
    }
    @pure def filterTypeMap(map: lang.symbol.Resolver.TypeMap): lang.symbol.Resolver.TypeMap = {
      var r: TypeMap = HashSMap.empty
      for (info <- map.values) {
        info match {
          case info: TypeInfo.Adt if shouldCheck(fileSet, line, info.posOpt) => r = r + info.name ~> info
          case info: TypeInfo.Sig if shouldCheck(fileSet, line, info.posOpt) => r = r + info.name ~> info
          case _ =>
        }
      }
      return r
    }
    val th4 = extension.Cancel.cancellable(() =>
      TypeChecker.checkComponents(config.parCores, strictAliasing, th3, filterNameMap(th3.nameMap), filterTypeMap(th3.typeMap), reporter))
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

    checkTypedPrograms(verifyingStartTime, fileSet, config, nameExePathMap, maxCores, th4, smt2f, cache, reporter,
      config.parCores, plugins, line, skipMethods, skipTypes, sources)
  }

  def checkTypedPrograms(verifyingStartTime: Z, fileSet: HashSSet[String], config: Config,
                         nameExePathMap: HashMap[String, String], maxCores: Z, th: TypeHierarchy,
                         smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Logika.Cache, reporter: Reporter, par: Z,
                         plugins: ISZ[Plugin], line: Z, skipMethods: ISZ[String], skipTypes: ISZ[String],
                         sources: ISZ[(Option[String], String)]): Unit = {
    if (config.transitionCache || config.smt2Caching) {
      val dummy: U64 = if (config.interp) th.fingerprintKeepMethodBody else th.fingerprintNoMethodBody // init fingerprint
      val dummy2 = config.fingerprint
    }
    var typeStmts = ISZ[(ISZ[String], AST.Stmt)]()
    for (info <- th.nameMap.values) {
      info match {
        case info: Info.Object if shouldCheck(fileSet, line, info.posOpt) => typeStmts = typeStmts :+ ((info.owner, info.ast))
        case _ =>
      }
    }
    for (info <- th.typeMap.values) {
      info match {
        case info: TypeInfo.Adt if shouldCheck(fileSet, line, info.posOpt) => typeStmts = typeStmts :+ ((info.owner, info.ast))
        case info: TypeInfo.Sig if shouldCheck(fileSet, line, info.posOpt) => typeStmts = typeStmts :+ ((info.owner, info.ast))
        case _ =>
      }
    }

    var fileOptions: LibUtil.FileOptionMap = HashMap.empty
    fileOptions = fileOptions ++ (for (p <- sources) yield (p._1, LibUtil.mineOptions(p._2)))
    checkStmts(nameExePathMap, maxCores, fileOptions, ISZ(), typeStmts, config, th, smt2f, cache, reporter, par, plugins,
      verifyingStartTime, F, line, skipMethods, skipTypes)
  }

  def checkTruthTable(tt: AST.TopUnit.TruthTableUnit, reporter: Reporter): Unit = {
    val vs: Assignment = ISZ(T, F)

    def checkStarPositionsForm(): Unit = {
      val varSet: HashSet[String] = {
        var r = HashSet.empty[String]
        for (id <- tt.vars) {
          val x = id.value
          if (r.contains(x)) {
            reporter.error(id.attr.posOpt, kind, s"Redeclaration of '$x'.")
          } else {
            r = r + x
          }
        }
        r
      }

      def checkExp(e: AST.Exp): Unit = {
        var hasError = F
        e match {
          case _: AST.Exp.LitB =>
          case e: AST.Exp.Ident =>
            val x = e.id.value
            if (!varSet.contains(x)) {
              reporter.error(e.posOpt, kind, s"Undeclared usage '$x'.")
            }
          case e: AST.Exp.Binary =>
            e.op match {
              case AST.Exp.BinaryOp.And =>
              case AST.Exp.BinaryOp.Or =>
              case "->:" =>
              case _ => hasError = T
            }
            checkExp(e.left)
            checkExp(e.right)
          case e: AST.Exp.Unary =>
            e.op match {
              case AST.Exp.UnaryOp.Not =>
              case AST.Exp.UnaryOp.Complement =>
              case _ => hasError = T
            }
            checkExp(e.exp)
          case _ => hasError = T
        }
        if (hasError) {
          reporter.error(e.posOpt, kind, "Unallowable expression in truth table.")
        }
      }

      var i = 0
      val stars: ISZ[Position] = tt.stars
      for (e <- tt.sequent.premises :+ tt.sequent.conclusion) {
        if (i < stars.size) {
          val posOpt = Some(stars(i))
          if (!AST.Util.beginColumnEqual(posOpt, e.posOpt)) {
            reporter.error(posOpt, kind, "Invalid * position.")
          }
        } else {
          reporter.error(e.posOpt, kind, "No associated * found.")
        }
        checkExp(e)
        i = i + 1
      }
    }

    def checkRowAssignments(): B = {
      @pure def allAssignments(i: Z, keys: ISZ[String], ss: ISZ[Assignment]): ISZ[Assignment] = {
        if (i >= keys.size) {
          return ss
        }
        return allAssignments(i + 1, keys, for (s <- ss; v <- vs) yield s :+ v)
      }
      @strictpure def a2s(a: Assignment): String = st"[${(for (e <- a) yield if (e) "T" else "F", "")}]".render

      val vars: ISZ[String] = for (id <- tt.vars) yield id.value
      val assignments = Set ++ allAssignments(0, vars, ISZ(ISZ()))
      var currentAssignments = assignments
      for (row <- tt.rows) {
        val ra: ISZ[AST.Exp.LitB] = row.assignment.values
        if (ra.size != vars.size) {
          reporter.error(row.assignment.attr.posOpt, kind, "Invalid number of truth assignment values.")
        }
        if (tt.separator.beginColumn != row.separator.beginColumn) {
          reporter.error(Some(row.separator), kind, "Invalid separator position.")
        }
        val rowAssignment: Assignment = for (b <- ra) yield b.value
        if (!assignments.contains(rowAssignment)) {
          reporter.error(row.assignment.attr.posOpt, kind, s"Invalid truth assignment ${a2s(rowAssignment)}.")
        } else {
          if (currentAssignments.contains(rowAssignment)) {
            currentAssignments = currentAssignments - rowAssignment
          } else {
            reporter.error(row.assignment.attr.posOpt, kind, s"Duplicated truth assignment ${a2s(rowAssignment)}.")
          }
        }
      }
      if (currentAssignments.nonEmpty) {
        reporter.error(None(), kind, "There are still missing truth assignments.")
      }
      return currentAssignments.isEmpty
    }

    def checkAssignments(): (ISZ[Assignment], ISZ[Assignment]) = {
      def buildStore(assignment: ISZ[AST.Exp.LitB]): HashMap[String, B] = {
        val vars: ISZ[AST.Id] = tt.vars
        val size = vars.size
        var store = HashMap.emptyInit[String, B](size)
        for (i <- 0 until size) {
          val x = vars(i)
          val v = assignment(i)
          if (!AST.Util.beginColumnEqual(x.attr.posOpt, v.attr.posOpt)) {
            reporter.error(v.attr.posOpt, kind, "Invalid asssignment position.")
          }
          store = store + x.value ~> v.value
        }
        return store
      }

      var tas: ISZ[Assignment] = ISZ()
      var fas: ISZ[Assignment] = ISZ()

      for (row <- tt.rows) {
        val ra: ISZ[AST.Exp.LitB] = row.assignment.values
        val store = buildStore(ra)
        var resultMap = HashMap.empty[Z, (B, B)]

        def evalExp(e: AST.Exp): B = {
          def putResult(v: B, opt: B): Unit = {
            resultMap = resultMap + AST.Util.beginColumn(e.posOpt) ~> ((v, opt))
          }

          e match {
            case e: AST.Exp.Ident =>
              val r = store.get(e.id.value).getOrElse(F)
              putResult(r, T)
              return r
            case e: AST.Exp.Binary =>
              val r: B = e.op match {
                case AST.Exp.BinaryOp.And => evalExp(e.left) & evalExp(e.right)
                case AST.Exp.BinaryOp.Or => evalExp(e.left) | evalExp(e.right)
                case "->:" => !evalExp(e.left) | evalExp(e.right)
                case _ => halt(s"Infeasible: ${e.op}")
              }
              putResult(r, F)
              return r
            case e: AST.Exp.Unary =>
              val r: B =
                if (e.op == AST.Exp.UnaryOp.Not || e.op == AST.Exp.UnaryOp.Complement) !evalExp(e.exp)
                else F
              putResult(r, F)
              return r
            case _ => return F
          }
        }

        var p = T
        for (e <- tt.sequent.premises) {
          p = p & evalExp(e)
        }
        val c = evalExp(tt.sequent.conclusion)
        var rowValues: Assignment = ISZ[B]()
        var hasError = F
        for (b <- row.values.values) {
          val column = AST.Util.beginColumn(b.posOpt)
          resultMap.get(column) match {
            case Some(p@(v, _)) =>
              if (v != b.value) {
                hasError = T
              } else {
                rowValues = rowValues :+ v
              }
              resultMap = resultMap - ((column, p))
            case _ => reporter.error(b.posOpt, kind, "Invalid truth value position.")
          }
        }
        if (hasError) {
          reporter.error(row.values.attr.posOpt, kind, s"Some truth values are incorrect.")
        }
        var missing = F
        for (p <- resultMap.values if !p._2) {
          missing = T
        }
        if (missing) {
          reporter.error(row.values.attr.posOpt, kind, s"There are still some missing truth values.")
        }
        if ((tt.isSequent && p) || !tt.isSequent) {
          val rowAssignment: ISZ[B] = for (b <- ra) yield b.value
          if (c) {
            tas = tas :+ rowAssignment
          } else {
            fas = fas :+ rowAssignment
          }
        }
      }
      return (tas, fas)
    }

    def checkConclusion(tas: ISZ[Assignment], fas: ISZ[Assignment]): Unit = {
      tt.conclusionOpt match {
        case Some(conclusion) =>
          if (tt.isSequent) {
            conclusion match {
              case conclusion: AST.TruthTable.Conclusion.Validity =>
                var set: Set[Assignment] =
                  if (conclusion.isValid) {
                    if (fas.nonEmpty) {
                      reporter.error(conclusion.attr.posOpt, kind, "Incorrect summary.")
                    }
                    Set ++ tas
                  } else {
                    if (fas.isEmpty) {
                      reporter.error(conclusion.attr.posOpt, kind, "Incorrect summary.")
                    }
                    Set ++ fas
                  }
                for (a <- conclusion.assignments) {
                  val ra = a.values
                  val w: Assignment = for (b <- ra) yield b.value
                  if (!set.contains(w)) {
                    reporter.error(a.attr.posOpt, kind, s"Incorrect witness.")
                  } else {
                    set = set - w
                  }
                }
                if (set.nonEmpty) {
                  reporter.error(conclusion.attr.posOpt, kind, "There are still some missing witnesses.")
                }
              case _ =>
            }
          } else {
            conclusion match {
              case conclusion: AST.TruthTable.Conclusion.Tautology if fas.nonEmpty =>
                reporter.error(conclusion.attr.posOpt, kind, "Incorrect summary.")
              case conclusion: AST.TruthTable.Conclusion.Contingent =>
                var taSet = Set ++ tas
                var faSet = Set ++ fas
                for (a <- conclusion.trueAssignments) {
                  val ra = a.values
                  val w: Assignment = for (b <- ra) yield b.value
                  if (!taSet.contains(w)) {
                    reporter.error(a.attr.posOpt, kind, s"Incorrect summary witness.")
                  } else {
                    taSet = taSet - w
                  }
                }
                for (a <- conclusion.falseAssignments) {
                  val ra = a.values
                  val w: Assignment = for (b <- ra) yield b.value
                  if (!faSet.contains(w)) {
                    reporter.error(a.attr.posOpt, kind, s"Incorrect summary witness.")
                  } else {
                    faSet = faSet - w
                  }
                }
                if (taSet.nonEmpty || faSet.nonEmpty) {
                  reporter.error(conclusion.attr.posOpt, kind, "There are still some missing witnesses.")
                }
              case conclusion: AST.TruthTable.Conclusion.Contradictory if tas.nonEmpty =>
                reporter.error(conclusion.attr.posOpt, kind, "Incorrect summary.")
              case _ =>
            }
          }
        case _ =>
          if (tt.isSequent) {
            reporter.error(None(), kind, "Missing 'Valid' or 'Invalid' summary.")
          } else {
            reporter.error(None(), kind, "Missing 'Tautology', 'Contingent', or 'Contradictory' summary.")
          }
      }
    }

    checkStarPositionsForm()

    if (reporter.hasError) {
      return
    }

    val all = checkRowAssignments()

    if (reporter.hasError) {
      return
    }

    val (tas, fas) = checkAssignments()

    if (all && !reporter.hasError) {
      checkConclusion(tas, fas)
    }

    return
  }
}

import Logika._
import Util._

@datatype class Logika(val th: lang.tipe.TypeHierarchy,
                       val config: Config,
                       val context: Context,
                       val plugins: ISZ[Plugin]) {

  val jescmPlugins: (ISZ[plugin.JustificationPlugin], ISZ[plugin.ExpPlugin], ISZ[plugin.StmtPlugin], ISZ[plugin.ClaimPlugin], ISZ[plugin.MethodPlugin]) = {
    var jps = ISZ[plugin.JustificationPlugin]()
    var eps = ISZ[plugin.ExpPlugin]()
    var sps = ISZ[plugin.StmtPlugin]()
    var cps = ISZ[plugin.ClaimPlugin]()
    var mps = ISZ[plugin.MethodPlugin]()
    for (p <- plugins) {
      p match {
        case p: plugin.JustificationPlugin => jps = jps :+ p
        case p: plugin.ExpPlugin => eps = eps :+ p
        case p: plugin.StmtPlugin => sps = sps :+ p
        case p: plugin.ClaimPlugin => cps = cps :+ p
        case p: plugin.MethodPlugin => mps = mps :+ p
        case _: plugin.StmtsPlugin =>
        case _ => halt(s"Unexpected plugin: $p")
      }
    }
    (jps, eps, sps, cps, mps)
  }

  @strictpure def isAuto: B = config.isAuto
  @strictpure def isManual: B = !config.isAuto

  def zero(tipe: AST.Typed.Name, pos: Position): State.Value = {
    tipe match {
      case AST.Typed.z => return State.Value.Z(0, pos)
      case AST.Typed.f32 => return State.Value.F32(0f, pos)
      case AST.Typed.f64 => return State.Value.F64(0d, pos)
      case AST.Typed.r => return State.Value.R(org.sireum.R("0").get, pos)
      case _ =>
        val ti = th.typeMap.get(tipe.ids).get.asInstanceOf[TypeInfo.SubZ]
        return z2SubZVal(ti, 0, pos)
    }
  }

  def valid(searchPc: B, smt2: Smt2, cache: Logika.Cache, title: String, pos: message.Position,
            premises: ISZ[State.Claim], conclusionOrs: ISZ[State.Claim], smt2Conclusion: State.Claim,
            reporter: Reporter): Either[AST.Exp, Smt2Query.Result] = {
    if (searchPc) {
      val claims = premises ++ conclusionOrs
      val cs2es = createClaimsToExps(jescmPlugins._4, pos, context.methodName, claims, th, F, T)
      val pcsOps = ops.ISZOps(cs2es.translate(claims))
      val pcs = HashSSet ++ pcsOps.dropRight(conclusionOrs.size)
      val normPCs = HashSet ++ PathConditions(th, pcs.elements).normalize
      val concOrs = pcsOps.takeRight(conclusionOrs.size)
      for (i <- 0 until conclusionOrs.size) {
        if (normPCs.contains(th.normalizeExp(concOrs(i)))) {
          return Either.Left(concOrs(i))
        }
      }
    }
    return Either.Right(smt2.valid(context.methodName, config, cache, T, title, pos, premises, smt2Conclusion, reporter))
  }

  def checkSeqIndexing(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, seq: State.Value, i: State.Value,
                       posOpt: Option[Position], reporter: Reporter): State = {
    if (!rtCheck || !s0.ok) {
      return s0
    }
    val pos = posOpt.get
    if (isManual || config.searchPc && i.tipe == AST.Typed.z) { // TODO: add support for non-Z index
      val (s1, size) = s0.freshSym(AST.Typed.z, pos)
      val (s2, loCond) = s1.freshSym(AST.Typed.b, pos)
      val (s3, hiCond) = s2.freshSym(AST.Typed.b, pos)
      val (s4, loHiCond) = s3.freshSym(AST.Typed.b, pos)
      val s5 = s4.addClaims(ISZ(
        State.Claim.Let.Binary(loCond, State.Value.Z(0, pos), AST.Exp.BinaryOp.Le, i, AST.Typed.z),
        State.Claim.Prop(T, loCond),
        State.Claim.Let.FieldLookup(size, seq, "size"),
        State.Claim.Let.Binary(hiCond, i, AST.Exp.BinaryOp.Lt, size, AST.Typed.z),
        State.Claim.Prop(T, hiCond),
        State.Claim.Let.Binary(loHiCond, loCond, AST.Exp.BinaryOp.And, hiCond, AST.Typed.b),
        State.Claim.Prop(T, loHiCond)
      ))
      val cs2es = createClaimsToExps(jescmPlugins._4, pos, context.methodName, s5.claims, th, F, T)
      val pcsOps = ops.ISZOps(cs2es.translate(s5.claims))
      val pcs = HashSSet ++ pcsOps.dropRight(3)
      val ISZ(loCondExp: AST.Exp.Binary, hiCondExp: AST.Exp.Binary, loHiCondExp: AST.Exp.Binary) = pcsOps.takeRight(3)
      val normPCs = HashSet ++ PathConditions(th, pcs.elements).normalize
      def accept(w: ST, rel: String): State = {
        if (config.detailedInfo) {
          reporter.inform(pos, Logika.Reporter.Info.Kind.Verified,
            st"""The sequence indexing accepted because it is in bound in the path conditions, i.e.,
                |$w $rel {
                |  ${(for (pc <- pcs.elements) yield pc.prettyST, ";\n")}
                |}""".render)
        }
        return s0
      }
      if (normPCs.contains(th.normalizeExp(loHiCondExp))) {
        return accept(loHiCondExp.prettyST, "is in")
      } else if (normPCs.contains(th.normalizeExp(loCondExp)) && normPCs.contains(th.normalizeExp(hiCondExp))) {
        return accept(st"{ ${loCondExp.prettyST}; ${hiCondExp.prettyST} }", "is a subset of")
      } else {
        val sizeCond = hiCondExp.right
        for (pc <- pcs.elements) {
          pc match {
            case pc@AST.Exp.Binary(`sizeCond`, _, right) if Util.isEquivResOpt(th, pc.attr.resOpt, AST.Typed.z) =>
              val altLoHiCondExp = loHiCondExp(right = hiCondExp(right = right))
              if (normPCs.contains(th.normalizeExp(altLoHiCondExp))) {
                return accept(st"[${right.prettyST} / ${sizeCond.prettyST}](${loHiCondExp.prettyST})", "is in")
              } else if (normPCs.contains(th.normalizeExp(altLoHiCondExp.left)) && normPCs.contains(th.normalizeExp(altLoHiCondExp.right))) {
                return accept(st"{ ${altLoHiCondExp.left.prettyST}; [${right.prettyST} / ${sizeCond.prettyST}](${loHiCondExp.prettyST} }", "is a subset of")
              }
            case pc@AST.Exp.Binary(left, _, `sizeCond`) if Util.isEquivResOpt(th, pc.attr.resOpt, AST.Typed.z) =>
              val altLoHiCondExp = loHiCondExp(right = hiCondExp(right = left))
              if (normPCs.contains(th.normalizeExp(altLoHiCondExp))) {
                return accept(st"[${left.prettyST} / ${sizeCond.prettyST}](${loHiCondExp.prettyST})", "is in")
              } else if (normPCs.contains(th.normalizeExp(altLoHiCondExp.left)) && normPCs.contains(th.normalizeExp(altLoHiCondExp.right))) {
                return accept(st"{ ${altLoHiCondExp.left.prettyST}; [${left.prettyST} / ${sizeCond.prettyST}](${loHiCondExp.prettyST} }", "is a subset of")
              }
            case _ =>
          }
        }
        if (!config.searchPc) {
          reporter.error(posOpt, kind,
            st"""Sequence indexing has not been proven to be in bound in the path conditions:
                |{
                |  ${(for (pc <- pcs.elements) yield pc.prettyST, ";\n")}
                |}""".render)
          return s0(status = State.Status.Error)
        }
      }
    }
    val (s1, v) = s0.freshSym(AST.Typed.b, pos)
    val s2 = s1.addClaim(State.Claim.Let.SeqInBound(v, seq, i))
    val claim = State.Claim.Prop(T, v)
    val (implicitCheckOpt, implicitPosOpt, suffixOpt): (Option[String], Option[Position], Option[String]) =
      context.implicitCheckTitlePosOpt match {
        case Some((t, p)) => (Some(t), Some(p), Some(s" at [${pos.beginLine}, ${pos.beginColumn}]"))
        case _ => (None(), posOpt, None())
      }
    if (s2.ok) {
      val r = smt2.valid(context.methodName, config, cache, T,
        st"${implicitCheckOpt}Implicit Indexing Assertion at [${pos.beginLine}, ${pos.beginColumn}]".render,
        pos, s2.claims, claim, reporter)
      r.kind match {
        case Smt2Query.Result.Kind.Unsat => return s0
        case Smt2Query.Result.Kind.Sat => error(implicitPosOpt, st"${implicitCheckOpt}Possibly out of bound sequence indexing$suffixOpt".render, reporter)
        case Smt2Query.Result.Kind.Unknown => error(implicitPosOpt, st"${implicitCheckOpt}Could not deduce that the sequence indexing is in bound$suffixOpt".render, reporter)
        case Smt2Query.Result.Kind.Timeout => error(implicitPosOpt, st"${implicitCheckOpt}Timed out when deducing that the sequence indexing is in bound$suffixOpt".render, reporter)
        case Smt2Query.Result.Kind.Error => error(implicitPosOpt, st"${implicitCheckOpt}Error encountered when deducing that the sequence indexing is in bound$suffixOpt".render, reporter)
      }
    }
    return s2(status = State.Status.Error)
  }

  def evalLit(smt2: Smt2, lit: AST.Lit, reporter: Reporter): State.Value = {
    lit match {
      case e: AST.Exp.LitB => return State.Value.B(e.value, e.posOpt.get)
      case e: AST.Exp.LitC => return State.Value.C(e.value, e.posOpt.get)
      case e: AST.Exp.LitF32 => return State.Value.F32(e.value, e.posOpt.get)
      case e: AST.Exp.LitF64 => return State.Value.F64(e.value, e.posOpt.get)
      case e: AST.Exp.LitR => return State.Value.R(e.value, e.posOpt.get)
      case e: AST.Exp.LitString => return State.Value.String(e.value, e.posOpt.get)
      case e: AST.Exp.LitZ => return State.Value.Z(e.value, e.posOpt.get)
      case e: AST.ProofAst.StepId => halt("Infeasible")
    }
  }

  def text2SubZVal(ti: TypeInfo.SubZ, text: String, pos: Position): State.Value = {
    val t = ti.typedOpt.get.asInstanceOf[AST.Typed.Name]
    if (ti.ast.isBitVector) {
      ti.ast.bitWidth match {
        case 8 => return State.Value.S8(org.sireum.S8(text).get, t, pos)
        case 16 => return State.Value.S16(org.sireum.S16(text).get, t, pos)
        case 32 => return State.Value.S32(org.sireum.S32(text).get, t, pos)
        case 64 => return State.Value.S64(org.sireum.S64(text).get, t, pos)
        case _ =>
      }
    } else {
      ti.ast.bitWidth match {
        case 8 => return State.Value.U8(org.sireum.U8(text).get, t, pos)
        case 16 => return State.Value.U16(org.sireum.U16(text).get, t, pos)
        case 32 => return State.Value.U32(org.sireum.U32(text).get, t, pos)
        case 64 => return State.Value.U64(org.sireum.U64(text).get, t, pos)
        case _ =>
      }
    }
    return State.Value.Range(org.sireum.Z(text).get, t, pos)
  }

  def evalStringInterpolate(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State,
                            lit: AST.Exp.StringInterpolate, reporter: Reporter): ISZ[(State, State.Value)] = {
    var r = ISZ[(State, State.Value)]()
    val isST = lit.prefix == "st"
    for (p <- evalExps(split, smt2, cache, rtCheck, state, lit.args.size, (n: Z) => lit.args(n), reporter)) {
      val s0 = p._1
      val pos = lit.posOpt.get
      val (s1, v) = s0.freshSym(if (isST) AST.Typed.st else AST.Typed.string, pos)
      r = r :+ ((s1.addClaim(State.Claim.Let.Random(v, F, pos)), v))
    }
    val tOpt: String = if (isST) " template" else ""
    reporter.warn(lit.posOpt, kind, s"String$tOpt interpolation is currently over-approximated to produce an unconstrained string$tOpt")
    return r
  }

  def evalInterpolate(smt2: Smt2, lit: AST.Exp.StringInterpolate, reporter: Reporter): State.Value = {
    lit.prefix match {
      case string"z" => return State.Value.Z(org.sireum.Z(lit.lits(0).value).get, lit.posOpt.get)
      case string"r" => return State.Value.R(org.sireum.R(lit.lits(0).value).get, lit.posOpt.get)
      case string"c" => return State.Value.C(conversions.String.toCis(lit.lits(0).value)(0), lit.posOpt.get)
      case string"f32" => return State.Value.F32(org.sireum.F32(lit.lits(0).value).get, lit.posOpt.get)
      case string"f64" => return State.Value.F64(org.sireum.F64(lit.lits(0).value).get, lit.posOpt.get)
      case _ =>
        val t = lit.typedOpt.get
        val ids = t.asInstanceOf[AST.Typed.Name].ids
        th.typeMap.get(ids).get match {
          case ti: TypeInfo.SubZ => return text2SubZVal(ti, lit.lits(0).value, lit.posOpt.get)
          case _ =>
        }
        halt(s"TODO: $lit")
    }
  }

  def evalConstantVar(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, info: Info.Var, reporter: Reporter): Option[(State, State.Value)] = {
    if (!info.ast.isVal) {
      return None()
    }
    AST.Util.constantInitOpt(info.ast.initOpt, info.ast.attr.typedOpt) match {
      case Some(exp) =>
        val r = evalExp(Split.Disabled, smt2, cache, rtCheck, s0, exp, reporter)
        assert(r.size == 1)
        return Some(r(0))
      case _ =>
        return None()
    }
  }

  def evalConstantVarInstance(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, owner: ISZ[String], id: String,  reporter: Reporter): Option[(State, State.Value)] = {
    th.typeMap.get(owner) match {
      case Some(info: TypeInfo.Adt) =>
        info.vars.get(id) match {
          case Some(info) => return evalConstantVar(smt2, cache, rtCheck, s0, info, reporter)
          case _ =>
        }
      case _ =>
    }
    return None()
  }


  def evalThisIdH(smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, id: String, t: AST.Typed, pos: Position, reporter: Reporter): (State, State.Value) = {
    val mc = context.methodOpt.get
    val receiverType = mc.receiverTypeOpt.get.asInstanceOf[AST.Typed.Name]
    evalConstantVarInstance(smt2, cache, rtCheck, state, receiverType.ids, id, reporter) match {
      case Some(r@(_, _)) => return r
      case _ =>
        val (s0, receiver) = idIntro(pos, state, mc.name, "this", receiverType, None())
        val (s1, r) = s0.freshSym(t, pos)
        return (s1.addClaim(State.Claim.Let.FieldLookup(r, receiver, id)), r)
    }
  }

  def evalExps(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, numOfExps: Z,
               fe: Z => AST.Exp@pure, reporter: Reporter): ISZ[(State, ISZ[State.Value])] = {
    var done = ISZ[(State, ISZ[State.Value])]()
    var currents = ISZ((state, ISZ[State.Value]()))
    for (i <- 0 until numOfExps) {
      val e = fe(i)
      val cs = currents
      currents = ISZ()
      var nextFresh: Z = state.nextFresh
      for (current <- cs) {
        val (s0, vs) = current
        for (p <- evalExp(split, smt2, cache, rtCheck, s0, e, reporter)) {
          val (s1, v) = p
          if (nextFresh < s1.nextFresh) {
            nextFresh = s1.nextFresh
          }
          if (s1.ok) {
            currents = currents :+ ((s1, vs :+ v))
          } else {
            done = done :+ ((s1, vs :+ v))
          }
        }
      }
      currents = for (p <- currents) yield (p._1(nextFresh = nextFresh), p._2)
    }
    return currents ++ done
  }

  def evalArgs(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, numOfArgs: Z,
               eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]], reporter: Reporter): ISZ[(State, ISZ[Option[State.Value]])] = {
    eargs match {
      case Either.Left(es) =>
        @strictpure def fe(i: Z): AST.Exp = es(i)

        return for (p <- evalExps(split, smt2, cache, rtCheck, state, es.size, fe _, reporter)) yield
          (p._1, for (v <- p._2) yield Some(v))
      case Either.Right(nargs) =>
        @strictpure def feM(i: Z): AST.Exp = nargs(i).arg

        var r = ISZ[(State, ISZ[Option[State.Value]])]()
        for (p <- evalExps(split, smt2, cache, rtCheck, state, nargs.size, feM _, reporter)) {
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

  def rewriteAt(atMap: Util.ClaimsToExps.AtMap, state: State, exp: AST.Exp, reporter: Reporter): (State, AST.Exp) = {
    val rw = AtSymRewriter(this, atMap, state, reporter.empty)
    val r = rw.transformExp(exp).getOrElse(exp)
    reporter.reports(rw.reporter.messages)
    return (rw.state, r)
  }

  def evalAtH(state: State, atMap: ClaimsToExps.AtMap, exp: AST.Exp.At, reporter: Reporter): (State, State.Value) = {
    val t = exp.typedOpt.get
    val pos = exp.posOpt.get

    def rand(num: Z): (State, State.Value) = {
      val key: ClaimsToExps.AtKey = (ISZ(), ".random", t, exp.num.value)
      atMap.get(key) match {
        case Some((poss, _, sym)) =>
          if (poss.size > 0) {
            val (s0, sym) = state.freshSym(t, pos)
            return (s0.addClaim(State.Claim.Let.Random(sym, F, poss(0))), sym)
          } else {
            return (state, sym)
          }
        case _ =>
          reporter.error(exp.posOpt, kind, st"Could not find .random of $t with the occurrence number $num".render)
          return (state(status = State.Status.Error), State.errorValue)
      }
    }

    def local(res: AST.ResolvedInfo.LocalVar, num: Z): (State, State.Value) = {
      val key: ClaimsToExps.AtKey = (ISZ(), st"${(res.context :+ res.id, ".")}".render, t, exp.num.value)
      atMap.get(key) match {
        case Some((poss, num, sym)) =>
          if (poss.size > 0) {
            val (s0, sym) = state.freshSym(t, pos)
            return (s0.addClaim(State.Claim.Let.Id(sym, T, res.context, res.id, num, poss)), sym)
          } else {
            return (state, sym)
          }
        case _ =>
          reporter.error(exp.posOpt, kind, st"Could not find ${res.id} with the occurrence number $num".render)
          return (state(status = State.Status.Error), State.errorValue)
      }
    }

    def global(res: AST.ResolvedInfo.Var, num: Z): (State, State.Value) = {
      val key: ClaimsToExps.AtKey = (res.owner :+ res.id, "", t, exp.num.value)
      atMap.get(key) match {
        case Some((poss, num, sym)) =>
          if (poss.size > 0) {
            val (s0, sym) = state.freshSym(t, pos)
            return (s0.addClaim(State.Claim.Let.Name(sym, key._1, num, poss)), sym)
          } else {
            return (state, sym)
          }
        case _ =>
          reporter.error(exp.posOpt, kind, st"Could not find ${(res.owner :+ res.id, ".")} with the occurrence number $num".render)
          return (state(status = State.Status.Error), State.errorValue)
      }
    }

    exp.exp match {
      case e: AST.Exp.Ref =>
        e.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar => return local(res, exp.num.value)
          case res: AST.ResolvedInfo.Var if res.isInObject => return global(res, exp.num.value)
          case res => halt(s"Infeasible: $res")
        }
      case _: AST.Exp.This => return local(AST.ResolvedInfo.LocalVar(context.methodName,
        AST.ResolvedInfo.LocalVar.Scope.Current, F, T, "this"), exp.num.value)
      case e: AST.Exp.LitString =>
        if (e.value == ".random") {
          return rand(exp.num.value)
        }
        val ids = ops.StringOps(e.value).split((c: C) => c == '.').map((s: String) => ops.StringOps(s).trim)
        val lcontext = ops.ISZOps(ids).dropRight(1)
        return local(AST.ResolvedInfo.LocalVar(lcontext, AST.ResolvedInfo.LocalVar.Scope.Current, F, T,
          ids(ids.size - 1)), exp.num.value)
      case e => halt(s"Infeasible: $e")
    }
  }


  def evalExp(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, e: AST.Exp,
              reporter: Reporter): ISZ[(State, State.Value)] = {
    if (!state.ok) {
      return ISZ((state, State.errorValue))
    }
    val ePlugins = jescmPlugins._2
    if (jescmPlugins._2.nonEmpty) {
      for (p <- ePlugins if p.canHandle(this, e)) {
        return p.handle(this, split, smt2, cache, rtCheck, state, e, reporter)
      }
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
                s1 = evalAssertH(T, smt2, cache, s"Min range check for $t", s3, sym, e.posOpt, ISZ(), reporter)
              }
              if (s1.ok && ti.ast.hasMax) {
                val (s4, sym) = s1.freshSym(AST.Typed.b, pos)
                val s5 = s4.addClaim(State.Claim.Let.Binary(sym, value, AST.Exp.BinaryOp.Le, z2SubZVal(ti, ti.ast.max, pos), t))
                s1 = evalAssertH(T, smt2, cache, s"Max range check for $t", s5, sym, e.posOpt, ISZ(), reporter)
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
        case AST.ResolvedInfo.Var(T, F, T, name, id) if (name == AST.Typed.f32Name || name == AST.Typed.f64Name) && (id == "NaN" || id == "PInf" || id == "NInf") =>
          val (s1, v) = nameIntro(pos, s0, name :+ id, t, Some(pos))
          return (s1, v)
        case res: AST.ResolvedInfo.LocalVar =>
          if (res.isVal && res.context.isEmpty && context.methodName.nonEmpty) {
            th.nameMap.get(ISZ(res.id)) match {
              case Some(info: Info.LocalVar) =>
                AST.Util.constantInitOpt(info.initOpt, info.typedOpt) match {
                  case Some(init) =>
                    val (s1, c) = evalExp(split, smt2, cache, rtCheck, s0, init, reporter)(0)
                    val (s2, r) = idIntro(pos, s1, res.context, res.id, t, None())
                    return (s2.addClaim(State.Claim.Eq(r, c)), r)
                  case _ =>
                }
              case _ =>
            }
          }
          val (s1, r) = idIntro(pos, s0, res.context, res.id, t, None())
          return (s1, r)
        case res: AST.ResolvedInfo.Var =>
          if (res.isInObject) {
            def evalObjectVarH(): (State, State.Value.Sym) = {
              th.nameMap.get(res.owner :+ res.id) match {
                case Some(info: Info.Var) =>
                  evalConstantVar(smt2, cache, rtCheck, s0, info, reporter) match {
                    case Some((s1, v)) => return value2Sym(s1, v, pos)
                    case _ =>
                  }
                case _ =>
              }
              return nameIntro(pos, s0, res.owner :+ res.id, t, None())
            }
            val (s2, v) = evalObjectVarH()
            val s3: State =
              if (res.owner == context.owner) s2
              else Util.assumeObjectInv(this, smt2, cache, res.owner, s2, pos, reporter)
            return (Util.assumeValueInv(this, smt2, cache, rtCheck, s3, v, pos, reporter), v)
          } else {
            val (s1, r) = evalThisIdH(smt2, cache, rtCheck, s0, res.id, t, pos, reporter)
            val (s2, sym) = value2Sym(s1, r, pos)
            return (Util.assumeValueInv(this, smt2, cache, rtCheck, s2, sym, pos, reporter), sym)
          }
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return (s0(status = State.Status.Error), State.errorValue)
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
        case AST.ResolvedInfo.BuiltIn(kind) if th.isGroundType(exp.typedOpt.get) =>
          def evalUnaryExpH(p: (State, State.Value)): (State, State.Value) = {
            val (s1, v) = p
            if (!s1.ok) {
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

          return for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp.exp, reporter)) yield evalUnaryExpH(p)
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $exp")
          return ISZ((s0(status = State.Status.Error), State.errorValue))
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
        if (!rtCheck || !s0.ok) {
          return s0
        }
        if (isManual || config.searchPc) {
          val tipe = value.tipe.asInstanceOf[AST.Typed.Name]
          val (s1, neCond) = s0.freshSym(AST.Typed.b, pos)
          val (s2, ltCond) = s1.freshSym(AST.Typed.b, pos)
          val (s3, gtCond) = s2.freshSym(AST.Typed.b, pos)
          val s4 = s3.addClaims(ISZ(
            State.Claim.Let.Binary(neCond, value, AST.Exp.BinaryOp.Ne, zero(tipe, pos), tipe),
            State.Claim.Prop(T, neCond),
            State.Claim.Let.Binary(ltCond, value, AST.Exp.BinaryOp.Lt, zero(tipe, pos), tipe),
            State.Claim.Prop(T, ltCond),
            State.Claim.Let.Binary(gtCond, value, AST.Exp.BinaryOp.Gt, zero(tipe, pos), tipe),
            State.Claim.Prop(T, gtCond)
          ))
          val cs2es = createClaimsToExps(jescmPlugins._4, pos, context.methodName, s4.claims, th, config.atLinesFresh, T)
          val expsOps = ops.ISZOps(cs2es.translate(s4.claims))
          val pcs = expsOps.dropRight(3)
          val ISZ(neExp, ltExp, gtExp) = expsOps.takeRight(3)
          val normPCs = HashSet ++ PathConditions(th, pcs).normalize
          if (normPCs.contains(th.normalizeExp(neExp))) {
            if (config.detailedInfo) {
              reporter.inform(pos, Logika.Reporter.Info.Kind.Verified,
                st"""Accepted because the right-hand-side operand is non-zero in the path conditions, i.e.,
                    |${neExp.prettyST} is in {
                    |  ${(for (pc <- pcs) yield pc.prettyST, ";\n")}
                    |}""".render)
            }
            return s0
          } else if (normPCs.contains(th.normalizeExp(ltExp))) {
            if (config.detailedInfo) {
              reporter.inform(pos, Logika.Reporter.Info.Kind.Verified,
                st"""Accepted because the right-hand-side operand is less than zero in the path conditions, i.e.,
                    |${ltExp.prettyST} is in {
                    |  ${(for (pc <- pcs) yield pc.prettyST, ";\n")}
                    |}""".render)
            }
            return s0
          } else if (normPCs.contains(th.normalizeExp(gtExp))) {
            if (config.detailedInfo) {
              reporter.inform(pos, Logika.Reporter.Info.Kind.Verified,
                st"""Accepted because the right-hand-side operand is greater than zero in the path conditions, i.e.,
                    |${gtExp.prettyST} is in {
                    |  ${(for (pc <- pcs) yield pc.prettyST, ";\n")}
                    |}""".render)
            }
            return s0
          } else if (!config.searchPc) {
            reporter.error(Some(pos), kind,
              st"""Could not find the fact that the right-hand-side operand is non-zero in the path conditions:
                  |{
                  |  ${(for (pc <- pcs) yield pc.prettyST, ";\n")}
                  |}""".render)
            return s0(status = State.Status.Error)
          }
        }
        val (s1, sym) = s0.freshSym(AST.Typed.b, pos)
        val tipe = value.tipe.asInstanceOf[AST.Typed.Name]
        val claim = State.Claim.Let.Binary(sym, value,
          if (AST.Typed.floatingPointTypes.contains(tipe)) AST.Exp.BinaryOp.FpNe
          else AST.Exp.BinaryOp.Ne, zero(tipe, pos), tipe)
        val (implicitCheckOpt, implicitPosOpt, suffixOpt): (Option[String], Option[Position], Option[String]) =
          context.implicitCheckTitlePosOpt match {
            case Some((t, p)) => (Some(t), Some(p), Some(s" at [${pos.beginLine}, ${pos.beginColumn}]"))
            case _ => (None(), Some(pos), None())
          }
        val r = smt2.valid(context.methodName, config, cache, T,
          st"${implicitCheckOpt}non-zero second operand of '$op' at [${pos.beginLine}, ${pos.beginColumn}]".render,
          pos, s0.claims :+ claim, State.Claim.Prop(T, sym), reporter)
        r.kind match {
          case Smt2Query.Result.Kind.Unsat => return s1.addClaim(claim)
          case Smt2Query.Result.Kind.Sat => error(implicitPosOpt, st"${implicitCheckOpt}Possibly zero second operand for ${exp.op}$suffixOpt".render, reporter)
          case Smt2Query.Result.Kind.Unknown => error(implicitPosOpt, st"${implicitCheckOpt}Could not deduce non-zero second operand for ${exp.op}$suffixOpt".render, reporter)
          case Smt2Query.Result.Kind.Timeout => error(implicitPosOpt, st"${implicitCheckOpt}Timed out when deducing non-zero second operand for ${exp.op}$suffixOpt".render, reporter)
          case Smt2Query.Result.Kind.Error => error(implicitPosOpt, st"${implicitCheckOpt}Error encountered when deducing non-zero second operand for ${exp.op}$suffixOpt\n${r.info}".render, reporter)
        }
        return s1(status = State.Status.Error)
      }

      def evalBasic(s0: State, kind: AST.ResolvedInfo.BuiltIn.Kind.Type, v1: State.Value): ISZ[(State, State.Value)] = {
        def evalBasicH(p: (State, State.Value)): (State, State.Value) = {
          val (s1, v2) = p
          val s2: State = if (reqNonZeroCheck(kind)) {
            checkNonZero(s1, exp.op, v2, exp.right.posOpt.get)
          } else {
            s1
          }
          if (!s2.ok) {
            return (s2, State.errorValue)
          }
          val rTipe = e.typedOpt.get
          val pos = e.posOpt.get
          val (s3, rExp) = s2.freshSym(rTipe, pos)
          val s4 = s3.addClaim(State.Claim.Let.Binary(rExp, v1, exp.op, v2, v1.tipe))
          return (checkRange(s4, rExp, pos), rExp)
        }

        return for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp.right, reporter)) yield evalBasicH(p)
      }

      def evalMapsTo(s0: State, v1: State.Value): ISZ[(State, State.Value)] = {
        def evalMapsToH(p: (State, State.Value)): (State, State.Value) = {
          val (s1, v2) = p
          val rTipe = e.typedOpt.get
          val pos = e.posOpt.get
          val (s2, rExp) = s1.freshSym(rTipe, pos)
          val s3 = s2.addClaim(State.Claim.Let.TupleLit(rExp, ISZ(v1, v2)))
          return (s3, rExp)
        }

        return for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp.right, reporter)) yield evalMapsToH(p)
      }

      def evalCond(kind: AST.ResolvedInfo.BuiltIn.Kind.Type): ISZ[(State, State.Value)] = {
        kind match {
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
            return evalIfExp("&&", split, AST.Exp.If(exp.left, exp.right, AST.Exp.LitB(F, AST.Attr(exp.left.posOpt)),
              AST.TypedAttr(exp.posOpt, exp.typedOpt)))
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
            return evalIfExp("||", split, AST.Exp.If(exp.left, AST.Exp.LitB(T, AST.Attr(exp.left.posOpt)), exp.right,
              AST.TypedAttr(exp.posOpt, exp.typedOpt)))
          case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
            return evalIfExp("-->:", split, AST.Exp.If(exp.left, exp.right, AST.Exp.LitB(T, AST.Attr(exp.left.posOpt)),
              AST.TypedAttr(exp.posOpt, exp.typedOpt)))
          case _ => halt("Infeasible")
        }
      }

      def evalSeq(s0: State, m: AST.ResolvedInfo.Method): ISZ[(State, State.Value)] = {
        @pure def capacityOpt(v: State.Value): Option[Z] = {
          val t = v.tipe.asInstanceOf[AST.Typed.Name]
          if (t.ids != AST.Typed.isName && t.ids != AST.Typed.msName) {
            return None()
          }
          val it = t.args(0).asInstanceOf[AST.Typed.Name]
          if (it != AST.Typed.z) {
            return th.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ].ast.capacityOpt
          } else {
            return None()
          }
        }
        var r = ISZ[(State, State.Value)]()
        val pos = e.posOpt.get
        for (p1 <- evalExp(split, smt2, cache, rtCheck, s0, exp.left, reporter)) {
          val (s1, v1) = p1
          if (exp.op == AST.Exp.BinaryOp.Append) {
            capacityOpt(v1) match {
              case Some(capacity) =>
                val (s2, size) = s1.freshSym(AST.Typed.z, pos)
                val (s3, cond) = s2.freshSym(AST.Typed.b, pos)
                val s4 = s3.addClaims(ISZ(
                  State.Claim.Let.FieldLookup(size, v1, "size"),
                  State.Claim.Let.Binary(cond, size, AST.Exp.BinaryOp.Lt, State.Value.Z(capacity, pos), AST.Typed.z)
                ))
                evalAssertH(T, smt2, cache, "Sequence append capacity check", s4, cond, e.posOpt, ISZ(), reporter)
              case _ =>
            }
          }
          if (s1.ok) {
            for (p2 <- evalExp(split, smt2, cache, rtCheck, s1, exp.right, reporter)) {
              val (s2, v2) = p2
              exp.op match {
                case AST.Exp.BinaryOp.Prepend =>
                  capacityOpt(v2) match {
                    case Some(capacity) =>
                      val (s3, size) = s2.freshSym(AST.Typed.z, pos)
                      val (s4, cond) = s3.freshSym(AST.Typed.b, pos)
                      val s5 = s4.addClaims(ISZ(
                        State.Claim.Let.FieldLookup(size, v2, "size"),
                        State.Claim.Let.Binary(cond, size, AST.Exp.BinaryOp.Lt, State.Value.Z(capacity, pos), AST.Typed.z)
                      ))
                      evalAssertH(T, smt2, cache, "Sequence prepend capacity check", s5, cond, e.posOpt, ISZ(), reporter)
                    case _ =>
                  }
                case AST.Exp.BinaryOp.AppendAll =>
                  capacityOpt(v1) match {
                    case Some(capacity) =>
                      val (s3, size1) = s2.freshSym(AST.Typed.z, pos)
                      val (s4, size2) = s3.freshSym(AST.Typed.z, pos)
                      val (s5, newSize) = s4.freshSym(AST.Typed.z, pos)
                      val (s6, cond) = s5.freshSym(AST.Typed.b, pos)
                      val s7 = s6.addClaims(ISZ(
                        State.Claim.Let.FieldLookup(size1, v1, "size"),
                        State.Claim.Let.FieldLookup(size2, v2, "size"),
                        State.Claim.Let.Binary(newSize, size1, AST.Exp.BinaryOp.Add, size2, AST.Typed.z),
                        State.Claim.Let.Binary(cond, newSize, AST.Exp.BinaryOp.Le, State.Value.Z(capacity, pos), AST.Typed.z)
                      ))
                      evalAssertH(T, smt2, cache,  "Sequence append-all capacity check", s7, cond, e.posOpt, ISZ(), reporter)
                    case _ =>
                  }
                case _ =>
              }
              if (s2.ok) {
                val rTipe = e.typedOpt.get
                val (s3, rExp) = s2.freshSym(rTipe, pos)
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
          if (isCond(kind)) {
            return evalCond(kind)
          } else {
            var r = ISZ[(State, State.Value)]()
            var maxFresh = s0.nextFresh
            for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp.left, reporter)) {
              val (s1, v1) = p
              if (s1.ok) {
                if (kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryMapsTo) {
                  for (svs2 <- evalMapsTo(s1, v1)) {
                    if (maxFresh < svs2._1.nextFresh) {
                      maxFresh = svs2._1.nextFresh
                    }
                    r = r :+ svs2
                  }
                } else if (TypeChecker.eqBinops.contains(exp.op) || th.isGroundType(v1.tipe)) {
                  for (svs2 <- evalBasic(s1, kind, v1)) {
                    if (maxFresh < svs2._1.nextFresh) {
                      maxFresh = svs2._1.nextFresh
                    }
                    r = r :+ svs2
                  }
                } else {
                  reporter.warn(e.posOpt, Logika.kind, s"Not currently supported: $e")
                  r = r :+ ((s1(status = State.Status.Error), State.errorValue))
                }
              } else {
                r = r :+ ((s1, State.errorValue))
              }
            }
            return for (svs <- r) yield (svs._1(nextFresh = maxFresh), svs._2)
          }
        case m: AST.ResolvedInfo.Method =>
          if (isSeq(m)) {
            return evalSeq(s0, m)
          }
          val posOpt = exp.posOpt
          return evalInvoke(s0, Some(exp.left), AST.Exp.Ident(AST.Id(exp.op, AST.Attr(posOpt)), exp.attr),
            Either.Left(ISZ(exp.right)), exp.attr)
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((s0(status = State.Status.Error), State.errorValue))
      }
    }

    def evalInstanceOfAs(isCast: B, receiverOpt: Option[AST.Exp], tipe: AST.Typed, pos: Position): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (p <- evalExp(split, smt2, cache, rtCheck, state, receiverOpt.get, reporter)) {
        val (s0, v) = p
        if (s0.ok) {
          val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
          val s2 = s1.addClaim(State.Claim.Let.TypeTest(cond, F, v, tipe))
          if (isCast) {
            val s3: State = if (rtCheck) {
              evalAssertH(T, smt2, cache, "asInstanceOf", s2, cond, Some(pos), ISZ(), reporter)
            } else {
              val thiz = this
              thiz(config = thiz.config(sat = F)).evalAssumeH(T, smt2, cache, "asInstanceOf", s2, cond, Some(pos), reporter)
            }
            if (s3.ok) {
              val (s4, cv) = s3.freshSym(tipe, pos)
              r = r :+ ((s4.addClaim(State.Claim.Let.Def(cv, v)), cv))
            } else {
              r = r :+ ((s3, State.errorValue))
            }
          } else {
            r = r :+ ((s2, cond))
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return r
    }

    def evalSelectH(sp: Split.Type, res: AST.ResolvedInfo, receiverOpt: Option[AST.Exp], id: String, tipe: AST.Typed,
                    pos: Position): ISZ[(State, State.Value)] = {
      def evalField(t: AST.Typed): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        for (p <- evalExp(sp, smt2, cache, rtCheck, state, receiverOpt.get, reporter)) {
          def evalFieldH(): (State, State.Value.Sym) = {
            var s0 = p._1
            val o = p._2
            o.tipe match {
              case tipe: AST.Typed.Name =>
                if (indexingFields.contains(id) && (tipe.ids == AST.Typed.isName || tipe.ids == AST.Typed.msName)) {
                  val (s1, size) = s0.freshSym(AST.Typed.z, pos)
                  val (s2, cond) = s1.addClaim(State.Claim.Let.FieldLookup(size, o, "size")).freshSym(AST.Typed.b, pos)
                  val s3 = s2.addClaim(State.Claim.Let.Binary(cond, size, AST.Exp.BinaryOp.Gt, State.Value.Z(0, pos), AST.Typed.z))
                  s0 = if (rtCheck) {
                    evalAssertH(T, smt2, cache, s"Non-empty check for $tipe", s3, cond, Some(pos), ISZ(), reporter)
                  } else {
                    val thiz = this
                    thiz(config = thiz.config(sat = F)).
                      evalAssumeH(T, smt2, cache, s"Non-empty check for $tipe", s3, cond, Some(pos), reporter)
                  }
                } else {
                  evalConstantVarInstance(smt2, cache, rtCheck, s0, tipe.ids, id, reporter) match {
                    case Some((s1, v)) => return value2Sym(s1, v, pos)
                    case _ =>
                  }
                }
              case _ =>
            }
            val (s4, sym) = s0.freshSym(t, pos)
            val s5 = s4.addClaim(State.Claim.Let.FieldLookup(sym, o, id))
            return (s5, sym)
          }
          val (s6, sym) = evalFieldH()
          if (s6.ok) {
            r = r :+ ((Util.assumeValueInv(this, smt2, cache, rtCheck, s6, sym, pos, reporter), sym))
          } else {
            r = r :+ ((s6, State.errorValue))
          }
        }
        return r
      }

      def evalEnumElement(eres: AST.ResolvedInfo.EnumElement): (State, State.Value) = {
        return (state, State.Value.Enum(tipe.asInstanceOf[AST.Typed.Name], eres.owner, eres.name, eres.ordinal, pos))
      }

      def evalTupleProjection(tres: AST.ResolvedInfo.Tuple): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        val (s0, sym) = state.freshSym(tipe, pos)
        for (p <- evalExp(split, smt2, cache, rtCheck, s0, receiverOpt.get, reporter)) {
          val (s1, v) = p
          if (s1.ok) {
            val s2 = s1.addClaim(State.Claim.Let.FieldLookup(sym, v, s"_${tres.index}"))
            r = r :+ ((Util.assumeValueInv(this, smt2, cache, rtCheck, s2, sym, pos, reporter), sym))
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
          return evalTupleProjection(res)
        case AST.ResolvedInfo.BuiltIn(kind) if (kind == AST.ResolvedInfo.BuiltIn.Kind.Min ||
          kind == AST.ResolvedInfo.BuiltIn.Kind.Max) && receiverOpt.get.typedOpt.get.isInstanceOf[AST.Typed.Object] =>
          val (s0, sym) = nameIntro(pos, state, receiverOpt.get.typedOpt.get.asInstanceOf[AST.Typed.Object].name, tipe, None())
          return ISZ((s0, sym))
        case AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.Apply) =>
          assert(receiverOpt.nonEmpty)
          return evalExp(split, smt2, cache, rtCheck, state, receiverOpt.get, reporter)
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((state(status = State.Status.Error), State.errorValue))
      }
    }

    def evalSelect(exp: AST.Exp.Select): ISZ[(State, State.Value)] = {
      val pos = exp.id.attr.posOpt.get
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.BuiltIn if res.kind == AST.ResolvedInfo.BuiltIn.Kind.IsInstanceOf ||
          res.kind == AST.ResolvedInfo.BuiltIn.Kind.AsInstanceOf =>
          return evalInstanceOfAs(res.kind == AST.ResolvedInfo.BuiltIn.Kind.AsInstanceOf, exp.receiverOpt,
            exp.targs(0).typedOpt.get, exp.posOpt.get)
        case res: AST.ResolvedInfo.Method if (res.mode == AST.MethodMode.Method || res.mode == AST.MethodMode.Ext) &&
          res.tpeOpt.get.isByName && !Logika.builtInByNameMethods.contains((res.isInObject, res.owner, res.id)) =>
          val mType = res.tpeOpt.get
          val attr = AST.ResolvedAttr(exp.id.attr.posOpt, exp.attr.resOpt, Some(mType.ret))
          return evalInvoke(state, exp.receiverOpt, AST.Exp.Ident(exp.id, exp.attr), Either.Left(ISZ()), attr)
        case res: AST.ResolvedInfo.Var if res.isInObject =>
          return ISZ(evalIdentH(state, res, exp.typedOpt.get, exp.posOpt.get))
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
        val it = t.args(0).asInstanceOf[AST.Typed.Name]
        if (it != AST.Typed.z) {
          val size: Z = eargs match {
            case Either.Left(s) => s.size
            case Either.Right(s) => s.size
          }
          val subz = th.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ]
          subz.ast.capacityOpt match {
            case Some(capacity) if size > capacity =>
              reporter.error(e.posOpt, Logika.kind, s"Expecting a maximum of $capacity elements, but found $size.")
              r = r :+ (state(status = State.Status.Error), State.errorValue)
              return
            case _ =>
          }
        }
        val (s0, sym) = state.freshSym(t, attr.posOpt.get)
        for (p <- evalArgs(sp, smt2, cache, rtCheck, s0, -1, eargs, reporter)) {
          val (s1, args) = p
          if (s1.ok) {
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
            val as: ISZ[State.Claim.Let.SeqLit.Arg] =
              for (p <- ops.ISZOps(indices).zip(args)) yield State.Claim.Let.SeqLit.Arg(p._1, p._2.get)
            r = r :+ ((s1.addClaim(State.Claim.Let.SeqLit(sym, as)), sym))
          } else {
            r = r :+ ((s1, State.errorValue))
          }
        }
      }

      def evalAdtConstructor(s0: State, receiverOpt: Option[State.Value]): Unit = {
        val (s1, sym) = s0.freshSym(t, attr.posOpt.get)
        val ti = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
        val params = ti.ast.params
        val sm = TypeChecker.buildTypeSubstMap(ti.name, e.posOpt, ti.ast.typeParams, t.args, message.Reporter.create).get
        for (p <- evalArgs(sp, smt2, cache, rtCheck, s1, params.size, eargs, reporter)) {
          val s2 = p._1
          val args = p._2.toMS
          if (s2.ok) {
            var s3 = s2
            eargs match {
              case Either.Right(_) =>
                for (i <- 0 until args.size) {
                  if (args(i).isEmpty) {
                    val receiver = receiverOpt.get
                    val param = params(i)
                    val pt = param.tipe.typedOpt.get.subst(sm)
                    val (s4, sym) = s3.freshSym(pt, param.id.attr.posOpt.get)
                    s3 = s4.addClaim(State.Claim.Let.FieldLookup(sym, receiver, param.id.value))
                    args(i) = Some(sym)
                  }
                }
              case _ =>
            }
            val s4 = s3.addClaim(State.Claim.Let.AdtLit(sym, args.toIS[Option[State.Value]].map((vOpt: Option[State.Value]) => vOpt.get)))
            val (s5, vs) = addValueInv(this, smt2, cache, T, s4, sym, attr.posOpt.get, reporter)
            var s6 = s5
            var thiz = this
            thiz = thiz(config = thiz.config(sat = F))
            for (v <- vs if s6.ok) {
              if (rtCheck) {
                s6 = evalAssertH(T, smt2, cache, st"Invariant on ${(ti.name, ".")} construction".render, s6, v,
                  attr.posOpt, ISZ(), reporter)
              } else {
                s6 = thiz.evalAssumeH(T, smt2, cache, st"Invariant on ${(ti.name, ".")} construction".render, s6, v,
                  attr.posOpt, reporter)
              }
            }
            r = r :+ ((s4(nextFresh = s6.nextFresh, status = s6.status), sym))
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
            for (p <- evalExp(split, smt2, cache, rtCheck, state, receiver, reporter)) yield (p._1, Some(p._2))
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
            case _ => return evalExp(sp, smt2, cache, rtCheck, state, rcv, reporter)
          }
        case _ =>
          if (isInObject) {
            return ISZ()
          } else {
            return ISZ(evalThis(AST.Exp.This(context.methodName, AST.TypedAttr(ident.posOpt, context.methodOpt.get.receiverTypeOpt))))
          }
      }
    }

    def evalSeqSelect(exp: AST.Exp.Invoke): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      val srcv: ISZ[(State, State.Value)] = exp.receiverOpt match {
        case Some(rcv) =>
          if (exp.ident.id.value == "apply") {
            evalExp(split, smt2, cache, rtCheck, state, rcv , reporter)
          } else {
            evalSelect(AST.Exp.Select(exp.receiverOpt, exp.ident.id, exp.targs, exp.ident.attr))
          }
        case _ => evalIdent(exp.ident)
      }
      for (p0 <- srcv; p1 <- evalExp(split, smt2, cache, rtCheck, p0._1, exp.args(0), reporter)) {
        val (_, seq) = p0
        val (s1, i) = p1
        val s2 = checkSeqIndexing(smt2, cache, rtCheck, s1, seq, i, exp.args(0).posOpt, reporter)
        val pos = exp.posOpt.get
        val (s3, v) = s2.freshSym(exp.typedOpt.get, pos)
        val s4 = s3.addClaim(State.Claim.Let.SeqLookup(v, seq, i))
        r = r :+ ((Util.assumeValueInv(this, smt2, cache, rtCheck, s4, v, pos, reporter), v))
      }
      return r
    }

    def evalSeqUpdate(exp: AST.Exp.Invoke): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      val srcv: ISZ[(State, State.Value)] = exp.receiverOpt match {
        case Some(rcv) =>
          if (exp.ident.id.value == "apply") {
            evalExp(split, smt2, cache, rtCheck, state, rcv , reporter)
          } else {
            evalSelect(AST.Exp.Select(exp.receiverOpt, exp.ident.id, exp.targs, exp.ident.attr))
          }
        case _ => evalIdent(exp.ident)
      }
      for (p0 <- srcv) {
        var p1 = p0
        for (arg <- exp.args) {
          val (s0, seq) = p1
          for (p2 <- evalExp(split, smt2, cache, rtCheck, s0, arg, reporter)) {
            val (s1, iv) = p2
            val AST.Typed.Tuple(ISZ(iType, vType)) = iv.tipe
            val pos = exp.posOpt.get
            val (s2, i) = s1.freshSym(iType, pos)
            val (s3, v) = s2.freshSym(vType, pos)
            val (s4, newSeq) = s3.freshSym(seq.tipe, pos)
            p1 = (s4.addClaims(ISZ(
              State.Claim.Let.FieldLookup(i, iv, "_1"),
              State.Claim.Let.FieldLookup(v, iv, "_2"),
              State.Claim.Let.SeqStore(newSeq, seq, i, v)
            )), newSeq)
          }
        }
        r = r :+ p1
      }
      return r
    }

    def evalResult(exp: AST.Exp.Result): (State, State.Value) = {
      val (s, sym) = resIntro(exp.posOpt.get, state, context.methodOpt.get.name, exp.typedOpt.get, None())
      return (s, sym)
    }

    def evalThis(exp: AST.Exp.This): (State, State.Value) = {
      val (s, sym) = idIntro(exp.posOpt.get, state, context.methodOpt.get.name, "this", exp.typedOpt.get, None())
      return (s, sym)
    }

    def evalAt(exp: AST.Exp.At): (State, State.Value) = {
      val pos = exp.posOpt.get
      return evalAtH(state, Util.claimsToExps(jescmPlugins._4, pos, context.methodName, state.claims, th, F,
        config.atRewrite)._2, exp, reporter)
    }

    def evalOld(exp: AST.Exp.Old): (State, State.Value) = {
      for (i <- state.claims.size - 1 to 0 by -1) {
        state.claims(i) match {
          case c: State.Claim.Old =>
            return (state, c.value)
          case _ =>
        }
      }
      reporter.error(exp.posOpt, kind, st"Could not find old value of ${exp.exp.prettyST}".render)
      return (state(status = State.Status.Error), State.errorValue)
    }

    def evalInput(input: AST.Exp.Input): (State, State.Value) = {
      input.exp match {
        case e: AST.Exp.Ref =>
          e.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              context.methodOpt.get.localInMap.get(res.id) match {
                case Some(sym) => return (state, sym)
                case _ =>
                  error(e.posOpt, s"Variable $e was not declared to be read/modified", reporter)
                  return (state(status = State.Status.Error), State.Value.B(F, e.posOpt.get))
              }
            case res: AST.ResolvedInfo.Var =>
              if (res.isInObject) {
                val ids = res.owner :+ res.id
                context.methodOpt.get.objectVarInMap.get(ids) match {
                  case Some(sym) => return (state, sym)
                  case _ =>
                    error(e.posOpt, s"Variable $e was not declared to be read/modified", reporter)
                    return (state(status = State.Status.Error), State.Value.B(F, e.posOpt.get))
                }
              } else {
                context.methodOpt.get.fieldVarInMap.get(res.id) match {
                  case Some(sym) =>
                    return (state, sym)
                  case _ =>
                    error(e.posOpt, s"Variable $e was not declared to be read/modified", reporter)
                    return (state(status = State.Status.Error), State.Value.B(F, e.posOpt.get))
                }
              }
            case _ =>
          }
        case e: AST.Exp.This =>
          context.methodOpt.get.localInMap.get("this") match {
            case Some(sym) => return (state, sym)
            case _ =>
              error(e.posOpt, s"this was not declared to be modified", reporter)
              return (state(status = State.Status.Error), State.Value.B(F, e.posOpt.get))
          }
        case _ =>
      }
      halt(s"Infeasible: $e")
    }

    def evalQuantType(quant: AST.Exp.QuantType): (State, State.Value) = {
      var quantClaims = ISZ[State.Claim]()
      val (s0, sym) = state.freshSym(AST.Typed.b, quant.attr.posOpt.get)
      val s1: State = {
        var s2 = s0
        for (p <- quant.fun.params) {
          val id = p.idOpt.get
          val res = AST.ResolvedInfo.LocalVar(quant.fun.context, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, id.value)
          val pos = id.attr.posOpt.get
          val (s3, v) = evalIdentH(s0, res, p.typedOpt.get, pos)
          val (s4, sym) = value2Sym(s3, v, pos)
          val (s5, conds) = Util.addValueInv(this, smt2, cache, rtCheck, s4, sym, pos, reporter)
          if (conds.nonEmpty) {
            s2 = s5.addClaims(for (cond <- conds) yield State.Claim.Prop(T, cond))
          }
        }
        s2
      }
      val ISZ((s8, v)) = evalAssignExpValue(Split.Disabled, smt2, cache, AST.Typed.b, rtCheck, s1, quant.fun.exp, reporter)
      val (s9, expSym) = value2Sym(s8, v, quant.fun.exp.asStmt.posOpt.get)
      if (s9.ok) {
        quantClaims = quantClaims ++ ops.ISZOps(s9.claims).slice(s1.claims.size, s9.claims.size) :+ State.Claim.Prop(T, expSym)
      }
      val vars: ISZ[State.Claim.Let.Quant.Var] =
        for (p <- quant.fun.params) yield State.Claim.Let.Quant.Var(quant.fun.context, p.idOpt.get.value, p.typedOpt.get)
      if (quantClaims.isEmpty) {
        return (s0(status = State.Status.Error), State.errorValue)
      }
      val qcs: ISZ[State.Claim] = if (s0.claims.size != s1.claims.size) {
        val invs = ops.ISZOps(s1.claims).slice(s0.claims.size, s1.claims.size)
        invs ++ quantClaims
      } else {
        quantClaims
      }
      return (s9(claims = ops.ISZOps(s9.claims).slice(0, s0.claims.size)).
        addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym)
    }

    def evalQuantRange(quant: AST.Exp.QuantRange): ISZ[(State, State.Value)] = {
      val qVarType = quant.attr.typedOpt.get
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val s0 = state
      var r = ISZ[(State, State.Value)]()
      for (p1 <- evalExp(Split.Disabled, smt2, cache, rtCheck, s0, quant.lo, reporter);
           p2 <- evalExp(Split.Disabled, smt2, cache, rtCheck, p1._1, quant.hi, reporter)) {
        val (_, lo) = p1
        val (s2, hi) = p2
        if (s2.ok) {
          val (s3, ident) = evalIdentH(s2, quant.attr.resOpt.get, qVarType, quant.fun.params(0).idOpt.get.attr.posOpt.get)
          val (s4, loSym) = s3.freshSym(AST.Typed.b, quant.lo.posOpt.get)
          val s5 = s4.addClaim(State.Claim.Let.Binary(loSym, lo, AST.Exp.BinaryOp.Le, ident, qVarType))
          val (s6, hiSym) = s5.freshSym(AST.Typed.b, quant.hi.posOpt.get)
          val s7 = s6.addClaim(State.Claim.Let.Binary(hiSym, ident,
            if (quant.hiExact) AST.Exp.BinaryOp.Le else AST.Exp.BinaryOp.Lt, hi, qVarType))
          val (s8, range) = s7.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val (s9, sym) = s8.addClaim(State.Claim.Let.Binary(range, loSym, AST.Exp.BinaryOp.And, hiSym, AST.Typed.b)).freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val rangeProp = State.Claim.Prop(T, range)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var(quant.fun.context, qVarRes.id, qVarType))
          var quantClaims = ISZ[State.Claim]()
          val ISZ((s10, v)) = evalAssignExpValue(Split.Disabled, smt2, cache, AST.Typed.b, rtCheck, s9.addClaim(rangeProp), quant.fun.exp, reporter)
          val (s11, vSym) = value2Sym(s10, v, quant.fun.exp.asStmt.posOpt.get)
          val s12 = s11.addClaims(
            if (quant.isForall) ISZ(State.Claim.Imply(F, ISZ(rangeProp, State.Claim.Prop(T, vSym))))
            else ISZ(rangeProp, State.Claim.Prop(T, vSym))
          )
          if (s12.ok) {
            val s12ClaimsOps = ops.ISZOps(s12.claims)
            quantClaims = quantClaims ++ s12ClaimsOps.slice(s2.claims.size, s9.claims.size) ++
              s12ClaimsOps.slice(s9.claims.size + 1, s12.claims.size)
          }
          if (quantClaims.isEmpty) {
            r = r :+ ((s2(status = State.Status.Error), State.errorValue))
          } else {
            r = r :+ ((s12(claims = ops.ISZOps(s12.claims).slice(0, s2.claims.size)).
              addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, quantClaims)), sym))
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
      val s0 = state
      var r = ISZ[(State, State.Value)]()
      val ISZ((s2, s)) = evalExp(Split.Disabled, smt2, cache, rtCheck, s0, seqExp, reporter)
      if (s2.ok) {
        val (s3, ident) = evalIdentH(s2, quant.attr.resOpt.get, qVarType, quant.fun.params(0).idOpt.get.attr.posOpt.get)
        val (s4, inBoundSym) = s3.freshSym(AST.Typed.b, seqExp.posOpt.get)
        val s5 = s4.addClaim(State.Claim.Let.SeqInBound(inBoundSym, s, ident))
        val inBoundProp = State.Claim.Prop(T, inBoundSym)
        val (s6, sym) = s5.freshSym(AST.Typed.b, quant.attr.posOpt.get)
        val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var(quant.fun.context, qVarRes.id, qVarType))
        var quantClaims = ISZ[State.Claim]()
        val ISZ((s7, v)) = evalAssignExpValue(Split.Disabled, smt2, cache, AST.Typed.b, rtCheck, s6.addClaims(ISZ(inBoundProp)),
          quant.fun.exp, reporter)
        val (s8, vSym) = value2Sym(s7, v, quant.fun.exp.asStmt.posOpt.get)
        val s9 = s8.addClaims(
          if (quant.isForall) ISZ(State.Claim.Imply(F, ISZ(inBoundProp, State.Claim.Prop(T, vSym))))
          else ISZ(inBoundProp, State.Claim.Prop(T, vSym))
        )
        if (s9.ok) {
          val s9ClaimsOps = ops.ISZOps(s9.claims)
          quantClaims = quantClaims ++ s9ClaimsOps.slice(s2.claims.size, s6.claims.size) ++
            s9ClaimsOps.slice(s6.claims.size + 1, s9.claims.size)
        }
        if (quantClaims.isEmpty) {
          r = r :+ ((s2(status = State.Status.Error), State.errorValue))
        } else {
          r = r :+ ((s9(claims = ops.ISZOps(s9.claims).slice(0, s2.claims.size)).
            addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, quantClaims)), sym))
        }
      } else {
        r = r :+ ((s2, State.errorValue))
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
      val ISZ((s0, seq)) = evalExp(Split.Disabled, smt2, cache, rtCheck, state, quant.seq, reporter)
      if (s0.ok) {
        val idx = s"${qVarRes.id}$idxSuffix"
        val (s1, qvarIdx) = idIntro(pos, s0, qVarRes.context, idx, iType, Some(pos))
        val (s2, inBound) = s1.freshSym(AST.Typed.b, pos)
        val s3 = s2.addClaim(State.Claim.Let.SeqInBound(inBound, seq, qvarIdx))
        val inBoundProp = State.Claim.Prop(T, inBound)
        val (s4, select) = s3.freshSym(eType, pos)
        val s5 = s4.addClaim(State.Claim.Let.SeqLookup(select, seq, qvarIdx))
        val (s6, qvar) = idIntro(pos, s5, qVarRes.context, qVarRes.id, eType, Some(pos))
        val (s7, eqSym) = s6.freshSym(AST.Typed.b, pos)
        val s8 = s7.addClaim(State.Claim.Let.Binary(eqSym, select, AST.Exp.BinaryOp.Equiv, qvar, select.tipe))
        val (s9, sym) = s8.freshSym(AST.Typed.b, quant.attr.posOpt.get)
        val (s10, invSyms) = Util.addValueInv(this, smt2, cache, rtCheck, s9, select, pos, reporter)
        val vars = ISZ[State.Claim.Let.Quant.Var](
          State.Claim.Let.Quant.Var(qVarRes.context, idx, iType),
          State.Claim.Let.Quant.Var(qVarRes.context, qVarRes.id, eType)
        )
        var quantClaims = ISZ[State.Claim]()
        val ISZ((s11, v)) = evalAssignExpValue(Split.Disabled, smt2, cache, AST.Typed.b, rtCheck,
          s10.addClaims(ISZ(inBoundProp)), quant.fun.exp, reporter)
        val (s12, vSym) = value2Sym(s11, v, quant.fun.exp.asStmt.posOpt.get)
        var prop: State.Claim =
          if (quant.isForall) State.Claim.Imply(F, ISZ(State.Claim.Prop(T, eqSym), State.Claim.Prop(T, vSym)))
          else State.Claim.And(ISZ(State.Claim.Prop(T, eqSym), State.Claim.Prop(T, vSym)))
        if (invSyms.nonEmpty) {
          prop = State.Claim.And(
            (for (invSym <- invSyms) yield State.Claim.Prop(T, invSym).asInstanceOf[State.Claim]) :+ prop)
        }
        val s13 = s12.addClaims(
          if (quant.isForall) ISZ(State.Claim.Imply(F, ISZ(inBoundProp, prop)))
          else ISZ(inBoundProp, prop))
        if (s13.ok) {
          val s13ClaimsOps = ops.ISZOps(s13.claims)
          quantClaims = quantClaims ++ s13ClaimsOps.slice(s0.claims.size, s10.claims.size) ++
            s13ClaimsOps.slice(s10.claims.size + 1, s13.claims.size
            )
        }
        if (quantClaims.isEmpty) {
          r = r :+ ((s0(status = State.Status.Error), State.errorValue))
        } else {
          r = r :+ ((s13(claims = ops.ISZOps(s13.claims).slice(0, s0.claims.size)).
            addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, quantClaims)), sym))
        }
      } else {
        r = r :+ ((s0, State.errorValue))
      }
      return r
    }

    def methodInfo(isInObject: B, owner: QName, id: String): Context.InvokeMethodInfo = {
      def extractResolvedInfo(attr: AST.ResolvedAttr): AST.ResolvedInfo.Method = {
        return attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      }

      if (isInObject) {
        th.nameMap.get(owner :+ id) match {
          case Some(mi: lang.symbol.Info.Method) =>
            return Context.InvokeMethodInfo(mi.ast.isHelper, mi.ast.hasInline, mi.ast.sig, mi.ast.contract,
              extractResolvedInfo(mi.ast.attr), mi.ast.bodyOpt.nonEmpty, extractAssignExpOpt(mi))
          case Some(mi: lang.symbol.Info.ExtMethod) =>
            return Context.InvokeMethodInfo (T, F, mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr), F, None())
          case Some(mi: lang.symbol.Info.SpecMethod) =>
            val typedAttr = AST.TypedAttr(mi.ast.sig.id.attr.posOpt, mi.ast.sig.returnType.typedOpt)
            return Context.InvokeMethodInfo(T, F, mi.ast.sig, AST.MethodContract.Simple.empty,
              extractResolvedInfo(mi.ast.attr), F, Some(AST.Stmt.Expr(
                AST.Exp.Result(None(), typedAttr), typedAttr)))
          case info => halt(s"Infeasible: $owner.$id => $info")
        }
      } else {
        th.typeMap.get(owner) match {
          case Some(info: lang.symbol.TypeInfo.Adt) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return Context.InvokeMethodInfo(mi.ast.isHelper, mi.ast.hasInline, mi.ast.sig, mi.ast.contract,
                  extractResolvedInfo(mi.ast.attr), mi.ast.bodyOpt.nonEmpty, extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return Context.InvokeMethodInfo(T, F, mi.ast.sig, AST.MethodContract.Simple.empty,
                      extractResolvedInfo(mi.ast.attr), F, None())
                  case _ => halt("Infeasible")
                }
            }
          case Some(info: lang.symbol.TypeInfo.Sig) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return Context.InvokeMethodInfo(mi.ast.isHelper, mi.ast.hasInline, mi.ast.sig, mi.ast.contract,
                  extractResolvedInfo(mi.ast.attr), mi.ast.bodyOpt.nonEmpty, extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return Context.InvokeMethodInfo(T, F, mi.ast.sig, AST.MethodContract.Simple.empty,
                      extractResolvedInfo(mi.ast.attr), F, None())
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

    def resolveVirtualInvoke(posOpt: Option[Position], info: Context.InvokeMethodInfo, s0: State,
                             receiver: State.Value.Sym, typeSubstMap: HashMap[String, AST.Typed]): ISZ[(State, Either[Info.Method, State.Value])] = {
      var r = ISZ[(State, Either[Info.Method, State.Value])]()
      val pos = posOpt.get
      val t = receiver.tipe.asInstanceOf[AST.Typed.Name]
      val subs: ISZ[AST.Typed.Name] = if (th.isAdtLeafType(t)) {
        ISZ(t)
      } else {
        th.substLeavesOfType(posOpt, t) match {
          case Either.Left(subsT) => subsT
          case Either.Right(messages) =>
            reporter.reports(messages)
            return ISZ((s0(status = State.Status.Error), Either.Right(State.errorValue)))
        }
      }
      if (subs.isEmpty) {
        reporter.error(posOpt, Logika.kind, st"Could not find a ${if (th.isMutable(t)) "@record" else "@datatype"} class implementing ${(info.res.owner, ".")}".render)
        return ISZ((s0(status = State.Status.Error), Either.Right(State.errorValue)))
      }
      for (sub <- subs) {
        val (s1, sym) = s0.freshSym(AST.Typed.b, pos)
        val s2 = s1.addClaims(ISZ(State.Claim.Let.TypeTest(sym, T, receiver, sub), State.Claim.Prop(T, sym)))
        if (smt2.sat(context.methodName, config, cache, T,
          st"Virtual invocation satisfiability on ${(sub.ids, ".")}".render, pos, s2.claims, reporter)) {
          val adt = th.typeMap.get(sub.ids).get.asInstanceOf[TypeInfo.Adt]
          if (adt.specVars.contains(info.res.id) || adt.specMethods.contains(info.res.id)) {
            reporter.error(posOpt, Logika.kind, st"Could not virtually invoke @spec ${(sub.ids, ".")}#${info.res.id}".render)
            r = r :+ ((s2(status = State.Status.Error), Either.Right(State.errorValue)))
          } else if (adt.vars.contains(info.res.id)) {
            halt("TODO")
          } else {
            val minfo = adt.methods.get(info.res.id).get
            var sm = TypeChecker.buildTypeSubstMap(sub.ids, posOpt, adt.ast.typeParams, sub.args, reporter).get
            for (i <- 0 until info.sig.typeParams.size) {
              sm = sm + minfo.ast.sig.typeParams(i).id.value ~> typeSubstMap.get(info.sig.typeParams(i).id.value).get
            }
            r = r :+ ((s2, Either.Left(Info.substMethod(minfo, sm))))
          }
        } else {
          r = r :+ ((s2(status = State.Status.Error), Either.Right(State.errorValue)))
        }
      }
      return r
    }

    def interprocedural(posOpt: Option[Position], info: Context.InvokeMethodInfo, s: State,
                        typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed, invokeReceiverOpt: Option[AST.Exp],
                        receiverOpt: Option[State.Value.Sym], paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]): ISZ[(State, State.Value)] = {
      val res = info.res
      val ctx = res.owner :+ res.id
      val pos = posOpt.get
      val resST = methodResST(res)
      val receiverPosOpt: Option[Position] =
        if (invokeReceiverOpt.nonEmpty) invokeReceiverOpt.get.posOpt
        else info.sig.id.attr.posOpt
      val mpos = info.sig.id.attr.posOpt.get

      var recCount = 0
      for (cm <- context.compMethods if cm == ctx) {
        recCount = recCount + 1
      }
      if (config.callBound > 0 && recCount > config.callBound) {
        reporter.warn(posOpt, Logika.kind,
          st"""Under-approximation due to recursive call capped with bound ${config.callBound} on $resST:
              |${for (i <- context.compMethods.size - 1 to 0) yield st"- ${(context.compMethods(i), ".")}"}""".render)
        return ISZ((s(status = State.Status.Error), State.errorValue))
      }

      val (s0, callerLocalMap): (State, LocalSaveMap) = {
        val (s1, m) = saveLocals(-(context.compMethods.size + 1), s, context.methodName)
        var s2 = s1
        receiverOpt match {
          case Some(receiver) =>
            val (s3, sym) = idIntro(mpos, s2, ctx, "this", receiver.tipe, Some(mpos))
            s2 = s3.addClaim(State.Claim.Eq(sym, receiver))
          case _ =>
        }
        for (paramArg <- paramArgs) {
          val (l, _, _, v) = paramArg
          val (s3, sym) = idIntro(mpos, s2, l.context, l.id, v.tipe, Some(mpos))
          s2 = s3.addClaim(State.Claim.Eq(sym, v))
        }
        (s2, m)
      }

      var r = ISZ[(State, State.Value)]()

      val stateMethods: ISZ[(State, Either[Info.Method, State.Value])] = if (info.res.isInObject) {
        th.nameMap.get(ctx).get match {
          case minfo: Info.Method => ISZ((s0, Either.Left(Info.substMethod(minfo, typeSubstMap))))
          case _ => halt(s"Infeasible: ${resST.render}")
        }
      } else {
        resolveVirtualInvoke(posOpt, info, s0, receiverOpt.get, typeSubstMap)
      }

      def evalMethod(s1: State, minfo: Info.Method): Unit = {
        val l = logikaMethod(context.nameExePathMap, context.maxCores, context.fileOptions, th, config,
          minfo.ast.isHelper, minfo.ast.hasInline, res.owner, res.id, receiverOpt.map(t => t.tipe), info.sig.paramIdTypes,
          info.sig.returnType.typedOpt.get, receiverPosOpt, ISZ(), ISZ(), ISZ(), ISZ(), ISZ(), plugins, Some(
            (s"(${if (res.owner.isEmpty) "" else res.owner(res.owner.size - 1)}${if (res.isInObject) '.' else '#'}${res.id}) ",
              info.sig.id.attr.posOpt.get)),
          this.context.compMethods :+ (res.owner :+ res.id)
        )
        var s2vs = ISZ[(State, State.Value)]()
        info.strictPureBodyOpt match {
          case Some(body) => s2vs = l.evalAssignExpValue(split, smt2, cache, retType, rtCheck, s1, body, reporter)
          case _ =>
            if (retType == AST.Typed.unit) {
              val unit = State.Value.Unit(pos)
              for (s2 <- evalStmts(l, split, smt2, cache, None(), rtCheck, s1, minfo.ast.bodyOpt.get.stmts, reporter)) {
                s2vs = s2vs :+ ((s2, unit))
              }
            } else {
              for (s2 <- evalStmts(l, split, smt2, cache, None(), rtCheck, s1, minfo.ast.bodyOpt.get.stmts, reporter)) {
                val (s3, sym) = idIntro(pos, s2, ctx, "Res", retType, None())
                s2vs = s2vs :+ ((s3, sym))
              }
            }
        }
        for (s2v <- s2vs) {
          val (s2, retVal) = s2v
          if (s2.status == State.Status.Error) {
            r = r :+ ((s2, State.errorValue))
          } else {
            var s3 = s2(status = State.Status.Normal)
            var assigns = ISZ[(AST.Exp, State.Value.Sym)]()
            val ids = Util.collectLocals(s3, ctx)
            if (minfo.ast.purity == AST.Purity.Impure) {
              receiverOpt match {
                case Some(receiver) =>
                  val t = receiver.tipe
                  if (th.isMutable(t)) {
                    val (s4, sym) = idIntro(pos, s3, ctx, "this", t, None())
                    invokeReceiverOpt match {
                      case Some(invokeReceiver) => assigns = assigns :+ ((invokeReceiver, sym))
                      case _ => assigns = assigns :+ ((AST.Exp.This(ctx, AST.TypedAttr(posOpt, Some(t))), sym))
                    }
                    s3 = s4
                  }
                case _ =>
              }
              for (paramArg <- paramArgs) {
                val (l, _, e, v) = paramArg
                if (th.isMutable(v.tipe)) {
                  val (s4, sym) = idIntro(pos, s3, ctx, l.id, v.tipe, None())
                  assigns = assigns :+ ((e, sym))
                  s3 = s4
                }
              }
              s3 = rewriteLocals(s3, F, ctx, ids)._1
            } else {
              s3 = rewriteLocals(s3, F, ctx, ids)._1
            }
            s3 = restoreLocals(s3, callerLocalMap)
            var s4s = ISZ(s3)
            for (assign <- assigns) {
              var s5s = ISZ[State]()
              for (s4 <- s4s) {
                assign._1 match {
                  case lhs: AST.Exp.This =>
                    var (s5, thiz) = idIntro(lhs.posOpt.get, s4, context.methodName, "this", context.receiverTypeOpt.get, None())
                    s5 = s5.addClaim(State.Claim.Old(T, F, context.methodName, "this", thiz, lhs.posOpt.get))
                    s5s = s5s :+ evalAssignLocalH(F, s5, context.methodName, "this", assign._2, lhs.posOpt, reporter)
                  case lhs =>
                    s5s = s5s ++ assignRec(split, smt2, cache, rtCheck, s4, lhs, assign._2, reporter)
                }
              }
              s4s = s5s
            }
            for (s4 <- s4s) {
              r = r :+ ((s4, retVal))
            }
          }
        }
      }

      for (p <- stateMethods) {
        p._2 match {
          case Either.Left(method) => evalMethod(if (context.pathConditionsOpt.isEmpty) removeOld(p._1) else p._1, method)
          case Either.Right(v) => r = r :+ ((p._1, v))
        }
      }

      val nextFresh = maxStateValuesNextFresh(r)
      return for (s6v <- r) yield (s6v._1(nextFresh = nextFresh), s6v._2)
    }

    def compositional(posOpt: Option[Position], info: Context.InvokeMethodInfo, s: State,
                      typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed, invokeReceiverOpt: Option[AST.Exp],
                      receiverOpt: Option[State.Value.Sym], paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]): ISZ[(State, State.Value)] = {
      val res = info.res
      val ctx = res.owner :+ res.id
      val pos = posOpt.get
      val resST = methodResST(res)
      val contract = info.contract
      val isUnit = info.sig.returnType.typedOpt == AST.Typed.unitOpt
      val receiverPosOpt: Option[Position] =
        if (invokeReceiverOpt.nonEmpty) invokeReceiverOpt.get.posOpt
        else info.sig.id.attr.posOpt
      val invs: ISZ[Info.Inv] =
        if (info.isHelper || info.strictPureBodyOpt.nonEmpty) ISZ()
        else retrieveInvs(res.owner, res.isInObject)
      var r = ISZ[(State, State.Value)]()
      for (cm <- context.compMethods if cm == ctx) {
        reporter.error(posOpt, kind, st"Cannot use ${(res.owner :+ res.id, ".")}'s contracts cyclicly".render)
        r = r :+ ((s(status = State.Status.Error), State.errorValue))
        return r
      }

      var s1 = s
      var oldVars = HashSMap.empty[String, State.Value.Sym]
      if (ctx == context.methodName) {
        for (paramArg <- paramArgs) {
          val id = paramArg._1.id
          val (s2, sym) = idIntro(pos, s1, ctx, paramArg._1.id, paramArg._4.tipe.subst(typeSubstMap), None())
          oldVars = oldVars + id ~> sym
          s1 = s2
        }
        s1 = rewriteLocals(s1, F, ctx, oldVars.keys ++ (if (receiverOpt.isEmpty) ISZ[String]() else ISZ[String]("this")))._1
      }
      for (q <- paramArgs) {
        val (l, _, arg, v) = q
        val argPosOpt = arg.posOpt
        val (s3, sym) = idIntro(arg.posOpt.get, s1, l.context, l.id, v.tipe, argPosOpt)
        val (s4, vSym) = value2Sym(s3, v, argPosOpt.get)
        s1 = s4.addClaim(State.Claim.Eq(sym, vSym))
      }

      val lComp: Logika = {
        val l = logikaMethod(context.nameExePathMap, context.maxCores, context.fileOptions, th, config, info.isHelper,
          info.hasInline, res.owner, res.id, receiverOpt.map(t => t.tipe), info.sig.paramIdTypes,
          info.sig.returnType.typedOpt.get, receiverPosOpt, contract.reads, ISZ(), contract.modifies, ISZ(), ISZ(),
          plugins, Some(
            (s"(${if (res.owner.isEmpty) "" else res.owner(res.owner.size - 1)}${if (res.isInObject) '.' else '#'}${res.id}) ",
              info.sig.id.attr.posOpt.get)),
          this.context.compMethods :+ (res.owner :+ res.id)
        )
        if (context.pathConditionsOpt.isEmpty) {
          s1 = removeOld(s1)
        }
        val mctx = l.context.methodOpt.get
        var objectVarInMap = mctx.objectVarInMap
        for (p <- mctx.modObjectVarMap(typeSubstMap).entries) {
          val (ids, (t, _)) = p
          val (s4, sym) = nameIntro(pos, s1, ids, t, None())
          objectVarInMap = objectVarInMap + ids ~> sym
          s1 = s4
        }
        var fieldVarInMap = mctx.fieldVarInMap
        mctx.receiverTypeOpt match {
          case Some(receiverType) =>
            val fieldVarMap = mctx.fieldVarMap(typeSubstMap)
            if (fieldVarMap.nonEmpty) {
              val (s5, thiz) = idIntro(mctx.posOpt.get, s1, mctx.name, "this", receiverType, mctx.posOpt)
              s1 = s5
              for (p <- mctx.fieldVarMap(typeSubstMap).entries) {
                val (id, (t, posOpt)) = p
                val (s6, sym) = s1.freshSym(t, posOpt.get)
                s1 = s6.addClaim(State.Claim.Let.FieldLookup(sym, thiz, id))
                fieldVarInMap = fieldVarInMap + id ~> sym
              }
            }
          case _ =>
        }
        var localInMap = mctx.localInMap
        for (p <- mctx.localMap(typeSubstMap).entries) {
          val (id, (_, ctx, _, t)) = p
          val (s7, sym): (State, State.Value.Sym) = idIntro(pos, s1, ctx, id, t, None())
          localInMap = localInMap + id ~> sym
          s1 = s7
        }
        l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
          localInMap = localInMap))))
      }

      val (receiverModified, modLocals) = contract.modifiedLocalVars(lComp.context.receiverLocalTypeOpt, typeSubstMap)

      val pfOpt: Option[State.ProofFun] = if (config.pureFun ||
        (info.sig.funType.isPureFun && !info.hasBody && info.contract.isEmpty)) {
        val typedAttr = AST.TypedAttr(posOpt, None())
        val (s8, pf) = Util.pureMethod(context.nameExePathMap, context.maxCores, context.fileOptions, th, config,
          plugins, smt2, cache, s1, lComp.context.receiverTypeOpt, info.sig.funType.subst(typeSubstMap),
          lComp.context.methodOpt.get.owner, info.sig.id.value, info.isHelper, F, for (p <- info.sig.params) yield p.id,
          AST.Stmt.Expr(AST.Exp.Result(None(), typedAttr), typedAttr), reporter, lComp.context.implicitCheckTitlePosOpt)
        s1 = s8
        Some(pf)
      } else {
        None()
      }

      def evalContractCase(logikaComp: Logika, callerReceiverOpt: Option[State.Value.Sym], assume: B, cs0: State,
                           labelOpt: Option[AST.Exp.LitString], requires: ISZ[AST.Exp],
                           ensures: ISZ[AST.Exp]): Context.ContractCaseResult = {

        def modVarsResult(ms0: State, mposOpt: Option[Position]): (State, State.Value.Sym) = {
          var ms1 = ms0
          val modObjectVars = contract.modifiedObjectVars
          val mpos = mposOpt.get
          for (p <- modObjectVars.entries) {
            val (res, (t, pos)) = p
            val (ms2, sym) = nameIntro(mpos, ms1, res.owner :+ res.id, t, None())
            ms1 = ms2.addClaim(State.Claim.Old(F, res.isSpec, res.owner, res.id, sym, pos))
          }
          ms1 = rewriteObjectVars(logikaComp, smt2, cache, rtCheck, ms1, modObjectVars, mpos, reporter)
          var oldIdMap = HashMap.empty[ISZ[String], State.Value.Sym]
          for (pair <- modLocals.entries) {
            val (info, (t, _)) = pair
            val (ls0, sym) = idIntro(pos, ms1, info.context, info.id, t, None())
            ms1 = ls0
            oldIdMap = oldIdMap + (info.context :+ info.id) ~> sym
          }
          ms1 = rewriteLocalVars(logikaComp, ms1, T, modLocals.keys, mposOpt, reporter)
          for (pair <- modLocals.entries) {
            val (info, (t, pos)) = pair
            val oldSym = oldIdMap.get(info.context :+ info.id).get
            val (ls1, newSym) = idIntro(pos, ms1, info.context, info.id, t, Some(pos))
            val ls2 = Util.assumeValueInv(this, smt2, cache, rtCheck, ls1, newSym, pos, reporter)
            if (AST.Util.isSeq(t)) {
              val (ls5, size1) = ls2.freshSym(AST.Typed.z, pos)
              val (ls6, size2) = ls5.freshSym(AST.Typed.z, pos)
              val (ls7, cond) = ls6.freshSym(AST.Typed.b, pos)
              val ls8 = ls7.addClaims(ISZ[State.Claim](
                State.Claim.Let.FieldLookup(size1, oldSym, "size"),
                State.Claim.Let.FieldLookup(size2, newSym, "size"),
                State.Claim.Let.Binary(cond, size2, AST.Exp.BinaryOp.Eq, size1, AST.Typed.z),
                State.Claim.Prop(T, cond)
              ))
              ms1 = ls8
            } else {
              ms1 = ls2
            }
          }
          if (isUnit) {
            return ms1.freshSym(AST.Typed.unit, mpos)
          } else {
            val (ms2, v) = resIntro(mpos, ms1, ctx, retType, mposOpt)
            ms1 = ms2
            return (ms1, v)
          }
        }

        def modVarsRewrite(ms0: State, modPosOpt: Option[Position]): State = {
          var ms1 = ms0
          var newVars = oldVars
          for (q <- paramArgs) {
            val (p, t, arg, _) = q
            if (modLocals.contains(p)) {
              val (ms2, v) = idIntro(arg.posOpt.get, ms1, p.context, p.id, t, None())
              ms1 = singleState(assignRec(Split.Disabled, smt2, cache, rtCheck, ms2, arg, v, reporter))
              if (newVars.contains(p.id)) {
                newVars = newVars + p.id ~> v
              }
            }
          }
          var rwLocals: ISZ[AST.ResolvedInfo.LocalVar] = for (q <- paramArgs) yield q._1
          if (!isUnit) {
            rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, T, T, "Res")
          }
          if (receiverOpt.nonEmpty) {
            rwLocals = rwLocals :+ AST.ResolvedInfo.LocalVar(ctx, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, "this")
          }
          ms1 = rewriteLocalVars(logikaComp, ms1, F, rwLocals, modPosOpt, reporter)
          if (newVars.nonEmpty) {
            for (q <- paramArgs) {
              val p = q._1
              newVars.get(p.id) match {
                case Some(v) => ms1 = ms1.addClaim(State.Claim.Let.CurrentId(T, v, ctx, p.id, posOpt))
                case _ =>
              }
            }
          }
          callerReceiverOpt match {
            case Some(receiver) =>
              val (ms2, receiverSym) = idIntro(receiver.pos, ms1, context.methodOpt.get.name, "this", receiver.tipe, Some(receiver.pos))
              ms1 = ms2.addClaim(State.Claim.Eq(receiverSym, receiver))
            case _ =>
          }
          return ms1
        }

        def evalRequires(cs1: State, label: String, rep: Reporter): (State, ISZ[State.Value]) = {
          var requireSyms = ISZ[State.Value]()
          var i = 0
          var csr0 = cs1
          val pLocals: ISZ[AST.ResolvedInfo] = for (p <- paramArgs) yield p._1.asInstanceOf[AST.ResolvedInfo]
          for (require <- requires if csr0.ok) {
            val title: String =
              if (requires.size == 1) st"${label}re-condition of $resST".render
              else st"${label}re-condition#$i of $resST".render

            val (csr1, sym): (State, State.Value.Sym) =
              if (assume) {
                val p = logikaComp.evalAssume(smt2, cache, F, title, csr0, AST.Util.substExp(require, typeSubstMap), posOpt, rep)
                val size = p._1.claims.size
                assert(p._1.claims(size - 1) == State.Claim.Prop(T, p._2))
                (p._1(claims = ops.ISZOps(p._1.claims).dropRight(1)), p._2)
              } else {
                logikaComp.evalAssert(smt2, cache, F, title, csr0, AST.Util.substExp(require, typeSubstMap), posOpt,
                  pLocals, rep)
              }
            requireSyms = requireSyms :+ sym
            csr0 = csr1
            i = i + 1
          }
          return (csr0, requireSyms)
        }

        def evalEnsures(cs1: State, label: String, rep: Reporter): State = {
          val claims: ISZ[AST.Exp] = for (ensure <- ensures) yield AST.Util.substExp(ensure, typeSubstMap)
          var i = 0
          var cse3 = cs1
          for (ensure <- claims if cse3.ok) {
            val title: String =
              if (ensures.size == 1) st"${label}ost-condition of $resST".render
              else st"${label}ost-condition#$i of $resST".render
            cse3 = logikaComp.evalAssume(smt2, cache, F, title, cse3, ensure, posOpt, rep)._1
            i = i + 1
          }
          return cse3
        }

        val rep = reporter.empty
        val (label, cs1): (String, State) = labelOpt match {
          case Some(lbl) if lbl.value.size == 0 =>
            (s"(${lbl.value}) p", cs0.addClaim(State.Claim.Label(lbl.value, lbl.posOpt.get)))
          case _ => ("P", cs0)
        }
        val (cs2, requireSyms) = evalRequires(cs1, label, rep)
        if (!cs2.ok) {
          val (cs3, rsym) = cs2.freshSym(AST.Typed.b, pos)
          return Context.ContractCaseResult(F, cs3.addClaim(State.Claim.Let.And(rsym, requireSyms)),
            State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
        }
        val (cs4, result) = modVarsResult(cs2, posOpt)
        var cs5 = evalEnsures(cs4, label, rep)

        pfOpt match {
          case Some(pf) =>
            val (cs6, sym) = cs5.freshSym(pf.returnType, pos)
            var args: ISZ[State.Value] = if (pf.receiverTypeOpt.nonEmpty) ISZ[State.Value](receiverOpt.get) else ISZ()
            for (pa <- paramArgs) {
              args = args :+ pa._4
            }
            cs5 = cs6.addClaims(ISZ(State.Claim.Let.ProofFunApply(sym, pf, args), State.Claim.Eq(result, sym)))
          case _ =>
        }

        if (!cs5.ok) {
          val (cs6, rsym) = cs5.freshSym(AST.Typed.b, pos)
          return Context.ContractCaseResult(T, cs6.addClaim(State.Claim.Let.And(rsym, requireSyms)),
            State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
        }
        val (cs10, rcvOpt): (State, Option[State.Value.Sym]) = if (receiverOpt.nonEmpty) {
          receiverOpt match {
            case Some(receiver) if invs.nonEmpty =>
              val (cs7, rcv) = idIntro(pos, cs5, ctx, "this", receiver.tipe, None())
              if (isUnit) {
                (cs7, Some(rcv))
              } else {
                val (cs8, res) = resIntro(pos, cs7, ctx, retType, None())
                val cs9 = assumeValueInv(logikaComp, smt2, cache, rtCheck, cs8, res, pos, reporter)
                (cs9, Some(rcv))
              }
            case _ => (cs5, receiverOpt)
          }
        } else {
          (cs5, None())
        }
        val cs11 = Util.checkInvs(logikaComp, posOpt, T, "Post-invariant", smt2, cache, rtCheck, cs10,
          logikaComp.context.receiverTypeOpt, rcvOpt, invs, typeSubstMap, reporter)
        val cs12 = evalAssignReceiver(
          if (receiverModified) contract.modifies else ISZ(),
          this, logikaComp, smt2, cache, rtCheck, cs11, invokeReceiverOpt, receiverOpt, typeSubstMap, reporter)
        val cs13 = modVarsRewrite(cs12, posOpt)
        val (cs14, rsym) = cs13.freshSym(AST.Typed.b, pos)
        val cs15 = cs14.addClaim(State.Claim.Let.And(rsym, requireSyms))
        return Context.ContractCaseResult(T, cs15, result, State.Claim.Prop(T, rsym), rep.messages)
      }

      val callerReceiverOpt: Option[State.Value.Sym] = context.methodOpt match {
        case Some(m) => m.receiverTypeOpt match {
          case Some(currentReceiverType) =>
            val lcontext = context.methodOpt.get.name
            val p = idIntro(posOpt.get, s1, lcontext, "this", currentReceiverType, None())
            s1 = p._1
            if (receiverModified && context.methodName == lcontext) {
              s1 = rewriteLocal(this, s1, F, lcontext, "this", posOpt, reporter)
            }
            Some(p._2)
          case _ => None()
        }
        case _ => None()
      }
      receiverOpt match {
        case Some(receiver) =>
          val (s2, receiverSym) = idIntro(receiver.pos, s1, res.owner :+ res.id, "this", receiver.tipe, receiverPosOpt)
          s1 = s2.addClaim(State.Claim.Eq(receiverSym, receiver))
        case _ =>
      }
      s1 = {
        val pis = Util.checkInvs(lComp, posOpt, F, "Pre-invariant", smt2, cache, rtCheck, s1,
          lComp.context.receiverTypeOpt, receiverOpt, invs, typeSubstMap, reporter)
        s1(status = pis.status, nextFresh = pis.nextFresh)
      }
      contract match {
        case contract: AST.MethodContract.Simple if s1.ok =>
          val ccr = evalContractCase(lComp, callerReceiverOpt, F, s1, None(), contract.requires, contract.ensures)
          reporter.reports(ccr.messages)
          r = r :+ ((ccr.state, ccr.retVal))
        case contract: AST.MethodContract.Cases if s1.ok =>
          val root = s1
          var isPreOK = F
          var ccrs = ISZ[Context.ContractCaseResult]()
          var okCcrs = ISZ[Context.ContractCaseResult]()
          for (cas <- contract.cases) {
            val ccr = evalContractCase(lComp, callerReceiverOpt, T, s1,
              if (cas.label.value == "") None() else Some(cas.label), cas.requires, cas.ensures)
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
            r = r :+ ((s1(status = State.Status.Error), State.errorValue))
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
              ops.ISZOps(okCcrs).foldLeft((nf: Z, ccr: Context.ContractCaseResult) =>
                if (nf < ccr.state.nextFresh) ccr.state.nextFresh else nf, -1)
            assert(nextFresh >= 0)
            if (!isUnit) {
              nextFresh = nextFresh + 1
            }
            if (shouldSplit) {
              for (ccr <- okCcrs) {
                val cs = ccr.requiresClaim +:
                  ops.ISZOps(ccr.state.claims).slice(root.claims.size, ccr.state.claims.size)
                val claims = ops.ISZOps(ccr.state.claims).slice(0, root.claims.size) ++ cs
                r = r :+ ((ccr.state(nextFresh = nextFresh, claims = claims), ccr.retVal))
              }
            } else {
              var claims = ISZ[State.Claim]()
              var map = HashMap.empty[State.Claim.Prop, ISZ[State.Claim]]
              for (i <- 0 until root.claims.size) {
                val rootClaim = root.claims(i)
                if (ops.ISZOps(okCcrs).forall((ccr: Context.ContractCaseResult) => ccr.state.claims(i) == rootClaim)) {
                  claims = claims :+ rootClaim
                } else {
                  for (ccr <- okCcrs) {
                    val l = map.get(ccr.requiresClaim).getOrElse(ISZ())
                    map = map + ccr.requiresClaim ~> (l :+ ccr.state.claims(i))
                  }
                }
              }
              val implies: ISZ[State.Claim] = for (ccr <- okCcrs) yield State.Claim.Imply(T, ISZ(ccr.requiresClaim,
                bigAnd(
                  map.get(ccr.requiresClaim).getOrElse(ISZ()) ++
                    (for (i <- root.claims.size until ccr.state.claims.size) yield ccr.state.claims(i)))
              ))
              claims = claims ++ implies
              claims = claims :+ State.Claim.Or(for (ccr <- okCcrs) yield ccr.requiresClaim)
              s1 = s1(claims = claims)
              if (isUnit) {
                r = r :+ ((s1(nextFresh = nextFresh), okCcrs(0).retVal))
              } else {
                val (s8, sym) = s1.freshSym(retType, pos)
                s1 = s8
                r = r :+ ((s1(nextFresh = nextFresh).addClaims(
                  for (ccr <- okCcrs) yield State.Claim.Imply(T, ISZ(ccr.requiresClaim,
                    State.Claim.Let.Def(sym, ccr.retVal)))), sym))
              }
            }
          }
        case _ => r = r :+ ((s1, State.errorValue))
      }
      val oldR = r
      r = ISZ()
      var nextFresh: Z = -1
      for (sv <- oldR) {
        val s9 = sv._1
        if (s9.nextFresh > nextFresh) {
          nextFresh = s9.nextFresh
        }
        r = r :+ sv
      }
      r = for (sv <- r) yield (sv._1(nextFresh = nextFresh), sv._2)
      return r
    }

    def strictPure(pos: Position, info: Context.InvokeMethodInfo, s1: State, typeSubstMap: HashMap[String, AST.Typed],
                   retType: AST.Typed, receiverOpt: Option[State.Value.Sym],
                   paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)]): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      val mres = info.res
      val funType = mres.tpeOpt.get.subst(typeSubstMap)
      val b = info.strictPureBodyOpt.get
      val body: AST.AssignExp = if (typeSubstMap.isEmpty) {
        b
      } else {
        AST.Transformer(AST.Util.TypePrePostSubstitutor(typeSubstMap)).transformAssignExp(F, b).resultOpt.getOrElse(b)
      }
      val receiverTypeOpt: Option[AST.Typed] = if (mres.isInObject) {
        None()
      } else {
        th.typeMap.get(mres.owner).get match {
          case ti: TypeInfo.Sig => Some(ti.tpe.subst(typeSubstMap))
          case ti: TypeInfo.Adt => Some(ti.tpe.subst(typeSubstMap))
          case _ => halt("Infeasible")
        }
      }
      val (s2, pf) = pureMethod(context.nameExePathMap, context.maxCores, context.fileOptions, th, config, plugins,
        smt2, cache, s1, receiverTypeOpt, funType, mres.owner, mres.id, info.isHelper, T,
        for (p <- info.sig.params) yield p.id, body, reporter, context.implicitCheckTitlePosOpt)
      val (s3, re) = s2.freshSym(retType, pos)
      var args: ISZ[State.Value] = for (q <- paramArgs) yield q._4
      receiverOpt match {
        case Some(receiver) => args = receiver +: args
        case _ =>
      }
      r = r :+ ((s3.addClaim(State.Claim.Let.ProofFunApply(re, pf, args)), re))
      return r
    }

    def evalInvokeSynthetic(s0: State, res: AST.ResolvedInfo.Method, receiverExpOpt: Option[AST.Exp],
                            eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]],
                            pos: Position): Option[ISZ[(State, State.Value)]] = {
      def fromZ(t: AST.Typed, minOpt: Option[Z], maxOpt: Option[Z]): Option[ISZ[(State, State.Value)]] = {
        val argExp: AST.Exp = eargs match {
          case Either.Left(s) => s(0)
          case Either.Right(s) => s(0).arg
        }
        var r = ISZ[(State, State.Value)]()
        for (p <- evalExp(split, smt2, cache, rtCheck, s0, argExp, reporter)) {
          val arg = p._2
          val s5: State = (minOpt, maxOpt) match {
            case (Some(min), Some(max)) =>
              val (s1, symLe) = p._1.freshSym(AST.Typed.b, pos)
              val (s2, symGe) = s1.freshSym(AST.Typed.b, pos)
              val (s3, symCond) = s2.freshSym(AST.Typed.b, pos)
              val s4 = s3.addClaims(ISZ(
                State.Claim.Let.Binary(symLe, State.Value.Z(min, pos), AST.Exp.BinaryOp.Le, arg, AST.Typed.z),
                State.Claim.Let.Binary(symGe, arg, AST.Exp.BinaryOp.Le, State.Value.Z(max, pos), AST.Typed.z),
                State.Claim.Let.Binary(symCond, symLe, AST.Exp.BinaryOp.And, symGe, AST.Typed.b)
              ))
              evalAssertH(T, smt2, cache, s"$t.fromZ range check", s4, symCond, Some(pos), ISZ(), reporter)
              p._1
            case (Some(min), _) =>
              val (s1, symCond) = p._1.freshSym(AST.Typed.b, pos)
              val s2 = s1.addClaim(
                State.Claim.Let.Binary(symCond, State.Value.Z(min, pos), AST.Exp.BinaryOp.Le, arg, AST.Typed.z)
              )
              evalAssertH(T, smt2, cache, s"$t.fromZ range check", s2, symCond, Some(pos), ISZ(), reporter)
              p._1
            case (_, Some(max)) =>
              val (s1, symCond) = p._1.freshSym(AST.Typed.b, pos)
              val s2 = s1.addClaim(
                State.Claim.Let.Binary(symCond, arg, AST.Exp.BinaryOp.Le, State.Value.Z(max, pos), AST.Typed.z)
              )
              evalAssertH(T, smt2, cache, s"$t.fromZ range check", s2, symCond, Some(pos), ISZ(), reporter)
              p._1
            case (_, _) => p._1
          }
          val (s6, symT) = s5.freshSym(t, pos)
          val (s7, symZ) = s6.freshSym(AST.Typed.z, pos)
          r = r :+ ((s7.addClaims(ISZ(
            State.Claim.Let.Random(symT, T, pos),
            State.Claim.Let.FieldLookup(symZ, symT, "toZ"),
            State.Claim.Eq(symZ, arg)
          )), symT))
        }
        return Some(r)
      }
      def fieldLookup(id: String, t: AST.Typed): Option[ISZ[(State, State.Value)]] = {
        var r = ISZ[(State, State.Value)]()
        for (p <- evalExp(split, smt2, cache, rtCheck, s0, receiverExpOpt.get, reporter)) {
          val (s1, sym) = p._1.freshSym(t, pos)
          r = r :+ ((s1.addClaim(State.Claim.Let.FieldLookup(sym, p._2, id)), sym))
        }
        return Some(r)
      }
      def random(tpe: AST.Typed.Name): Option[ISZ[(State, State.Value)]] = {
        val (s1, sym) = s0.freshSym(tpe, pos)
        val s2 = s1.addClaim(State.Claim.Let.Random(sym, F, pos))
        return Some(ISZ((Util.assumeValueInv(this, smt2, cache, rtCheck, s2, sym, pos, reporter), sym)))
      }
      def randomSeed(tpe: AST.Typed.Name): Option[ISZ[(State, State.Value)]] = {
        var r = ISZ[(State, State.Value)]()
        val pf = State.ProofFun(None(), tpe.ids, "randomSeed", F, ISZ("seed"), ISZ(AST.Typed.z), tpe)
        for (p <- evalArgs(split, smt2, cache, rtCheck, s0, 1, eargs, reporter)) {
          val s1 = p._1
          val args: ISZ[State.Value] = for (argOpt <- p._2) yield argOpt.get
          val (s2, sym) = s1.freshSym(tpe, pos)
          val s3 = s2.addClaim(State.Claim.Let.ProofFunApply(sym, pf, args))
          r = r :+ ((assumeValueInv(this, smt2, cache, rtCheck, s3, sym, pos, reporter), sym))
        }
        return Some(r)
      }
      def randomBetween(tpe: AST.Typed.Name): Option[ISZ[(State, State.Value)]] = {
        var r = ISZ[(State, State.Value)]()
        val posOpt = Option.some(pos)
        for (p <- evalArgs(split, smt2, cache, rtCheck, s0, 2, eargs, reporter)) {
          val s1 = p._1
          val args: ISZ[State.Value] = for (argOpt <- p._2) yield argOpt.get
          val (s2, cond) = s1.freshSym(AST.Typed.b, pos)
          val min = args(0)
          val max = args(1)
          evalAssertH(T, smt2, cache, s"$tpe.randomBetween min <= max", s2.addClaim(
            State.Claim.Let.Binary(cond, min, AST.Exp.BinaryOp.Le, max, tpe)), cond, posOpt, ISZ(), reporter)
          val (s4, sym) = s1.freshSym(tpe, pos)
          val (s5, condMin) = s4.freshSym(AST.Typed.b, pos)
          val (s6, condMax) = s5.freshSym(AST.Typed.b, pos)
          r = r :+ ((s6.addClaims(ISZ(
            State.Claim.Let.Random(sym, F, pos),
            State.Claim.Let.Binary(condMin, min, AST.Exp.BinaryOp.Le, sym, tpe),
            State.Claim.Let.Binary(condMax, sym, AST.Exp.BinaryOp.Le, max, tpe),
            State.Claim.Prop(T, condMin),
            State.Claim.Prop(T, condMax)
          )), sym))
        }
        return Some(r)
      }
      def randomSeedBetween(tpe: AST.Typed.Name): Option[ISZ[(State, State.Value)]] = {
        var r = ISZ[(State, State.Value)]()
        val posOpt = Option.some(pos)
        val pf = State.ProofFun(None(), tpe.ids, "randomSeedBetween", F, ISZ("seed", "min", "max"),
          ISZ(AST.Typed.z, tpe, tpe), tpe)
        for (p <- evalArgs(split, smt2, cache, rtCheck, s0, 3, eargs, reporter)) {
          val s1 = p._1
          val args: ISZ[State.Value] = for (argOpt <- p._2) yield argOpt.get
          val (s2, cond) = s1.freshSym(AST.Typed.b, pos)
          val min = args(1)
          val max = args(2)
          evalAssertH(T, smt2, cache, s"$tpe.randomSeedBetween min <= max", s2.addClaim(
            State.Claim.Let.Binary(cond, min, AST.Exp.BinaryOp.Le, max, tpe)), cond, posOpt, ISZ(), reporter)
          val (s4, sym) = s1.freshSym(tpe, pos)
          val (s5, condMin) = s4.freshSym(AST.Typed.b, pos)
          val (s6, condMax) = s5.freshSym(AST.Typed.b, pos)
          r = r :+ ((s6.addClaims(ISZ(
            State.Claim.Let.ProofFunApply(sym, pf, args),
            State.Claim.Let.Binary(condMin, min, AST.Exp.BinaryOp.Le, sym, tpe),
            State.Claim.Let.Binary(condMax, sym, AST.Exp.BinaryOp.Le, max, tpe),
            State.Claim.Prop(T, condMin),
            State.Claim.Prop(T, condMax)
          )), sym))
        }
        return Some(r)
      }

      res.owner match {
        case AST.Typed.bName =>
          res.id.native match {
            case "random" => return random(AST.Typed.b)
            case "randomSeed" => return randomSeed(AST.Typed.b)
            case _ =>
          }
        case AST.Typed.cName =>
          res.id.native match {
            case "fromZ" => return fromZ(AST.Typed.c, Some(0), Some(0x10FFFF))
            case "toZ" => return fieldLookup(res.id, AST.Typed.z)
            case "random" => return random(AST.Typed.c)
            case "randomBetween" => return randomBetween(AST.Typed.c)
            case "randomSeed" => return randomSeed(AST.Typed.c)
            case "randomSeedBetween" => return randomSeedBetween(AST.Typed.c)
            case _ =>
          }
        case AST.Typed.zName =>
          res.id.native match {
            case "random" => return random(AST.Typed.z)
            case "randomBetween" => return randomBetween(AST.Typed.z)
            case "randomSeed" => return randomSeed(AST.Typed.z)
            case "randomSeedBetween" => return randomSeedBetween(AST.Typed.z)
            case _ =>
          }
        case AST.Typed.rName =>
          res.id.native match {
            case "random" => return random(AST.Typed.r)
            case "randomBetween" => return randomBetween(AST.Typed.r)
            case "randomSeed" => return randomSeed(AST.Typed.r)
            case "randomSeedBetween" => return randomSeedBetween(AST.Typed.r)
            case _ =>
          }
        case AST.Typed.f32Name =>
          res.id.native match {
            case "random" => return random(AST.Typed.f32)
            case "randomBetween" => return randomBetween(AST.Typed.f32)
            case "randomSeed" => return randomSeed(AST.Typed.f32)
            case "randomSeedBetween" => return randomSeedBetween(AST.Typed.f32)
            case _ =>
          }
        case AST.Typed.f64Name =>
          res.id.native match {
            case "random" => return random(AST.Typed.f64)
            case "randomBetween" => return randomBetween(AST.Typed.f64)
            case "randomSeed" => return randomSeed(AST.Typed.f64)
            case "randomSeedBetween" => return randomSeedBetween(AST.Typed.f64)
            case _ =>
          }
        case AST.Typed.stringName =>
          res.id.native match {
            case "random" => return random(AST.Typed.string)
            case _ =>
          }
        case _ =>
      }
      if (res.isInObject) {
        th.typeMap.get(res.owner) match {
          case Some(info: TypeInfo.SubZ) =>
            val t = AST.Typed.Name(info.name, ISZ())
            res.id.native match {
              case "fromZ" =>
                val minOpt: Option[Z] = if (info.ast.hasMin || info.ast.isBitVector) Some(info.ast.min) else None()
                val maxOpt: Option[Z] = if (info.ast.hasMax || info.ast.isBitVector) Some(info.ast.max) else None()
                return fromZ(t, minOpt, maxOpt)
              case "random" => return random(t)
              case "randomBetween" => return randomBetween(t)
              case "randomSeed" => return randomSeed(t)
              case "randomSeedBetween" => return randomSeedBetween(t)
              case _ =>
            }
          case _ =>
            th.nameMap.get(res.owner) match {
              case Some(info: Info.Enum) =>
                val t = AST.Typed.Name(info.name :+ "Type", ISZ())
                res.id.native match {
                  case "random" => return random(t)
                  case "randomBetween" => return randomBetween(t)
                  case "randomSeed" => return randomSeed(t)
                  case "randomSeedBetween" => return randomSeedBetween(t)
                  case "numOfElements" => return Some(ISZ((s0, State.Value.Z(info.elements.size, pos))))
                  case "elements" =>
                    val elements = info.elements.keys
                    val (s1, sym) = s0.freshSym(AST.Typed.Name(AST.Typed.isName, ISZ(AST.Typed.z, AST.Typed.string)), pos)
                    return Some(ISZ((
                      s1.addClaim(State.Claim.Let.SeqLit(sym, for (i <- elements.indices) yield
                        State.Claim.Let.SeqLit.Arg(State.Value.Z(i, pos), State.Value.String(elements(i), pos)))),
                      sym)))
                  case "byName" =>
                    reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
                    return Some(ISZ((s0(status = State.Status.End), State.errorValue)))
                  case "byOrdinal" =>
                    reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
                    return Some(ISZ((s0(status = State.Status.End), State.errorValue)))
                  case _ =>
                }
              case _ =>
            }
        }
      } else {
        th.typeMap.get(res.owner) match {
          case Some(_: TypeInfo.Enum) =>
            res.id.native match {
              case "ordinal" => return fieldLookup(res.id, AST.Typed.z)
              case "name" => return fieldLookup(res.id, AST.Typed.string)
              case _ =>
            }
          case Some(_: TypeInfo.SubZ) =>
            res.id.native match {
              case "toZ" => return fieldLookup(res.id, AST.Typed.z)
              case _ =>
            }
          case _ =>
        }
      }
      receiverExpOpt match {
        case Some(receiver) => receiver.typedOpt match {
          case Some(t: AST.Typed.TypeVar) if t.isIndex =>
            res.id.native match {
              case "toZ" => return fieldLookup(res.id, AST.Typed.z)
              case _ =>
            }
          case _ =>
        }
        case _ =>
      }
      return None()
    }

    def evalInvoke(s0: State,
                   invokeReceiverOpt: Option[AST.Exp],
                   ident: AST.Exp.Ident,
                   eargs: Either[ISZ[AST.Exp], ISZ[AST.NamedArg]],
                   attr: AST.ResolvedAttr): ISZ[(State, State.Value)] = {
      val res = attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.Method]
      val posOpt = attr.posOpt
      val pos = posOpt.get
      val receiverPosOpt: Option[Position] =
        if (invokeReceiverOpt.nonEmpty) invokeReceiverOpt.get.posOpt
        else ident.posOpt

      evalInvokeSynthetic(s0, res, invokeReceiverOpt, eargs, pos) match {
        case Some(r) => return r
        case _ =>
      }

      val info = methodInfo(res.isInObject, res.owner, res.id)
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

      for (t <- stateSubstMapReceiverOpts) {
        var typeSubstMap = t._2
        val receiverOpt = t._3
        for (p <- evalArgs(split, smt2, cache, rtCheck, t._1, info.sig.params.size, eargs, reporter)) {
          val (s1, vs) = p
          if (s1.ok) {
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
            TypeChecker.unifyFun(Logika.kind, th, posOpt, TypeChecker.TypeRelation.Subtype, invokeType, mType, reporter) match {
              case Some(sm) =>
                typeSubstMap = typeSubstMap ++ sm.entries
                val retType = info.res.tpeOpt.get.ret.subst(typeSubstMap)
                val isStrictPure = info.strictPureBodyOpt.nonEmpty
                if (info.hasInline || ((if (isStrictPure) config.interp &&
                  config.strictPureMode != Config.StrictPureMode.Flip ||
                  !config.interp && config.strictPureMode == Config.StrictPureMode.Flip else config.interp) &&
                  !(config.interpContracts && info.contract.nonEmpty) && info.hasBody)) {
                  r = r ++ interprocedural(posOpt, info, s1, typeSubstMap, retType, invokeReceiverOpt, receiverOpt,
                    paramArgs)
                } else if (isStrictPure &&
                  (info.contract.isEmpty || config.strictPureMode == Config.StrictPureMode.Uninterpreted)) {
                  r = r ++ strictPure(pos, info, s1, typeSubstMap, retType, receiverOpt, paramArgs)
                } else {
                  var default = T
                  if (jescmPlugins._5.nonEmpty) {
                    for (p <- jescmPlugins._5 if default && p.canHandleCompositional(th, info)) {
                      default = F
                      r = r ++ p.handleCompositional(this, smt2, cache, rtCheck, split, posOpt, info, s1,
                        typeSubstMap, retType, invokeReceiverOpt, receiverOpt, paramArgs, reporter)
                    }
                  }
                  if (default) {
                    r = r ++ compositional(posOpt, info, s1, typeSubstMap, retType, invokeReceiverOpt,
                      receiverOpt, paramArgs)
                  }
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
        return evalExp(split, smt2, cache, rtCheck, state, tuple.args(0), reporter)
      }
      var r = ISZ[(State, State.Value)]()
      var nextFresh: Z = -1
      for (p <- evalExps(Split.Default, smt2, cache, rtCheck, state, tuple.args.size, (i: Z) => tuple.args(i), reporter)) {
        val (s0, args) = p
        if (s0.ok) {
          val (s1, sym) = s0.freshSym(tuple.typedOpt.get, tuple.posOpt.get)
          r = r :+ ((s1.addClaim(State.Claim.Let.TupleLit(sym, args)), sym))
          if (nextFresh < s1.nextFresh) {
            nextFresh = s1.nextFresh
          }
        } else {
          if (nextFresh < s0.nextFresh) {
            nextFresh = s0.nextFresh
          }
          r = r :+ ((s0, State.errorValue))
        }
      }
      return if (r.size > 1) r else for (p <- r) yield (p._1(nextFresh = nextFresh), p._2)
    }

    def evalIfExp(construct: String, sp: Split.Type, ifExp: AST.Exp.If): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      val shouldSplit: B = sp match {
        case Split.Default => config.splitAll || config.splitIf
        case Split.Enabled => T
        case Split.Disabled => F
      }
      val t = ifExp.typedOpt.get
      val pos = ifExp.posOpt.get
      for (p <- evalExp(sp, smt2, cache, rtCheck, state, ifExp.cond, reporter)) {
        val (s0, cond) = p
        if (s0.ok) {
          val (s1, sym) = value2Sym(s0, cond, ifExp.cond.posOpt.get)
          val prop = State.Claim.Prop(T, sym)
          val negProp = State.Claim.Prop(F, sym)
          val thenBranch = smt2.sat(context.methodName, config, cache, T,
            s"$construct-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims :+ prop, reporter)
          val elseBranch = smt2.sat(context.methodName, config, cache, T,
            s"$construct-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims :+ negProp, reporter)
          (thenBranch, elseBranch) match {
            case (T, T) =>
              val (s2, re) = s1.freshSym(t, pos)
              val s3vs = evalExp(sp, smt2, cache, rtCheck, s2.addClaim(prop), ifExp.thenExp, reporter)
              val s3NextFresh = maxStateValuesNextFresh(s3vs)
              val s4vs = evalExp(sp, smt2, cache, rtCheck, s2(nextFresh = s3NextFresh).addClaim(negProp), ifExp.elseExp, reporter)
              val s4NextFresh = maxStateValuesNextFresh(s4vs)
              if (shouldSplit) {
                for (s3v <- s3vs) {
                  val (s3t, tv) = s3v
                  val cs = prop +: ops.ISZOps(s3t.claims).slice(s2.claims.size + 1, s3t.claims.size)
                  val s3 = s3t(nextFresh = s4NextFresh, claims = ops.ISZOps(s3t.claims).slice(0, s2.claims.size) ++ cs)
                  r = r :+ ((s3, tv))
                }
                for (s4v <- s4vs) {
                  val (s4t, ev) = s4v
                  val cs = negProp +: ops.ISZOps(s4t.claims).slice(s2.claims.size + 1, s4t.claims.size)
                  val s4 = s4t(claims = ops.ISZOps(s4t.claims).slice(0, s2.claims.size) ++ cs)
                  r = r :+ ((s4, ev))
                }
              } else {
                for (s3v <- s3vs; s4v <- s4vs) {
                  val (s3, tv) = s3v
                  val (s4, ev) = s4v
                  val s5 = mergeStates(s1, sym, s3, s4, s4.nextFresh)
                  r = r :+ ((s5.addClaim(State.Claim.Let.Ite(re, sym, tv, ev)), re))
                }
              }
            case (T, F) => r = r ++ evalExp(sp, smt2, cache, rtCheck, s1.addClaim(prop), ifExp.thenExp, reporter)
            case (F, T) => r = r ++ evalExp(sp, smt2, cache, rtCheck, s1.addClaim(negProp), ifExp.elseExp, reporter)
            case (_, _) => r = r :+ ((s0(status = State.Status.Error), State.errorValue))
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      val nextFresh = maxStateValuesNextFresh(r)
      return for (p <- r) yield (p._1(nextFresh = nextFresh), p._2)
    }

    def evalRandomInt(): ISZ[(State, State.Value)] = {
      val pos = e.posOpt.get
      val (s1, sym) = state.freshSym(AST.Typed.z, pos)
      return ISZ((s1.addClaim(State.Claim.Let.Random(sym, F, pos)), sym))
    }

    def evalSeqIndexValidSize(targ: AST.Type, arg: AST.Exp): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (p <- evalExp(split, smt2, cache, rtCheck, state, arg, reporter)) {
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
      for (p <- evalArgs(split, smt2, cache, rtCheck, state, t.args.size, Either.Left(args), reporter)) {
        val (s0, valueOpts) = p
        if (s0.ok && ops.ISZOps(valueOpts).forall((vOpt: Option[State.Value]) => vOpt.nonEmpty)) {
          val (s1, sym) = s0.freshSym(t.ret, pos)
          r = r :+ ((s1.addClaim(State.Claim.Let.Apply(sym, isLocal, context, id, for (vOpt <- valueOpts) yield vOpt.get, t)), sym))
        } else {
          r = r :+ ((s0(nextFresh = s0.nextFresh + 1), State.errorValue))
        }
      }
      return r
    }

    def evalIsInBound(s0: State, receiver: AST.Exp, index: AST.Exp, attr: AST.ResolvedAttr): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (sv <- evalExp(split, smt2, cache, rtCheck, s0, receiver, reporter)) {
        for (sv2 <- evalExp(split, smt2, cache, rtCheck, sv._1, index, reporter)) {
          val s1 = sv2._1
          val rcv = sv._2
          val idx = sv2._2
          val (s2, sym) = s1.freshSym(AST.Typed.b, attr.posOpt.get)
          r = r :+ ((s2.addClaim(State.Claim.Let.SeqInBound(sym, rcv, idx)), sym))
        }
      }
      return r
    }

    def evalTypeCond(cond: AST.Exp.TypeCond): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      var nextFresh = state.nextFresh
      def evalTypeCondH(s0: State, args: ISZ[State.Value]): Unit = {
        var condIdTypes = ISZ[State.Value]()
        var paramMap = HashSMap.empty[String, AST.Exp]
        var s1 = s0
        for (p <- ops.ISZOps(args).zip(cond.fun.params)) {
          val id = p._2.idOpt.get
          val pos = id.attr.posOpt.get
          val (s2, arg) = value2Sym(s1, p._1, pos)
          val paramType = p._2.typedOpt.get
          val (s3, c) = s2.freshSym(AST.Typed.b, pos)
          s1 = s3.addClaim(State.Claim.Let.TypeTest(c, F, arg, paramType))
          condIdTypes = condIdTypes :+ c
          paramMap = paramMap + id.value ~> AST.Exp.Sym(arg.num, AST.TypedAttr(id.attr.posOpt, p._2.typedOpt))
        }
        val pos = cond.posOpt.get
        val antecedent: State.Value.Sym = if (condIdTypes.size == 1) {
          condIdTypes(0).asInstanceOf[State.Value.Sym]
        } else {
          val (s3, b) = s1.freshSym(AST.Typed.b, pos)
          s1 = s3.addClaim(State.Claim.Let.And(b, condIdTypes))
          b
        }
        val exp = Util.Substitutor(HashMap.empty, cond.fun.context, paramMap, reporter).
          transformExp(cond.fun.exp.asInstanceOf[AST.Stmt.Expr].exp).get
        for (p <- evalExp(split, smt2, cache, rtCheck, s1.addClaim(State.Claim.Prop(T, antecedent)), exp, reporter)) {
          val (s5, e) = p
          val (s6, res) = s5.freshSym(AST.Typed.b, pos)
          val s7 = s6.addClaim(State.Claim.Let.Binary(res, antecedent, AST.Exp.BinaryOp.Imply, e, AST.Typed.b))
          if (nextFresh < s7.nextFresh) {
            nextFresh = s7.nextFresh
          }
          val s7ClaimOps = ops.ISZOps(s7.claims)
          r = r :+ ((s7(claims = s7ClaimOps.slice(0, s1.claims.size) ++ s7ClaimOps.slice(s1.claims.size + 1, s7.claims.size)), res))
        }
      }
      for (p <- evalArgs(split, smt2, cache, rtCheck, state, cond.args.size, Either.Left[ISZ[AST.Exp], ISZ[AST.NamedArg]](cond.args), reporter)) {
        val (s0, argOpts) = p
        if (!s0.ok) {
          if (nextFresh < s0.nextFresh) {
            nextFresh = s0.nextFresh
          }
          r = r :+ ((s0, State.errorValue))
        } else {
          evalTypeCondH(s0, for (argOpt <- argOpts) yield argOpt.get)
        }
      }
      return for (p <- r) yield (p._1(nextFresh = nextFresh), p._2)
    }

    def expH(s0: State): ISZ[(State, State.Value)] = {
      e match {
        case lit: AST.Lit => return ISZ((s0, evalLit(smt2, lit, reporter)))
        case lit: AST.Exp.StringInterpolate =>
          lit.prefix match {
            case string"s" => return evalStringInterpolate(split, smt2, cache, rtCheck, s0, lit, reporter)
            case string"string" => return evalStringInterpolate(split, smt2, cache, rtCheck, s0, lit, reporter)
            case string"st" => return evalStringInterpolate(split, smt2, cache, rtCheck, s0, lit, reporter)
            case _ => return ISZ((s0, evalInterpolate(smt2, lit, reporter)))
          }
        case e: AST.Exp.Ident => return evalIdent(e)
        case e: AST.Exp.Select => return evalSelect(e)
        case e: AST.Exp.Unary => return evalUnaryExp(e)
        case e: AST.Exp.Binary => return evalBinaryExp(e)
        case e: AST.Exp.If => return evalIfExp("if", split, e)
        case e: AST.Exp.Tuple => return evalTupleExp(e)
        case e: AST.Exp.Invoke =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Select => return evalSeqSelect(e)
                case AST.MethodMode.Store => return evalSeqUpdate(e)
                case AST.MethodMode.Constructor =>
                  return evalConstructor(split, F, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
                case AST.MethodMode.Ext if res.id == "randomInt" && res.owner == AST.Typed.sireumName =>
                  return evalRandomInt()
                case AST.MethodMode.Spec =>
                  if (res.id == "seqIndexValidSize" && res.owner == AST.Typed.sireumName) {
                    return evalSeqIndexValidSize(e.targs(0), e.args(0))
                  } else {
                    return evalInvoke(s0, e.receiverOpt, e.ident, Either.Left(e.args), e.attr)
                  }
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
              e.ident.attr.typedOpt.get match {
                case t: AST.Typed.Fun if t.isPureFun => return evalApplyFun(e.posOpt.get, T, res.context, res.id, t, e.args)
                case _ =>
              }
            case _ =>
          }
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((s0(status = State.Status.Error), State.errorValue))
        case e: AST.Exp.InvokeNamed =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Constructor =>
                  return evalConstructor(split, F, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Copy =>
                  return evalConstructor(split, T, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Spec =>
                  if (res.id == "seqIndexValidSize" && res.owner == AST.Typed.sireumName) {
                    return evalSeqIndexValidSize(e.targs(0), e.args(0).arg)
                  } else {
                    return evalInvoke(s0, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                  }
                case AST.MethodMode.Method =>
                  return evalInvoke(s0, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case AST.MethodMode.Ext =>
                  return evalInvoke(s0, e.receiverOpt, e.ident, Either.Right(e.args), e.attr)
                case _ =>
              }
            case _ =>
          }
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((s0(status = State.Status.Error), State.errorValue))
        case e: AST.Exp.Result => return ISZ(evalResult(e))
        case e: AST.Exp.Input => return ISZ(evalInput(e))
        case e: AST.Exp.Old => return ISZ(evalOld(e))
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
        case e: AST.Exp.At => return ISZ(evalAt(e))
        case e: AST.Exp.TypeCond => return evalTypeCond(e)
        case e: AST.Exp.Sym => return ISZ[(State, State.Value)]((state, State.Value.Sym(e.num, e.typedOpt.get, e.posOpt.get)))
        case e: AST.Exp.StrictPureBlock => return evalAssignExpValue(split, smt2, cache, e.typedOpt.get, rtCheck,
          s0, e.block, reporter)
        case e: AST.Exp.Labeled => return evalExp(split, smt2, cache, rtCheck, state, e.exp, reporter)
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((s0(status = State.Status.Error), State.errorValue))
      }
    }

    def checkSplits(): ISZ[(State, State.Value)] = {
      val cachedExp: B = e match {
        case _: AST.Exp.If => T
        case _: AST.Exp.StrictPureBlock => T
        case _ => F
      }
      if (config.transitionCache && cachedExp && state.ok) {
        cache.getAssignExpTransitionAndUpdateSmt2(th, config,
          AST.Stmt.Expr(e, AST.TypedAttr(e.posOpt, e.typedOpt)), context.methodName, state, smt2) match {
          case Some((svs, cached)) =>
            reporter.coverage(F, cached, e.posOpt.get)
            return svs
          case _ =>
        }
      }
      val svs = expH(state)
      def check(): B = {
        if (!(svs.size > 0)) {
          return F
        }
        var nextFresh: Z = -1
        for (sv <- svs if nextFresh == -1) {
          nextFresh = sv._1.nextFresh
        }
        if (nextFresh < 0) {
          return F
        }
        val r = svs.size == 1 || ops.ISZOps(svs).forall((p: (State, State.Value)) => !p._1.ok || nextFresh == p._1.nextFresh)
        return r
      }
      assert(check(),
        st"""${e.posOpt.get}:
            |Split exp evaluation does not maintain nextFresh invariant for: ${e.prettyST}
            |${(for (sv <- svs) yield st"* ${sv._2.toRawST}: ${sv._1.toST}", "\n")}""".render)
      if (cachedExp) {
        if (config.transitionCache && ops.ISZOps(svs).
          forall((p: (State, State.Value)) => p._1.status != State.Status.Error)) {
          val cached = cache.setAssignExpTransition(th, config, AST.Stmt.Expr(e, AST.TypedAttr(e.posOpt, e.typedOpt)),
            context.methodName, state, svs, smt2)
          reporter.coverage(T, cached, e.posOpt.get)
        } else {
          reporter.coverage(F, zeroU64, e.posOpt.get)
        }
      }
      return svs
    }

    return checkSplits()
  }

  def value2Sym(s0: State, v: State.Value, pos: Position): (State, State.Value.Sym) = {
    v match {
      case v: State.Value.Sym => return (s0, v)
      case _ =>
        val (s2, symV) = s0.freshSym(v.tipe, pos)
        return (s2.addClaim(State.Claim.Let.Def(symV, v)), symV)
    }
  }

  def evalAssumeH(reportQuery: B, smt2: Smt2, cache: Logika.Cache, title: String, s0: State, sym: State.Value.Sym,
                  posOpt: Option[Position], reporter: Reporter): State = {
    val s1 = s0(claims = s0.claims :+ State.Claim.Prop(T, sym))
    if (config.sat && s1.ok) {
      val pos = posOpt.get
      val sat = smt2.sat(context.methodName, config, cache, reportQuery,
        s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims, reporter)
      return s1(status = State.statusOf(sat))
    } else {
      return s1
    }
  }

  def evalAssume(smt2: Smt2, cache: Logika.Cache, rtCheck: B, title: String, s0: State, cond: AST.Exp, posOpt: Option[Position],
                 reporter: Reporter): (State, State.Value.Sym) = {
    val pos = cond.posOpt.get
    val (s1, v) = singleStateValue(pos, s0, evalExp(Split.Disabled, smt2, cache, rtCheck, s0, cond, reporter))
    if (!s1.ok) {
      return value2Sym(s1, v, pos)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, pos)
    return (evalAssumeH(T, smt2, cache, title, s2, sym, posOpt, reporter), sym)
  }

  def evalAssertH(reportQuery: B, smt2: Smt2, cache: Logika.Cache, title: String, s0: State, sym: State.Value.Sym,
                  posOpt: Option[Position], rwLocals: ISZ[AST.ResolvedInfo], reporter: Reporter): State = {
    val conclusion = State.Claim.Prop(T, sym)
    val pos = posOpt.get
    if (isManual || config.searchPc) {
      val (pcs, concOpt, _) = Util.claimsToExpsLastOpt(jescmPlugins._4, pos, context.methodName, s0.claims :+ conclusion, th, config.atLinesFresh, T)
      val pcs2: HashSSet[AST.Exp] = if (rwLocals.nonEmpty) {
        val rwLocalSet = HashSet ++ rwLocals
        var substMap = HashMap.empty[AST.Exp, AST.Exp]
        for (pc <- pcs) {
          pc match {
            case pc@AST.Exp.Binary(left: AST.Exp.Ident, _, right) if Util.isEquivResOpt(th, pc.attr.resOpt, left.typedOpt.get) && rwLocalSet.contains(left.attr.resOpt.get) =>
              substMap = substMap + right ~> left
            case pc@AST.Exp.Binary(left: AST.Exp.Result, _, right) if Util.isEquivResOpt(th, pc.attr.resOpt, left.typedOpt.get) =>
              substMap = substMap + right ~> left
            case pc@AST.Exp.Binary(left, _, right: AST.Exp.Ident) if Util.isEquivResOpt(th, pc.attr.resOpt, left.typedOpt.get) && rwLocalSet.contains(right.attr.resOpt.get) =>
              substMap = substMap + left ~> right
            case pc@AST.Exp.Binary(left, _, right: AST.Exp.Result) if Util.isEquivResOpt(th, pc.attr.resOpt, left.typedOpt.get) =>
              substMap = substMap + left ~> right
            case _ =>
          }
        }
        val es = AST.Util.ExpSubstitutor(substMap)
        HashSSet ++ pcs ++ (for (pc <- pcs) yield es.transformExp(pc).getOrElseEager(pc))
      } else {
        HashSSet ++ pcs
      }
      concOpt match {
        case Some(conc) =>
          val normPCs = HashSet ++ PathConditions(th, pcs2.elements).normalize
          val normConclusion = th.normalizeExp(conc)
          if (normPCs.contains(normConclusion)) {
            reporter.inform(pos, Logika.Reporter.Info.Kind.Verified,
              st"""Accepted because the ${ops.StringOps(title).firstToLower} is in the path conditions:
                  |{
                  |  ${(for (pc2 <- pcs2.elements) yield pc2.prettyST, ";\n")}
                  |}""".render)
            return s0.addClaim(conclusion)
          }
        case _ =>
      }
      if (!config.searchPc) {
        reporter.error(posOpt, kind,
          st"""The ${ops.StringOps(title).firstToLower} has not been proven yet in the path conditions:
              |{
              |  ${(for (pc2 <- pcs2.elements) yield pc2.prettyST, ";\n")}
              |}""".render)
        return s0(status = State.Status.Error)
      }
    }
    if (s0.ok) {
      val r = smt2.valid(context.methodName, config, cache, reportQuery,
        s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s0.claims, conclusion, reporter)
      r.kind match {
        case Smt2Query.Result.Kind.Unsat => return s0.addClaim(conclusion)
        case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}", reporter)
        case Smt2Query.Result.Kind.Unknown => error(posOpt, s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds", reporter)
        case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower} holds", reporter)
        case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower} holds\n${r.info}", reporter)
      }
    }
    return s0(status = State.Status.Error)
  }

  def evalAssert(smt2: Smt2, cache: Logika.Cache, rtCheck: B, title: String, s0: State, cond: AST.Exp,
                 posOpt: Option[Position], rwLocals: ISZ[AST.ResolvedInfo],
                 reporter: Reporter): (State, State.Value.Sym) = {
    val pos = cond.posOpt.get
    val (s1, v) = singleStateValue(pos, s0, evalExp(Split.Disabled, smt2, cache, rtCheck, s0, cond, reporter))
    if (!s1.ok) {
      return value2Sym(s1, v, pos)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, pos)
    return (evalAssertH(T, smt2, cache, title, s2, sym, posOpt, rwLocals, reporter), sym)
  }

  def evalAssignExp(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rOpt: Option[State.Value.Sym], rtCheck: B,
                    s0: State, ae: AST.AssignExp, reporter: Reporter): ISZ[State] = {
    ae match {
      case ae: AST.Stmt.Expr =>
        ae.exp match {
          case e: AST.Exp.Invoke =>
            var r = ISZ[State]()
            for (p <- evalExprInvoke(split, smt2, cache, rtCheck, s0, ae, e, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.ok => r = r :+ s1.addClaim(State.Claim.Let.Def(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
          case _ =>
            var r = ISZ[State]()
            for (p <- evalExp(split, smt2, cache, rtCheck, s0, ae.exp, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.ok => r = r :+ s1.addClaim(State.Claim.Let.Def(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
        }
      case ae: AST.Stmt.Block => return evalBlock(split, smt2, cache, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.If => return evalIf(split, smt2, cache, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Match => return evalMatch(split, smt2, cache, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Return => return evalStmt(split, smt2, cache, rtCheck, s0, ae, reporter)._2
    }
  }

  def evalAssignExpValue(split: Split.Type, smt2: Smt2, cache: Logika.Cache, t: AST.Typed, rtCheck: B, s0: State,
                         ae: AST.AssignExp, reporter: Reporter): ISZ[(State, State.Value)] = {
    val pos = ae.asStmt.posOpt.get
    if (config.transitionCache && s0.ok) {
      cache.getAssignExpTransitionAndUpdateSmt2(th, config, ae, context.methodName, s0, smt2) match {
        case Some((svs, cached)) =>
          reporter.coverage(F, cached, pos)
          return svs
        case _ =>
      }
    }
    val r: ISZ[(State, State.Value)] = ae match {
      case ae: AST.Stmt.Expr => evalExp(split, smt2, cache, rtCheck, s0, ae.exp, reporter)
      case _ =>
        val (s1, sym) = s0.freshSym(t, pos)
        for (s2 <- evalAssignExp(split, smt2, cache, Some(sym), rtCheck, s1, ae, reporter)) yield (s2, sym)
    }
    if (config.transitionCache && ops.ISZOps(r).forall((p: (State, State.Value)) => p._1.status != State.Status.Error)) {
      val cached = cache.setAssignExpTransition(th, config, ae, context.methodName, s0, r, smt2)
      reporter.coverage(T, cached, pos)
    } else {
      reporter.coverage(F, zeroU64, pos)
    }
    return r
  }

  def evalAssignLocalH(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: State.Value.Sym,
                       idPosOpt: Option[Position], reporter: Reporter): State = {
    val s1: State = if (decl) s0 else rewriteLocal(this, s0, T, lcontext, id, idPosOpt, reporter)
    val (s2, lhs) = idIntro(idPosOpt.get, s1, lcontext, id, rhs.tipe, idPosOpt)
    return s2.addClaim(State.Claim.Eq(lhs, rhs))
  }

  def evalAssignObjectVarH(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, ids: ISZ[String], t: AST.Typed,
                           rhs: State.Value.Sym, namePosOpt: Option[Position], reporter: Reporter): State = {
    val poss = StateTransformer(CurrentNamePossCollector(ids)).transformState(ISZ(), s0).ctx
    if (poss.isEmpty && !config.interp && !context.hasInline) {
      reporter.error(namePosOpt, Logika.kind, st"Missing Modifies clause for ${(ids, ".")}.".render)
      return s0(status = State.Status.Error)
    }
    val (s1, num) = s0.fresh
    val objectVars = HashMap.empty[ISZ[String], (ISZ[Position], Z)] + ids ~> ((poss, num))
    val (s2, o1) = nameIntro(namePosOpt.get, s1, ids, t, None())
    val rt = StateTransformer(CurrentNameRewriter(objectVars)).transformState(F, s2)
    val s3 = rt.resultOpt.getOrElse(s1)
    val pos = namePosOpt.get
    val (s4, lhs) = nameIntro(namePosOpt.get, s3, ids, rhs.tipe, namePosOpt)
    val s5 = s4.addClaim(State.Claim.Eq(lhs, rhs))
    val tipe = rhs.tipe
    val s9: State = if (AST.Util.isSeq(tipe)) {
      val (s6, size1) = s5.freshSym(AST.Typed.z, pos)
      val (s7, size2) = s6.freshSym(AST.Typed.z, pos)
      val (s8, cond) = s7.freshSym(AST.Typed.b, pos)
      s8.addClaims(ISZ(
        State.Claim.Let.FieldLookup(size1, o1, "size"),
        State.Claim.Let.FieldLookup(size2, rhs, "size"),
        State.Claim.Let.Binary(cond, size2, AST.Exp.BinaryOp.Eq, size1, AST.Typed.z),
        State.Claim.Prop(T, cond)
      ))
    } else {
      s5
    }
    val objectName = ops.ISZOps(ids).dropRight(1)
    if (notInContext(objectName, T)) {
      return Util.checkInvs(this, namePosOpt, F, "Invariant after an object field assignment", smt2, cache, rtCheck, s9,
        None(), None(), if (context.isHelper) ISZ() else retrieveInvs(objectName, T), TypeChecker.emptySubstMap, reporter)
    } else {
      return s9
    }
  }

  def notInContext(name: ISZ[String], isInObject: B): B = {
    context.methodOpt match {
      case Some(cm) if cm.name.size > 1 =>
        if (isInObject) {
          if (context.receiverTypeOpt.nonEmpty) {
            return T
          }
        } else {
          if (context.receiverTypeOpt.isEmpty) {
            return T
          }
        }
        val mContext = ops.ISZOps(cm.name).dropRight(1)
        return mContext != name
      case _ => return name.nonEmpty
    }
  }

  def evalAssignThisVarH(s0: State, id: String, rhs: State.Value, pos: Position, reporter: Reporter): State = {
    val lcontext = context.methodOpt.get.name
    val receiverType = context.methodOpt.get.receiverTypeOpt.get
    val (s1, o) = idIntro(pos, s0, lcontext, "this", receiverType, None())
    val (s2, newSym) = s1.freshSym(receiverType, pos)
    val s3 = evalAssignLocalH(F, s2.addClaim(State.Claim.Let.FieldStore(newSym, o, id, rhs)), lcontext, "this",
      newSym, Some(pos), reporter)
    return s3
  }

  def assignRec(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, lhs: AST.Exp,
                rhs: State.Value.Sym, reporter: Reporter): ISZ[State] = {
    @pure def isSeqSelect(exp: AST.Exp.Invoke): B = {
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Select => return T
        case res: AST.ResolvedInfo.BuiltIn if res.kind == AST.ResolvedInfo.BuiltIn.Kind.Apply =>
          exp.receiverOpt match {
            case Some(receiver) => receiver.typedOpt.get match {
              case t: AST.Typed.Name if t.ids == AST.Typed.isName || t.ids == AST.Typed.msName => return T
              case _ =>
            }
            case _ =>
          }
        case _ =>
      }
      return F
    }
    lhs match {
      case lhs: AST.Exp.Ident =>
        lhs.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar =>
            context.methodOpt match {
              case Some(mctx) if !config.interp && !context.hasInline && res.context == mctx.name =>
                val isParam = mctx.paramIds.contains(res.id)
                if (isParam && !mctx.modLocalIds.contains(res.id) || !isParam && !context.modifiableIds.contains(res.id)) {
                  reporter.error(lhs.posOpt, kind, s"Missing Modifies clause for ${res.id}")
                }
              case _ =>
            }
            val (s1, sym) = idIntro(lhs.posOpt.get, s0, res.context, res.id, lhs.typedOpt.get, None())
            val s2 = s1.addClaim(State.Claim.Old(T, res.isSpec, res.context, res.id, sym, lhs.posOpt.get))
            return ISZ(evalAssignLocalH(F, s2, res.context, res.id, rhs, lhs.posOpt, reporter))
          case res: AST.ResolvedInfo.Var =>
            if (res.isInObject) {
              val (s1, sym) = nameIntro(lhs.posOpt.get, s0, res.owner :+ res.id, lhs.typedOpt.get, None())
              val s2 = s1.addClaim(State.Claim.Old(F, res.isSpec, res.owner, res.id, sym, lhs.posOpt.get))
              return ISZ(evalAssignObjectVarH(smt2, cache, rtCheck, s2, res.owner :+ res.id, lhs.typedOpt.get, rhs,
                lhs.posOpt, reporter))
            } else {
              val (s1, sym) = idIntro(lhs.posOpt.get, s0, context.methodName, "this", context.receiverTypeOpt.get, None())
              val s2 = s1.addClaim(State.Claim.Old(T, res.isSpec, context.methodName, "this", sym, lhs.posOpt.get))
              return ISZ(evalAssignThisVarH(s2, lhs.id.value, rhs, lhs.posOpt.get, reporter))
            }
          case _ => halt(s"Infeasible: $lhs")
        }
      case lhs: AST.Exp.Invoke =>
        if (!isSeqSelect(lhs)) {
          return ISZ(s0)
        }
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        var r = ISZ[State]()
        for (p1 <- evalExp(split, smt2, cache, T, s0, receiver, reporter);
             p2 <- evalExp(split, smt2, cache, T, p1._1, lhs.args(0), reporter)) {
          val (_, a) = p1
          val (s2, i) = p2
          val s3 = checkSeqIndexing(smt2, cache, T, s2, a, i, lhs.args(0).posOpt, reporter)
          if (s3.ok) {
            val (s4, newSym) = s3.freshSym(t, receiverPos)
            r = r ++ assignRec(split, smt2, cache, rtCheck, s4.addClaim(State.Claim.Let.SeqStore(newSym, a, i, rhs)),
              receiver, newSym, reporter)
          } else {
            r = r :+ s3
          }
        }
        return r
      case lhs: AST.Exp.Select =>
        lhs.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var =>
            if (res.isInObject) {
              val (s1, sym) = nameIntro(lhs.posOpt.get, s0, res.owner :+ res.id, lhs.typedOpt.get, None())
              val s2 = s1.addClaim(State.Claim.Old(F, res.isSpec, res.owner, res.id, sym, lhs.posOpt.get))
              return ISZ(evalAssignObjectVarH(smt2, cache, rtCheck, s2, res.owner :+ res.id, lhs.typedOpt.get, rhs,
                lhs.posOpt, reporter))
            } else {
              lhs.receiverOpt match {
                case Some(_: AST.Exp.This) =>
                  val (s1, sym) = idIntro(lhs.posOpt.get, s0, context.methodName, "this", context.receiverTypeOpt.get, None())
                  val s2 = s1.addClaim(State.Claim.Old(T, res.isSpec, context.methodName, "this", sym, lhs.posOpt.get))
                  return ISZ(evalAssignThisVarH(s2, lhs.id.value, rhs, lhs.posOpt.get, reporter))
                case _ =>
              }
            }
          case _ =>
        }
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        var r = ISZ[State]()
        for (p <- evalExp(split, smt2, cache, T, s0, receiver, reporter)) {
          val (s1, o) = p
          if (s1.ok) {
            val (s2, newSym) = s1.freshSym(t, receiverPos)
            val id = lhs.id.value
            val s3 = s2.addClaim(State.Claim.Let.FieldStore(newSym, o, id, rhs))
            if (notInContext(t.ids, F)) {
              val typeParams: ISZ[AST.TypeParam] = th.typeMap.get(t.ids).get match {
                case info: TypeInfo.Adt => info.ast.typeParams
                case info: TypeInfo.Sig => info.ast.typeParams
                case info => halt(s"Infeasible: $info")
              }
              val sm = TypeChecker.buildTypeSubstMap(t.ids, lhs.posOpt, typeParams, t.args, reporter).get
              val (s4, oSym) = value2Sym(s3, o, receiverPos)
              val s5 = Util.checkInvs(this, lhs.posOpt, F, "Invariant after an instance field assignment", smt2, cache,
                rtCheck, s4, Some(t), Some(oSym), if (context.isHelper) ISZ() else retrieveInvs(t.ids, T), sm, reporter)
              r = r ++ assignRec(split, smt2, cache, rtCheck, s5, receiver, newSym, reporter)
            } else {
              r = r ++ assignRec(split, smt2, cache, rtCheck, s3, receiver, newSym, reporter)
            }
          } else {
            r = r :+ s1
          }
        }
        return r
      case _ => halt(s"Infeasible: $lhs")
    }

  }

  def evalPattern(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, v: State.Value, pattern: AST.Pattern, reporter: Reporter): (State, State.Value, Bindings) = {
    val posOpt = pattern.posOpt
    val pos = posOpt.get
    pattern match {
      case pattern: AST.Pattern.Literal =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        return (s1.addClaim(State.Claim.Let.Binary(cond, v, AST.Exp.BinaryOp.Equiv,
          evalLit(smt2, pattern.lit, reporter), v.tipe)), cond, Map.empty)
      case pattern: AST.Pattern.LitInterpolate =>
        val lit = evalInterpolate(smt2, AST.Exp.StringInterpolate(pattern.prefix,
          ISZ(AST.Exp.LitString(pattern.value, AST.Attr(pattern.posOpt))), ISZ(), pattern.attr), reporter)
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        return (s1.addClaim(State.Claim.Let.Binary(cond, v, AST.Exp.BinaryOp.Equiv, lit, v.tipe)), cond, Map.empty)
      case pattern: AST.Pattern.VarBinding =>
        pattern.tipeOpt match {
          case Some(tipe) =>
            val t = tipe.typedOpt.get
            val tpos = tipe.posOpt.get
            val (s1, cond) = evalTypeTestH(s0, v, t, tpos)
            val (s2, sym) = value2Sym(s1, v, tpos)
            return (s2, cond, emptyBindings + pattern.id.value ~> ((sym, t, tpos)))
          case _ =>
            val t = pattern.attr.typedOpt.get
            val (s1, sym) = value2Sym(s0, v, pattern.id.attr.posOpt.get)
            return (s1, State.Value.B(T, pos),
              emptyBindings + pattern.id.value ~> ((sym, t, pos)))
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
        var m = emptyBindings
        var s1 = s0
        pattern.idOpt match {
          case Some(id) =>
            val idPos = id.attr.posOpt.get
            val (s3, sym) = value2Sym(s1, v, idPos)
            m = m + id.value ~> ((sym, pattern.attr.typedOpt.get, idPos))
            s1 = s3
          case _ =>
        }
        if (pattern.nameOpt.nonEmpty) {
          val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
          if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
            val it = t.args(0).asInstanceOf[AST.Typed.Name]
            val et = t.args(1)
            val hasWildcard = ops.ISZOps(pattern.patterns).exists(
              (p: AST.Pattern) => p.isInstanceOf[AST.Pattern.SeqWildcard])
            val (s3, sizeSym) = s1.freshSym(AST.Typed.z, pos)
            val s4 = s3.addClaim(State.Claim.Let.FieldLookup(sizeSym, v, "size"))
            val (s5, cond) = s4.freshSym(AST.Typed.b, pos)
            val (op, size): (String, Z) =
              if (hasWildcard) (">=", pattern.patterns.size - 1) else (AST.Exp.BinaryOp.Equiv, pattern.patterns.size)
            var s6 = s5.addClaim(State.Claim.Let.Binary(cond, sizeSym, op, State.Value.Z(size, pos), AST.Typed.z))
            var conds = ISZ[State.Value](cond)
            val offset: Z = if (it == AST.Typed.z) 0 else th.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ].ast.index
            for (i <- 0 until size) {
              val sub = pattern.patterns(i)
              val subPos = sub.posOpt.get
              val (s7, sym) = s6.freshSym(et, subPos)
              val (s8, cond, subM) = evalPattern(smt2, cache, rtCheck, s7.addClaim(
                State.Claim.Let.SeqLookup(sym, v, State.Value.Z(offset + i, subPos))), sym, sub, reporter)
              conds = conds :+ cond
              s6 = s8
              m = m ++ subM.entries
            }
            val (s9, aconds) = s6.freshSym(AST.Typed.b, pos)
            return (s9.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
          } else {
            val (s3, tcond) = evalTypeTestH(s1, v, t, pos)
            val ti = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
            val sm = TypeChecker.buildTypeSubstMap(t.ids, posOpt, ti.ast.typeParams, t.args, reporter).get
            val (s4, o) = s3.freshSym(t, pos)
            var s5 = s4.addClaim(State.Claim.Let.Def(o, v))
            var conds = ISZ[State.Value](tcond)
            for (p <- ops.ISZOps(ti.extractorTypeMap.entries).zip(pattern.patterns)) {
              val f = p._1._1
              val ft = p._1._2.subst(sm)
              val sub = p._2
              val (s6, sym) = s5.freshSym(ft, sub.posOpt.get)
              s5 = s6.addClaim(State.Claim.Let.FieldLookup(sym, o, f))
              val (s7, cond, subM) = evalPattern(smt2, cache, rtCheck, s5, sym, sub, reporter)
              s5 = s7
              conds = conds :+ cond
              m = m ++ subM.entries
            }
            val (s8, aconds) = s5.freshSym(AST.Typed.b, pos)
            return (s8.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
          }
        } else {
          val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Tuple]
          var s3 = s1
          var conds = ISZ[State.Value]()
          for (i <- 1 to pattern.patterns.size) {
            val sub = pattern.patterns(i - 1)
            val (s4, sym) = s3.freshSym(t.args(i - 1), sub.posOpt.get)
            val s5 = s4.addClaim(State.Claim.Let.FieldLookup(sym, v, s"_$i"))
            val (s6, cond, subM) = evalPattern(smt2, cache, rtCheck, s5, sym, sub, reporter)
            s3 = s6
            conds = conds :+ cond
            m = m ++ subM.entries
          }
          val (s7, aconds) = s3.freshSym(AST.Typed.b, pos)
          return (s7.addClaim(State.Claim.Let.And(aconds, conds)), aconds, m)
        }
      case pattern: AST.Pattern.Ref =>
        val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
        pattern.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var =>
            if (res.owner == AST.Typed.sireumName && res.id == "T" || res.id == "F") {
              return (s1.addClaim(State.Claim.Let.Binary(cond, v, AST.Exp.BinaryOp.Equiv,
                State.Value.B(res.id == "T", pos), AST.Typed.b)), cond, Map.empty)
            }
            val t = pattern.attr.typedOpt.get
            val (s2, sym): (State, State.Value) = if (res.isInObject) {
              val p = nameIntro(pos, s1, res.owner :+ res.id, t, None())
              (p._1, p._2)
            } else {
              evalThisIdH(smt2, cache, rtCheck, s1, res.id, t, pos, reporter)
            }
            return (s2.addClaim(State.Claim.Let.Binary(cond, v, AST.Exp.BinaryOp.Equiv, sym, t)), cond, Map.empty)
          case res: AST.ResolvedInfo.EnumElement =>
            val t = pattern.attr.typedOpt.get.asInstanceOf[AST.Typed.Name]
            return (s1.addClaim(State.Claim.Let.Binary(cond, v, AST.Exp.BinaryOp.Equiv,
              State.Value.Enum(t, res.owner, res.name, res.ordinal, pos), t)), cond, Map.empty)
          case _ => halt(s"Infeasible: $pattern")
        }
      case _: AST.Pattern.SeqWildcard => halt(s"Infeasible")
    }
  }

  def addBindings(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, lcontext: ISZ[String],
                  m: Bindings, reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    val ids = m.keys
    val s1 = rewriteLocals(s0, F, lcontext, ids)._1
    var s2 = s1
    var bindings = ISZ[State.Value.Sym]()
    for (p <- m.entries) {
      val (id, (v, t, pos)) = p
      val (s3, x) = idIntro(pos, s2, lcontext, id, t, Some(pos))
      val s4 = Util.assumeValueInv(this, smt2, cache, rtCheck, s3, x, pos, reporter)
      val (s5, sym) = s4.freshSym(AST.Typed.b, pos)
      s2 = s5.addClaim(State.Claim.Let.Binary(sym, x, AST.Exp.BinaryOp.Equiv, v, t))
      bindings = bindings :+ sym
    }
    return (s2, bindings)
  }

  def assumeBindings(s0: State, lcontext: ISZ[String], m: Bindings, bidMap: HashMap[String, (Z, ISZ[Position])]): State = {
    var s1 = s0
    for (p <- m.entries) {
      val (id, (v, t, pos)) = p
      val (num, poss) = bidMap.get(id).get
      val (s2, x) = idIntro(pos, s1, lcontext, id, t, Some(pos))
      val (s3, reX) = s2.freshSym(t, pos)
      s1 = s3.addClaims(ISZ(
        State.Claim.Let.Id(reX, F, lcontext, id, num, poss),
        State.Claim.Eq(reX, x),
        State.Claim.Eq(x, v)
      ))
    }
    return s1
  }

  def evalBranch(isMatch: B, split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State,
                 lcontext: ISZ[String], branches: ISZ[Branch], i: Z, rOpt: Option[State.Value.Sym],
                 reporter: Reporter): (Z, Option[(State.Claim, ISZ[(State.Status.Type, ISZ[State.Claim])])]) = {
    val shouldSplit: B = split match {
      case Split.Default => config.splitAll || (isMatch && config.splitMatch)
      case Split.Enabled => T
      case Split.Disabled => F
    }
    var nextFresh = s0.nextFresh
    val Branch(title, sym, body, m, bidMap) = branches(i)
    val cond = State.Claim.And(
      (for (j <- 0 until i) yield State.Claim.Prop(F, branches(j).sym).asInstanceOf[State.Claim]) :+
        State.Claim.Prop(T, sym))
    val pos = sym.pos
    val posOpt: Option[Position] = Some(pos)
    val s1 = s0.addClaim(cond)
    if (s1.ok) {
      if (smt2.sat(context.methodName, config, cache, T,
        s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims, reporter)) {
        val s2 = assumeBindings(s1, lcontext, m, bidMap)
        var claims = ISZ[(State.Status.Type, ISZ[State.Claim])]()
        for (s3 <- evalBody(split, smt2, cache, rOpt, rtCheck, s2, body, posOpt, reporter)) {
          val s4 = rewriteLocals(s3, F, lcontext, m.keys)._1
          if (nextFresh < s4.nextFresh) {
            nextFresh = s4.nextFresh
          }
          claims = claims :+ ((s4.status, s4.claims))
        }
        if (claims.nonEmpty) {
          return (nextFresh, Some((cond, claims)))
        }
      } else {
        if (isMatch && config.checkInfeasiblePatternMatch && !config.interp && !context.hasInline && !shouldSplit) {
          warn(posOpt, "Infeasible pattern matching case", reporter)
        }
      }
    }
    return (nextFresh, None())
  }

  def evalBranches(isMatch: B, split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B,
                   rOpt: Option[State.Value.Sym], lcontext: ISZ[String], s0: State, branches: ISZ[Branch],
                   reporter: Reporter): (State, LeafClaims) = {
    @pure def allReturns: B = {
      for (branch <- branches if !branch.body.allReturns) {
        return F
      }
      return T
    }
    var leafClaims: LeafClaims = ISZ()
    if (config.parCores > 1 && (config.branchPar == Config.BranchPar.All ||
      (allReturns && config.branchPar == Config.BranchPar.OnlyAllReturns))) {
      val inputs: ISZ[Z] = branches.indices

      def computeBranch(i: Z): (Option[(State.Claim, ISZ[(State.Status.Type, ISZ[State.Claim])])], Z, Smt2) = {
        val rep = reporter.empty
        val lsmt2 = smt2
        val (nextFresh, lcsOpt) = evalBranch(isMatch, split, lsmt2, cache, rtCheck, s0, lcontext, branches, i, rOpt, rep)
        reporter.combine(rep)
        return (lcsOpt, nextFresh, lsmt2)
      }

      if (!(branches.size == 2 && (branches(1).body.stmts.isEmpty || branches(0).body.stmts.isEmpty))) {
        var first: Z = -1
        val outputs = ops.MSZOps(inputs.toMS).mParMapCores(computeBranch _, config.parCores)
        for (i <- 0 until outputs.size) {
          smt2.combineWith(outputs(i)._3)
        }
        for (i <- 0 until outputs.size if first < 0) {
          if (outputs(i)._1.nonEmpty) {
            first = i
          }
        }
        if (first < 0) {
          return (s0(status = State.Status.Error), leafClaims)
        }
        leafClaims = leafClaims :+ outputs(first)._1.get
        var nextFreshGap = outputs(first)._2 - s0.nextFresh
        for (i <- first + 1 until outputs.size) {
          outputs(i)._1 match {
            case Some((cond, claimss)) =>
              val gap = outputs(i)._2 - s0.nextFresh
              assert(gap >= 0)
              if ((!allReturns || config.interp || context.hasInline) && gap > 0) {
                val rw = Util.SymAddRewriter(s0.nextFresh, nextFreshGap, jescmPlugins._4)
                val newCond = rw.transformStateClaim(cond).getOrElseEager(cond)
                var newClaimss = ISZ[(State.Status.Type, ISZ[State.Claim])]()
                for (statusClaims <- claimss) {
                  newClaimss = newClaimss :+ ((statusClaims._1, for (claim <- statusClaims._2) yield
                    rw.transformStateClaim(claim).getOrElseEager(claim)))
                }
                leafClaims = leafClaims :+ ((newCond, newClaimss))
                nextFreshGap = nextFreshGap + gap
              } else {
                leafClaims = leafClaims :+ ((cond, claimss))
              }
            case _ =>
          }
        }
        return (s0(nextFresh = s0.nextFresh + nextFreshGap), leafClaims)
      }
    }

    var s1 = s0
    for (i <- 0 until branches.size) {
      val (nextFresh, lcsOpt) = evalBranch(isMatch, split, smt2, cache, rtCheck, s1, lcontext, branches, i, rOpt, reporter)
      s1 = s1(nextFresh = nextFresh)
      if (lcsOpt.nonEmpty) {
        leafClaims = leafClaims :+ lcsOpt.get
      }
    }
    return (s1, leafClaims)

  }

  def mergeBranches(shouldSplit: B, s0: State, leafClaims: LeafClaims): ISZ[State] = {
    if (leafClaims.isEmpty) {
      return ISZ(s0(status = State.Status.Error))
    } else if (shouldSplit || leafClaims.size == 1) {
      return for (p <- leafClaims; cs <- p._2) yield s0(status = cs._1, claims = (ops.ISZOps(cs._2).slice(0, s0.claims.size) :+ p._1) ++
        ops.ISZOps(cs._2).slice(s0.claims.size + 1, cs._2.size))
    }
    var r = ISZ[State]()
    var scss = ISZ[ISZ[(State.Claim, ISZ[State.Claim])]]()
    for (leafClaim <- leafClaims) {
      var newScss = ISZ[ISZ[(State.Claim, ISZ[State.Claim])]]()
      val (cond, claimss) = leafClaim
      def processClaimss(scs: ISZ[(State.Claim, ISZ[State.Claim])]): Unit = {
        for (statusClaims <- claimss) {
          val (status, claims) = statusClaims
          if (status == State.Status.Normal) {
            newScss = newScss :+ (scs :+ ((cond, claims)))
          } else {
            r = r :+ s0(status = status, claims = (ops.ISZOps(claims).slice(0, s0.claims.size) :+ cond) ++
              ops.ISZOps(claims).slice(s0.claims.size + 1, claims.size))
          }
        }
      }
      if (scss.isEmpty) {
        processClaimss(ISZ())
      } else {
        for (scs <- scss) {
          processClaimss(scs)
        }
      }
      scss = newScss
    }
    if (scss.size == 1 && scss(0).size == 1) {
      var claims = ISZ[State.Claim]()
      val sc = scss(0)(0)
      claims = claims :+ sc._1
      for (i <- s0.claims.size + 1 until sc._2.size) {
        claims = claims :+ sc._2(i)
      }
      r = r :+ s0(claims = s0.claims ++ claims)
    } else {
      for (scs <- scss) {
        @pure def computeDiffIndices(): (ISZ[State.Claim], ISZ[Z]) = {
          var commonClaimPrefix = ISZ[State.Claim]()
          var diffIndices = ISZ[Z]()
          for (i <- 0 until s0.claims.size) {
            val c = scs(0)._2(i)
            var ok = T
            var j = 1
            while (ok && j < scs.size) {
              if (c != scs(j)._2(i)) {
                ok = F
              }
              j = j + 1
            }
            if (ok) {
              commonClaimPrefix = commonClaimPrefix :+ c
            } else {
              commonClaimPrefix = commonClaimPrefix :+ trueClaim
              diffIndices = diffIndices :+ i
            }
          }
          return (commonClaimPrefix, diffIndices)
        }

        val (commonClaimPrefix, diffIndices) = computeDiffIndices()
        var claims = ISZ[State.Claim]()
        for (sc <- scs) {
          for (i <- diffIndices) {
            claims = claims :+ State.Claim.Imply(T, ISZ(sc._1, sc._2(i)))
          }
          for (i <- s0.claims.size + 1 until sc._2.size) {
            claims = claims :+ State.Claim.Imply(T, ISZ(sc._1, sc._2(i)))
          }
        }
        r = r :+ s0(claims = commonClaimPrefix ++ claims)
      }
    }
    return r
  }

  def evalMatch(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
                stmt: AST.Stmt.Match, reporter: Reporter): ISZ[State] = {
    def evalCasePattern(s1: State, lcontext: ISZ[String], c: AST.Case, v: State.Value): (State, State.Value.Sym, Bindings, HashMap[String, (Z, ISZ[Position])]) = {
      val (s2, pcond, m) = evalPattern(smt2, cache, rtCheck, s1, v, c.pattern, reporter)
      val (s3, bindings) = addBindings(smt2, cache, rtCheck, s2, lcontext, m, reporter)
      var conds = ISZ(pcond)
      val s6: State = c.condOpt match {
        case Some(cond) =>
          val condPos = cond.posOpt.get
          val (s4, ccond) = singleStateValue(condPos, s3, evalExp(Split.Disabled, smt2, cache, rtCheck, s3, cond, reporter))
          if (bindings.nonEmpty) {
            val (s5, sym) = s4.freshSym(AST.Typed.b, condPos)
            conds = conds :+ sym
            s5.addClaim(State.Claim.Let.Imply(sym, (for (b <- bindings) yield b.asInstanceOf[State.Value]) :+ ccond))
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
      val (s9, locals) = rewriteLocals(s8, F, lcontext, m.keys)
      return (s9, sym, m, HashMap.empty[String, (Z, ISZ[Position])] ++ (for (p <- locals.entries) yield (p._1._2, (p._2._2, p._2._1))))
    }
    def evalInductMatch(): ISZ[State] = {
      @pure def unifyPattern(p1: AST.Pattern, p2: AST.Pattern): Option[HashMap[AST.Exp, AST.Exp]] = {
        @strictpure def ident(vb: AST.Pattern.VarBinding): AST.Exp =
          AST.Exp.Ident(vb.id, AST.ResolvedAttr(vb.attr.posOpt, Some(AST.ResolvedInfo.LocalVar(vb.idContext, AST.ResolvedInfo.LocalVar.Scope.Current, F, T, vb.id.value)), vb.attr.typedOpt))
        (p1, p2) match {
          case (p1: AST.Pattern.Ref, p2: AST.Pattern.Ref) if p1.attr.resOpt == p2.attr.resOpt => return Some(HashMap.empty)
          case (p1: AST.Pattern.VarBinding, p2: AST.Pattern.VarBinding) if p1.idContext == p2.idContext =>
            return Some(HashMap.empty[AST.Exp, AST.Exp] + ident(p2) ~> ident(p1))
          case (p1: AST.Pattern.Structure, p2: AST.Pattern.Structure) if p1.attr.typedOpt == p2.attr.typedOpt =>
            var m = HashMap.empty[AST.Exp, AST.Exp]
            for (i <- 0 until p1.patterns.size) {
              unifyPattern(p1.patterns(i), p2.patterns(i)) match {
                case Some(m2) => m = m ++ m2.entries
                case _ => return None()
              }
            }
            return Some(m)
          case _ => return None()
        }
      }
      val posOpt = stmt.exp.posOpt
      val cm = context.methodOpt.get
      val claim: AST.Exp =
        if (cm.requires.isEmpty) AST.Util.bigAnd(cm.ensures, posOpt)
        else AST.Util.bigImply(T, cm.requires :+ AST.Util.bigAnd(cm.ensures, posOpt), posOpt)
      var (s1, v) = evalExp(Split.Disabled, smt2, cache, rtCheck, state, stmt.exp, reporter)(0)
      var branches = ISZ[Branch]()
      th.induct(T, HashSet.empty, context.methodName, claim, stmt.exp, posOpt.get) match {
        case Some(ir) =>
          val lcontext = context.methodName
          var cases = ir.cases
          for (cas <- stmt.cases) {
            var found = F
            for (icas <- ir.cases if !found) {
              unifyPattern(cas.pattern, icas.pattern) match {
                case Some(sm) =>
                  found = T
                  cases = cases - icas
                  val premises: ISZ[AST.Exp] = if (sm.isEmpty) {
                    icas.premises
                  } else {
                    val es = AST.Util.ExpSubstitutor(sm)
                    for (p <- icas.premises) yield es.transformExp(p).getOrElse(p)
                  }
                  val (s2, sym, m, bidMap) = evalCasePattern(s1, lcontext, cas, v)
                  s1 = s2
                  val assumeAttr = AST.ResolvedAttr(posOpt, TypeChecker.assumeResOpt, TypeChecker.assertumeTypedOpt)
                  val assumeIdent = AST.Exp.Ident(AST.Id("assume", AST.Attr(posOpt)), assumeAttr)
                  val exprAttr = AST.TypedAttr(posOpt, AST.Typed.unitOpt)
                  val assumes: ISZ[AST.Stmt] = for (p <- premises) yield AST.Stmt.Expr(
                    AST.Exp.Invoke(None(), assumeIdent, ISZ(), ISZ(p), assumeAttr), exprAttr)
                  branches = branches :+ Branch("match case pattern", sym,
                    cas.body(stmts = assumes ++ cas.body.stmts), m, bidMap)
                case _ =>
              }
            }
            if (!found) {
              reporter.error(cas.pattern.posOpt, kind, s"Could not match the induction pattern")
            }
          }
          val (s3, leafClaims) = evalBranches(T, split, smt2, cache, rtCheck, rOpt, lcontext, s1, branches, reporter)
          val shouldSplit: B = split match {
            case Split.Default => config.splitAll || config.splitMatch
            case Split.Enabled => T
            case Split.Disabled => F
          }
          return mergeBranches(shouldSplit, s3, leafClaims)
        case _ =>
          reporter.error(posOpt, kind, st"Could not induct on ${stmt.exp.prettyST}".render)
          return ISZ(state(status = State.Status.Error))
      }
    }

    if (stmt.isInduct) {
      return evalInductMatch()
    }

    var r = ISZ[State]()
    val lcontext: ISZ[String] = context.methodOpt match {
      case Some(mctx) => mctx.name
      case _ => ISZ()
    }

    for (p <- evalExp(split, smt2, cache, rtCheck, state, stmt.exp, reporter)) {
      val (s0, v) = p
      if (s0.ok) {
        var branches = ISZ[Branch]()
        var s1 = s0
        for (c <- stmt.cases) {
          val (s2, sym, m, bidMap) = evalCasePattern(s1, lcontext, c, v)
          s1 = s2
          branches = branches :+ Branch("match case pattern", sym, c.body, m, bidMap)
        }
        val stmtPos = stmt.posOpt.get
        if (!config.interp && !context.hasInline && config.patternExhaustive &&
          smt2.satResult(context.methodName, config, cache, config.timeoutInMs, T,
            s"pattern match inexhaustiveness at [${stmtPos.beginLine}, ${stmtPos.beginColumn}]",
            stmtPos, s1.claims :+ State.Claim.And(for (p <- branches) yield State.Claim.Prop(F, p.sym)), reporter).
            _2.kind == Smt2Query.Result.Kind.Sat) {
          error(stmt.exp.posOpt, "Inexhaustive pattern match", reporter)
          r = r :+ s1(status = State.Status.Error)
        } else {
          val (s3, leafClaims) = evalBranches(T, split, smt2, cache, rtCheck, rOpt, lcontext, s1, branches, reporter)
          val shouldSplit: B = split match {
            case Split.Default => config.splitAll || config.splitMatch
            case Split.Enabled => T
            case Split.Disabled => F
          }
          r = r ++ mergeBranches(shouldSplit, s3, leafClaims)
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

  def evalBlock(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State,
                block: AST.Stmt.Block,
                reporter: Reporter): ISZ[State] = {
    return evalBody(split, smt2, cache, rOpt, rtCheck, s0, block.body, block.attr.posOpt, reporter)
  }

  def evalIf(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
             stmt: AST.Stmt.If, reporter: Reporter): ISZ[State] = {
    var branches = ISZ[Branch]()
    def evalConds(s0: State, ifStmt: AST.Stmt.If): State = {
      val pos = ifStmt.cond.posOpt.get
      val (s1, cond) = singleStateValue(pos, s0, evalExp(Split.Disabled, smt2, cache, rtCheck, s0, ifStmt.cond, reporter))
      val (s2, sym) = value2Sym(s1, cond, pos)
      branches = branches :+ Branch("if-then", sym, ifStmt.thenBody, Map.empty, HashMap.empty)
      ifStmt.elseBody.stmts match {
        case ISZ(nif: AST.Stmt.If) => return evalConds(s2, nif)
        case _ =>
          val (s3, econd) = s2.freshSym(AST.Typed.b, pos)
          branches = branches :+ Branch("if-else", econd, ifStmt.elseBody, Map.empty, HashMap.empty)
          return s3.addClaim(State.Claim.Let.Def(econd, State.Value.B(T, pos)))
      }
    }
    val s4 = evalConds(state, stmt)
    val (s5, leafClaims) = evalBranches(F, split, smt2, cache, rtCheck, rOpt, ISZ(), s4, branches, reporter)
    val shouldSplit: B = split match {
      case Split.Default => config.splitAll || config.splitIf
      case Split.Enabled => T
      case Split.Disabled => F
    }
    return mergeBranches(shouldSplit, s5, leafClaims)
  }

  def evalExprInvoke(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, stmt: AST.Stmt,
                     e: AST.Exp.Invoke, reporter: Reporter): ISZ[(State, State.Value)] = {
    def printH(): ISZ[(State, State.Value)] = {
      val pos = e.posOpt.get
      var ss = ISZ[State](state)
      var nextFresh: Z = -1
      for (arg <- e.args) {
        var newSS = ISZ[State]()
        for (s <- ss) {
          if (s.ok) {
            val svs = evalExp(split, smt2, cache, rtCheck, s, arg, reporter)
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
            val (s0, v) = evalAssert(smt2, cache, T, "Assertion", state, exp, exp.posOpt, ISZ(), reporter)
            return ISZ((s0, v))
          case AST.ResolvedInfo.BuiltIn.Kind.AssertMsg =>
            val exp = e.args(0)
            val (s0, v) = evalAssert(smt2, cache, T, "Assertion", state, exp, exp.posOpt, ISZ(), reporter)
            return ISZ((s0, v))
          case AST.ResolvedInfo.BuiltIn.Kind.Assume =>
            val exp = e.args(0)
            val (s0, v) = evalAssume(smt2, cache, T, "Assumption", state, exp, exp.posOpt, reporter)
            return ISZ((s0, v))
          case AST.ResolvedInfo.BuiltIn.Kind.AssumeMsg =>
            val exp = e.args(0)
            val (s0, v) = evalAssume(smt2, cache, T, "Assumption", state, exp, exp.posOpt, reporter)
            return ISZ((s0, v))
          case AST.ResolvedInfo.BuiltIn.Kind.Print => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Println => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Cprint => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Cprintln => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Eprint => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Eprintln => return printH()
          case AST.ResolvedInfo.BuiltIn.Kind.Halt =>
            val s0 = state(status = State.Status.Error)
            return ISZ((s0, State.errorValue))
          case _ =>
            reporter.warn(e.posOpt, Logika.kind, s"Not currently supported: $stmt")
            return ISZ((state(status = State.Status.Error), State.errorValue))
        }
      case _ =>
        return evalExp(split, smt2, cache, rtCheck, state, e, reporter)
    }
  }

  def evalProofStep(smt2: Smt2,
                    cache: Logika.Cache,
                    stateMap: (State, HashSMap[AST.ProofAst.StepId, StepProofContext]),
                    step: AST.ProofAst.Step,
                    reporter: Reporter): (State, HashSMap[AST.ProofAst.StepId, StepProofContext]) = {
    @pure def extractClaims(steps: ISZ[AST.ProofAst.Step]): ISZ[AST.Exp] = {
      var r = ISZ[AST.Exp]()
      for (stp <- steps) {
        stp match {
          case stp: AST.ProofAst.Step.Regular => r = r :+ th.normalizeExp(stp.claim)
          case stp: AST.ProofAst.Step.Assert => r = r :+ th.normalizeExp(stp.claim)
          case stp: AST.ProofAst.Step.Assume => r = r :+ th.normalizeExp(stp.claim)
          case _ =>
        }
      }
      return r
    }
    val stepNo = step.id
    var (s0, m) = stateMap
    step match {
      case step: AST.ProofAst.Step.Regular =>
        val pos = step.claim.posOpt.get
        if (config.transitionCache) {
          cache.getTransitionAndUpdateSmt2(th, config, Cache.Transition.ProofStep(step, m.values), context.methodName, s0, smt2) match {
            case Some((ISZ(nextState), cached)) =>
              reporter.coverage(F, cached, pos)
              return (nextState, m + stepNo ~> StepProofContext.Regular(th, stepNo, step.claim))
            case _ =>
          }
        }
        val normStep: AST.ProofAst.Step.Regular = step.just match {
          case j: AST.ProofAst.Step.Justification.Apply =>
            j.invokeIdent.attr.resOpt.get match {
              case res: AST.ResolvedInfo.Method =>
                val name = res.owner :+ res.id
                th.nameMap.get(name).get match {
                  case info: Info.JustMethod if info.ast.etaOpt.nonEmpty =>
                    val sm = TypeChecker.buildTypeSubstMap(name, j.posOpt, info.ast.sig.typeParams,
                      for (t <- j.invoke.targs) yield t.typedOpt.get, reporter).get
                    val id = info.ast.etaOpt.get.value
                    th.nameMap.get(res.owner :+ id) match {
                      case Some(minfo: Info.Method) =>
                        val t = minfo.ast.sig.funType.subst(sm)
                        val minfoAttr = AST.ResolvedAttr(
                          j.invokeIdent.posOpt,
                          Some(AST.ResolvedInfo.Method(T, AST.MethodMode.Method,
                            for (tp <- minfo.ast.sig.typeParams) yield tp.id.value, res.owner, id,
                            for (p <- minfo.ast.sig.params) yield p.id.value, Some(t), ISZ(), ISZ())), Some(t))
                        var witnesses = ISZ[AST.ProofAst.StepId]()
                        for (arg <- j.invoke.args) {
                          arg match {
                            case arg: AST.Exp.LitZ => witnesses = witnesses :+ AST.ProofAst.StepId.Num(arg.value, arg.attr)
                            case arg: AST.Exp.LitString => witnesses = witnesses :+ AST.ProofAst.StepId.Str(F, arg.value, arg.attr)
                            case arg: AST.ProofAst.StepId => witnesses = witnesses :+ arg
                            case _ =>
                              reporter.error(arg.posOpt, Logika.kind, "Invalid witness reference (has to be either a number or a string)")
                          }
                        }
                        step(just = AST.ProofAst.Step.Justification.ApplyEta(
                          AST.Exp.Eta(AST.Exp.Ident(AST.Id(id, AST.Attr(j.invokeIdent.posOpt)), minfoAttr),
                            AST.TypedAttr(j.invokeIdent.posOpt, Some(t))), j.invoke.args.nonEmpty, witnesses))
                      case _ =>
                        reporter.error(step.just.posOpt, Logika.kind, st"Could not find ${(res.owner :+ id, ".")}".render)
                        return (s0(status = State.Status.Error), m)
                    }
                  case _ => step
                }
              case _ => step
            }
          case _ => step
        }
        for (plugin <- jescmPlugins._1 if plugin.canHandle(this, normStep.just)) {
          if (!plugin.checkMode(this, normStep.just, reporter)) {
            return (s0(status = State.Status.Error), m)
          }
          val nextState = plugin.handle(this, smt2, cache, m, s0, normStep, reporter)
          if (config.transitionCache && nextState.ok && !reporter.hasError) {
            val cached = cache.setTransition(th, config, Cache.Transition.ProofStep(step, m.values), context.methodName, s0, ISZ(nextState), smt2)
            reporter.coverage(T, cached, pos)
          } else {
            reporter.coverage(F, zeroU64, pos)
          }
          return (nextState, m + stepNo ~> StepProofContext.Regular(th, stepNo, step.claim))
        }
        reporter.error(step.just.posOpt, Logika.kind, "Could not recognize justification form")
        return (s0(status = State.Status.Error), m)
      case step: AST.ProofAst.Step.Assume =>
        val s1 = evalRegularStepClaim(smt2, cache, s0, step.claim, step.id.posOpt, reporter)
        return (s1, m + stepNo ~> StepProofContext.Regular(th, stepNo, step.claim))
      case step: AST.ProofAst.Step.SubProof =>
        for (sub <- step.steps if s0.ok) {
          val p = evalProofStep(smt2, cache, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
        }
        s0 = stateMap._1(status = s0.status, nextFresh = s0.nextFresh)
        if (s0.ok) {
          m = stateMap._2 + stepNo ~> StepProofContext.SubProof(stepNo,
            th.normalizeExp(step.steps(0).asInstanceOf[AST.ProofAst.Step.Assume].claim), extractClaims(step.steps))
          return (s0, m)
        } else {
          return (s0, stateMap._2)
        }
      case step: AST.ProofAst.Step.Assert =>
        var provenClaims = HashSet.empty[AST.Exp]
        for (sub <- step.steps if s0.ok) {
          val p = evalProofStep(smt2, cache, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
          sub match {
            case sub: AST.ProofAst.Step.Regular if s0.ok => provenClaims = provenClaims +
              th.normalizeExp(sub.claim)
            case _ =>
          }
        }
        s0 = stateMap._1(nextFresh = s0.nextFresh)
        if (!s0.ok) {
          return (s0(status = State.Status.Error), stateMap._2)
        }
        if (!provenClaims.contains(th.normalizeExp(step.claim))) {
          reporter.error(step.claim.posOpt, Logika.kind, "The claim is not proven in the assertion's sub-proof")
          return (s0(status = State.Status.Error), stateMap._2)
        }
        val s1 = evalRegularStepClaimRtCheck(smt2, cache, F, s0, step.claim, step.id.posOpt, reporter)
        return (s1, m + stepNo ~> StepProofContext.Regular(th, stepNo, step.claim))
      case step: AST.ProofAst.Step.Let =>
        for (sub <- step.steps if s0.ok) {
          val p = evalProofStep(smt2, cache, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
        }
        s0 = stateMap._1(status = s0.status, nextFresh = s0.nextFresh)
        if (s0.ok) {
          if (step.steps.nonEmpty && step.steps(0).isInstanceOf[AST.ProofAst.Step.Assume]) {
            return (s0,
              stateMap._2 + stepNo ~> StepProofContext.FreshAssumeSubProof(stepNo, step.params,
                th.normalizeExp(step.steps(0).asInstanceOf[AST.ProofAst.Step.Assume].claim),
                extractClaims(step.steps)))
          } else {
            return (s0,
              stateMap._2 + stepNo ~> StepProofContext.FreshSubProof(stepNo, step.params, extractClaims(step.steps)))
          }
        } else {
          return (s0, stateMap._2)
        }
    }
  }

  def evalRegularStepClaim(smt2: Smt2, cache: Logika.Cache, s0: State, claim: AST.Exp, posOpt: Option[Position],
                           reporter: Reporter): State = {
    return evalRegularStepClaimRtCheck(smt2, cache, T, s0, claim, posOpt, reporter)
  }

  def evalRegularStepClaimValue(smt2: Smt2, cache: Logika.Cache, s0: State, claim: AST.Exp, posOpt: Option[Position],
                                reporter: Reporter): (State, State.Value.Sym) = {
    return evalRegularStepClaimRtCheckValue(smt2, cache, T, s0, claim, posOpt, reporter)
  }
  def evalRegularStepClaimRtCheck(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, claim: AST.Exp,
                                  posOpt: Option[Position], reporter: Reporter): State = {
    val (s1, v) = evalRegularStepClaimRtCheckValue(smt2, cache, rtCheck, s0, claim, posOpt, reporter)
    return if (s1.ok) s1.addClaim(State.Claim.Prop(T, v)) else s1
  }
  def evalRegularStepClaimRtCheckValue(smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, claim: AST.Exp,
                                       posOpt: Option[Position], reporter: Reporter): (State, State.Value.Sym) = {
    val svs = evalExp(Logika.Split.Disabled, smt2, cache, rtCheck, s0, claim, reporter)
    for (sv <- svs) {
      val (s1, v) = sv
      val (s2, sym) = value2Sym(s1, v, posOpt.get)
      return (s2, sym)
    }
    return (s0(status = State.Status.Error), State.errorValue)
  }

  @pure def claimsAnd(claims: ISZ[AST.Exp]): Option[AST.Exp] = {
    if (claims.isEmpty) {
      return None()
    }
    var claim = claims(claims.size - 1)
    val typedOpt: Option[AST.Typed] = Some(AST.Typed.b)
    val resOpt: Option[AST.ResolvedInfo] = Some(AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd))
    for (i <- claims.size - 2 to 0 by -1) {
      val exp = claims(i)
      val attr = AST.ResolvedAttr(exp.posOpt, resOpt, typedOpt)
      claim = AST.Exp.Binary(exp, AST.Exp.BinaryOp.CondAnd, claim, attr, attr.posOpt)
    }
    return Some(claim)
  }

  @memoize def invs2exp(invs: ISZ[Info.Inv], substMap: HashMap[String, AST.Typed]): Option[AST.Exp] = {
    if (substMap.nonEmpty) {
      val ts = AST.Transformer(ExpTypedSubst(substMap))
      val claims: ISZ[AST.Exp] = for (inv <- invs; claim <- inv.ast.claims) yield ts.transformExp(F, claim).resultOpt.getOrElse(claim)
      return claimsAnd(claims)
    } else {
      val claims: ISZ[AST.Exp] = for (inv <- invs; claim <- inv.ast.claims) yield claim
      return claimsAnd(claims)
    }
  }

  def evalInv(posOpt: Option[Position], isAssume: B, title: String, smt2: Smt2, cache: Logika.Cache, rtCheck: B,
              s0: State, invStmt: AST.Stmt.Inv, substMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
    var s1 = s0
    var i = 0
    val isSingle = invStmt.claims.size == 1
    val id = invStmt.id.value
    for (c <- invStmt.claims if s1.ok) {
      val claim = AST.Util.substExp(c, substMap)
      val (titl, pOpt): (String, Option[Position]) = if (posOpt.isEmpty) {
        (if (isSingle) s"$title $id" else s"$title $id#$i", claim.posOpt)
      } else {
        val cpos = claim.posOpt.get
        (if (isSingle) s"$title $id at [${cpos.beginLine}, ${cpos.beginColumn}]"
        else s"$title $id#$i at [${cpos.beginLine}, ${cpos.beginColumn}]", posOpt)
      }
      s1 =
        if (isAssume) evalAssume(smt2, cache, rtCheck, titl, s1, claim, pOpt, reporter)._1
        else evalAssert(smt2, cache, rtCheck, titl, s1, claim, pOpt, ISZ(), reporter)._1
      i = i + 1
    }
    return s1
  }

  def evalStmt(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, state: State, stmt: AST.Stmt,
               reporter: Reporter): (Logika, ISZ[State]) = {
    if (!state.ok) {
      return (this, ISZ(state))
    }
    val sPlugins = jescmPlugins._3
    if (sPlugins.nonEmpty) {
      for (p <- sPlugins if p.canHandle(this, stmt)) {
        return (this, p.handle(this, split, smt2, cache, rtCheck, state, stmt, reporter))
      }
    }

    def evalAssignLocal(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: AST.AssignExp, lhsType: AST.Typed,
                        idPosOpt: Option[Position]): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, cache, lhsType, rtCheck, s0, rhs, reporter)) {
        val (s1, init) = p
        if (s1.ok) {
          val (s2, sym) = value2Sym(s1, init, rhs.asStmt.posOpt.get)
          r = r :+ evalAssignLocalH(decl, s2, lcontext, id, sym, idPosOpt, reporter)
        } else {
          r = r :+ s1
        }
      }
      val nextFresh = Util.maxStatesNextFresh(r)
      return for (s <- r) yield s(nextFresh = nextFresh)
    }

    def evalAssign(s0: State, assignStmt: AST.Stmt.Assign): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, cache, assignStmt.lhs.typedOpt.get, rtCheck, s0, assignStmt.rhs, reporter)) {
        val (s1, init) = p
        if (s1.ok) {
          val (s2, sym) = value2Sym(s1, init, assignStmt.rhs.asStmt.posOpt.get)
          r = r ++ assignRec(split, smt2, cache, rtCheck, s2, assignStmt.lhs, sym, reporter)
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
        for (p1 <- evalExp(split, smt2, cache, rtCheck, s1, step.start, reporter);
             p2 <- evalExp(split, smt2, cache, rtCheck, p1._1, step.end, reporter)) {
          val (_, start) = p1
          val (s3, end) = p2
          val s4vs: ISZ[(State, Option[State.Value])] = step.byOpt match {
            case Some(e) => for (p3 <- evalExp(split, smt2, cache, rtCheck, s3, e, reporter)) yield (p3._1, Some(p3._2))
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
                  done = done :+ d.addClaim(State.Claim.Let.Id(idSym, F, ctx, id.value, num, ISZ(pos)))
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

      reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
      return ISZ(s0(status = State.Status.Error))
    }

    def evalWhile(s0: State, whileStmt: AST.Stmt.While): ISZ[State] = {
      var r = ISZ[State]()
      for (s0w <- checkExps(split, smt2, cache, F, "Loop invariant", " at the beginning of while-loop", s0,
        whileStmt.invariants, reporter)) {
        if (s0w.ok) {
          val s1: State = {
            val modObjectVars = whileStmt.contract.modifiedObjectVars
            var srw = rewriteObjectVars(this, smt2, cache, rtCheck, s0(nextFresh = s0w.nextFresh),
              whileStmt.contract.modifiedObjectVars, whileStmt.posOpt.get, reporter)
            for (p <- modObjectVars.entries) {
              val (res, (tipe, pos)) = p
              val (srw1, sym) = srw.freshSym(tipe, pos)
              val srw2 = assumeValueInv(this, smt2, cache, rtCheck, srw1, sym, pos, reporter)
              srw = srw2.addClaim(State.Claim.Let.CurrentName(sym, res.owner :+ res.id, Some(pos)))
            }
            val (receiverModified, modLocalVars) = whileStmt.contract.modifiedLocalVars(context.receiverLocalTypeOpt, HashMap.empty)
            val receiverOpt: Option[State.Value.Sym] = if (receiverModified) {
              val (srw3, sym) = idIntro(whileStmt.posOpt.get, srw, context.methodName, "this",
                context.receiverLocalTypeOpt.get._2, None())
              srw = srw3
              Some(sym)
            } else {
              None()
            }
            srw = rewriteLocalVars(this, srw, T, modLocalVars.keys, whileStmt.posOpt, reporter)
            for (p <- modLocalVars.entries) {
              val (res, (tipe, pos)) = p
              val (srw4, sym) = idIntro(pos, srw, res.context, res.id, tipe, Some(pos))
              srw = assumeValueInv(this, smt2, cache, rtCheck, srw4, sym, pos, reporter)
            }
            if (receiverModified) {
              val srw6 = evalAssignReceiver(whileStmt.contract.modifies, this, this, smt2, cache, rtCheck, srw,
                Some(AST.Exp.This(context.methodName, AST.TypedAttr(whileStmt.posOpt, Some(receiverOpt.get.tipe)))), receiverOpt,
                HashMap.empty, reporter)
              val (srw7, sym) = idIntro(whileStmt.posOpt.get, srw6, context.methodName, "this",
                context.receiverLocalTypeOpt.get._2, None())
              srw = assumeValueInv(this, smt2, cache, rtCheck, srw7, sym, sym.pos, reporter)
            }
            srw
          }
          for (p <- evalExp(split, smt2, cache, rtCheck, s1, whileStmt.cond, reporter)) {
            val (s2, v) = p
            if (s2.ok) {
              val pos = whileStmt.cond.posOpt.get
              val (s3, cond) = value2Sym(s2, v, pos)
              val prop = State.Claim.Prop(T, cond)
              val thenClaims = s3.claims :+ prop
              val thenSat = smt2.sat(context.methodName, config, cache, T,
                s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, thenClaims, reporter)
              var thisL = this
              var modifiableIds = HashSet.empty[String]
              for (m <- whileStmt.modifies) {
                m.resOpt match {
                  case Some(res: AST.ResolvedInfo.LocalVar) => modifiableIds = modifiableIds + res.id
                  case _ =>
                }
              }
              thisL = thisL(context = context(modifiableIds = modifiableIds))
              if (thenSat) {
                for (s4 <- assumeExps(split, smt2, cache, rtCheck, s3(claims = thenClaims), whileStmt.invariants, reporter);
                     s5 <- evalStmts(thisL, split, smt2, cache, None(), rtCheck, s4, whileStmt.body.stmts, reporter)) {
                  if (s5.ok) {
                    checkExps(split, smt2, cache, F, "Loop invariant", " at the end of while-loop", s5,
                      whileStmt.invariants, reporter)
                  }
                }
              }
              val negProp = State.Claim.Prop(F, cond)
              val elseClaims = s3.claims :+ negProp
              val elseSat = smt2.sat(context.methodName, config, cache, T,
                s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, elseClaims, reporter)
              val s4 = s3(status = State.statusOf(elseSat), claims = elseClaims)
              if (elseSat) {
                r = r ++ assumeExps(split, smt2, cache, rtCheck, s4, whileStmt.invariants, reporter)
              } else {
                r = r :+ s4
              }
            }
          }
        } else {
          r = r :+ s0w
        }
      }
      return r
    }

    def evalWhileUnroll(sp: Split.Type, s0: State, whileStmt: AST.Stmt.While): ISZ[State] = {
      def whileRec(current: State, numLoops: Z): ISZ[State] = {
        if (!current.ok) {
          return ISZ(current)
        }
        if (config.loopBound > 0 && numLoops > config.loopBound) {
          warn(whileStmt.cond.posOpt, s"Under-approximation due to loop unrolling capped with bound ${config.loopBound}",
            reporter)
          return ISZ(current(status = State.Status.Error))
        }
        var r = checkExps(sp, smt2, cache, F, "Loop invariant", "", current, whileStmt.invariants, reporter)
        for (s1 <- r if !s1.ok) {
          return for (s2 <- r) yield s2(status = State.Status.Error)
        }
        r = ISZ[State]()
        for (p <- evalExp(sp, smt2, cache, rtCheck, current, whileStmt.cond, reporter)) {
          val (s2, v) = p
          if (s2.ok) {
            val pos = whileStmt.cond.posOpt.get
            val (s2w, cond) = value2Sym(s2, v, pos)
            val s3 = s2w
            val prop = State.Claim.Prop(T, cond)
            val s4 = s3.addClaim(prop)
            val thenSat = smt2.sat(context.methodName, config, cache, T,
              s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, s4.claims, reporter)
            if (thenSat) {
              for (s5 <- evalStmts(this, sp, smt2, cache, None(), rtCheck, s4, whileStmt.body.stmts, reporter)) {
                if (s5.ok) {
                  val s6 = rewriteLocalVars(this, s5, F, whileStmt.body.undecls, whileStmt.posOpt, reporter)
                  r = r ++ whileRec(s6, numLoops + 1)
                } else {
                  r = r :+ s5
                }
              }
            }
            val negProp = State.Claim.Prop(F, cond)
            val s7 = s3.addClaim(negProp)
            val elseSat = smt2.sat(context.methodName, config, cache, T,
              s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, s7.claims, reporter)
            r = r :+ s7(status = State.statusOf(elseSat))
          } else {
            r = r :+ s2
          }
        }
        val nextFresh = maxStatesNextFresh(r)
        return for (s8 <- r) yield s8(nextFresh = nextFresh)
      }

      return whileRec(s0, 0)
    }

    def evalReturn(s0: State, returnStmt: AST.Stmt.Return): ISZ[State] = {
      def evalReturnH(): ISZ[State] = {
        returnStmt.expOpt match {
          case Some(exp) =>
            var r = ISZ[State]()
            for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp, reporter)) {
              val (s1, v) = p
              val pos = exp.posOpt.get
              val (s2, sym) = value2Sym(s1, v, pos)
              val (s3, res) = idIntro(pos, s2, context.methodName, "Res", sym.tipe, Some(pos))
              r = r :+ s3.addClaim(State.Claim.Eq(res, sym))
            }
            return r
          case _ => return ISZ(state)
        }
      }
      val ss: ISZ[State] = if (config.interp || context.hasInline) {
        evalReturnH()
      } else {
        val mcontext = context.methodOpt.get
        val invs: ISZ[Info.Inv] = if (context.isHelper) ISZ() else retrieveInvs(mcontext.owner, mcontext.isInObject)
        Util.checkMethodPost(this, smt2, cache, reporter, evalReturnH(), mcontext.posOpt, invs,
          mcontext.ensures, config.logPc, config.logRawPc, returnStmt.posOpt)
      }
      val r: ISZ[State] = for (s <- ss) yield s(status = if (s.ok) State.Status.End else s.status)
      return r
    }

    def evalSpecBlock(sp: Split.Type, s0: State, block: AST.Stmt.SpecBlock): ISZ[State] = {
      return evalBlock(sp, smt2, cache, None(), rtCheck, s0, block.block, reporter)
    }

    def evalDeduceSteps(s0: State, deduceStmt: AST.Stmt.DeduceSteps): ISZ[State] = {
      var p = (s0, HashSMap.empty[AST.ProofAst.StepId, StepProofContext])
      var stepIds = ISZ[AST.ProofAst.StepId]()
      val lpcs = this
      val l = lpcs(context = lpcs.context(pathConditionsOpt = Some(
        Logika.PathConditions(th, Util.claimsToExps(jescmPlugins._4, deduceStmt.posOpt.get, context.methodName,
          s0.claims, th, config.atLinesFresh, config.atRewrite)._1))))
      for (step <- deduceStmt.steps if p._1.ok) {
        p = l.evalProofStep(smt2, cache, p, step, reporter)
        step match {
          case step: AST.ProofAst.Step.Regular if p._1.ok => stepIds = stepIds :+ step.id
          case _ =>
        }
      }
      val m = p._2
      var s1 = s0
      //var s1 = s0(nextFresh = p._1.nextFresh, claims = ops.ISZOps(p._1.claims).slice(0, s0.claims.size))
      if (p._1.ok) {
        for (stepId <- stepIds) {
          val spc = m.get(stepId).get.asInstanceOf[StepProofContext.Regular]
          s1 = evalAssume(smt2, cache, F, s"${spc.stepNo}", s1, spc.exp, spc.stepNo.posOpt, reporter)._1
//          s1 = s1.addClaims(spc.claims)
        }
      }
      return ISZ(s1)
    }

    def evalDeduceSequent(s0: State, deduceStmt: AST.Stmt.DeduceSequent): ISZ[State] = {
      val thisL = this
      val l = thisL(context = thisL.context(pathConditionsOpt = Some(
        Logika.PathConditions(th, Util.claimsToExps(jescmPlugins._4, deduceStmt.posOpt.get, context.methodName,
          s0.claims, th, config.atLinesFresh, config.atRewrite)._1))))

      @pure def premises(st: State, sequent: AST.Sequent): (State, HashSMap[AST.ProofAst.StepId, StepProofContext]) = {
        var r = HashSMap.empty[AST.ProofAst.StepId, StepProofContext]
        var id = AST.ProofAst.StepId.Num(-1, AST.Attr(None()))
        var st0 = st
        for (premise <- sequent.premises if st0.ok) {
          st0 = evalRegularStepClaim(smt2, cache, st0, premise, premise.posOpt, reporter)
          r = r + id ~> StepProofContext.Regular(th, id(attr = AST.Attr(premise.posOpt)), premise)
          id = id(no = id.no - 1)
        }
        return (st0, r)
      }
      var st0 = s0
      for (sequent <- deduceStmt.sequents if st0.ok) {
        if (deduceStmt.justOpt.isEmpty && sequent.steps.isEmpty) {
          val pos = sequent.attr.posOpt.get
          var cacheHit = F
          if (config.transitionCache) {
            cache.getTransitionAndUpdateSmt2(th, config, Cache.Transition.Sequent(sequent), context.methodName, st0, smt2) match {
              case Some((ISZ(nextState), cached)) =>
                cacheHit = T
                reporter.coverage(F, cached, pos)
                st0 = nextState
              case _ =>
            }
          }
          if (!cacheHit) {
            var i = 0
            val st00 = st0
            for (premise <- sequent.premises if st0.ok) {
              st0 = evalAssume(smt2, cache, rtCheck, s"Premise #$i", st0, premise, premise.posOpt, reporter)._1
              i = i + 1
            }
            if (st0.ok) {
              st0 = evalAssert(smt2, cache, rtCheck, "Conclusion", st0, sequent.conclusion, sequent.conclusion.posOpt,
                ISZ(), reporter)._1
            }
            if (config.transitionCache && st0.ok) {
              val cached = cache.setTransition(th, config, Cache.Transition.Sequent(sequent), context.methodName, st00, ISZ(st0), smt2)
              reporter.coverage(T, cached, pos)
            } else {
              reporter.coverage(F, zeroU64, pos)
            }
          }
        } else {
          var p = premises(st0, sequent)
          for (step <- sequent.steps if p._1.ok) {
            p = l.evalProofStep(smt2, cache, p, step, reporter)
          }
          st0 = s0(status = p._1.status, nextFresh = p._1.nextFresh, claims = s0.claims)
          val provenClaims = HashSet ++ (for (spc <- p._2.values if spc.isInstanceOf[StepProofContext.Regular]) yield
            th.normalizeExp(spc.asInstanceOf[StepProofContext.Regular].exp))
          if (st0.ok && !provenClaims.contains(th.normalizeExp(sequent.conclusion))) {
            reporter.error(sequent.conclusion.posOpt, Logika.kind, "The sequent's conclusion has not been proven")
            st0 = st0(status = State.Status.Error)
          }
        }
      }
      if (st0.ok) {
        st0 = s0
        @strictpure def bin(e1: AST.Exp, op: String, opKind: AST.ResolvedInfo.BuiltIn.Kind.Type, e2: AST.Exp,
                            posOpt: Option[Position]): AST.Exp =
          AST.Exp.Binary(e1, op, e2, AST.ResolvedAttr(posOpt, Some(AST.ResolvedInfo.BuiltIn(opKind)), Some(AST.Typed.b)), posOpt)
        var i = 0
        for (sequent <- deduceStmt.sequents) {
          val seqClaim: AST.Exp = if (sequent.premises.isEmpty) {
            sequent.conclusion
          } else {
            bin(
              ops.ISZOps(ops.ISZOps(sequent.premises).drop(1)).foldLeft((r: AST.Exp, e: AST.Exp) =>
                bin(r, AST.Exp.BinaryOp.And, AST.ResolvedInfo.BuiltIn.Kind.BinaryAnd, e, e.posOpt),
                sequent.premises(0)), AST.Exp.BinaryOp.Imply, AST.ResolvedInfo.BuiltIn.Kind.BinaryImply,
              sequent.conclusion, sequent.attr.posOpt)
          }
          st0 = thisL(config = config(sat = F)).evalAssume(smt2, cache, F, s"Sequent #$i", st0, seqClaim, seqClaim.posOpt, reporter)._1
          i = i + 1
        }
      }
      return ISZ(st0)
    }

    def evalVarPattern(varPattern: AST.Stmt.VarPattern): (Logika, ISZ[State]) = {
      var r = ISZ[State]()
      var nextFresh = state.nextFresh
      var modIds = HashSet.empty[String]
      for (p <- evalAssignExpValue(split, smt2, cache, varPattern.pattern.typedOpt.get, rtCheck, state, varPattern.init,
        reporter)) {
        val (s1, init) = p
        val s9: State = if (s1.ok) {
          val (s2, sym) = value2Sym(s1, init, varPattern.init.asStmt.posOpt.get)
          val (s3, cond, m) = evalPattern(smt2, cache, rtCheck, s2, sym, varPattern.pattern, reporter)
          if (modIds.isEmpty) {
            for (e <- m.entries) {
              val (id, (_, t, _)) = e
              if (!varPattern.isVal || th.isModifiable(t)) {
                modIds = modIds + id
              }
            }
          }
          var s4 = s3
          for (p <- m.entries) {
            val (id, (v, _, pos)) = p
            val (s5, rhs) = value2Sym(s4, v, pos)
            val s6 = Util.assumeValueInv(this, smt2, cache, rtCheck, s5, rhs, pos, reporter)
            val (s7, lhs) = idIntro(pos, s6, context.methodName, id, rhs.tipe, Some(pos))
            s4 = s7.addClaim(State.Claim.Eq(lhs, rhs))
          }
          val (s8, condSym) = value2Sym(s4, cond, varPattern.pattern.posOpt.get)
          evalAssertH(T, smt2, cache, "Variable Pattern Matching", s8, condSym, varPattern.pattern.posOpt, ISZ(), reporter)
        } else {
          s1
        }
        r = r :+ s9
        if (nextFresh < s9.nextFresh) {
          nextFresh = s9.nextFresh
        }

      }
      val ss: ISZ[State] = for (s <- r) yield s(nextFresh = nextFresh)
      if (context.methodOpt.isEmpty || modIds.isEmpty) {
        return (this, ss)
      } else {
        var thisL = this
        thisL = thisL(context = context(modifiableIds = modIds))
        return (thisL, ss)
      }
    }

    def evalStmtH(): (Logika, ISZ[State]) = {
      stmt match {
        case stmt: AST.Stmt.Expr =>
          stmt.exp match {
            case e: AST.Exp.Invoke =>
              return (this, for (p <- evalExprInvoke(split, smt2, cache, rtCheck, state, stmt, e, reporter)) yield p._1)
            case e =>
              return (this, for (p <- evalExp(split, smt2, cache, rtCheck, state, e, reporter)) yield p._1)
          }
        case stmt: AST.Stmt.Var if stmt.initOpt.nonEmpty =>
          stmt.attr.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              val t = stmt.attr.typedOpt.get
              val ss = evalAssignLocal(T, state, res.context, res.id, stmt.initOpt.get, stmt.attr.typedOpt.get,
                stmt.id.attr.posOpt)
              if (stmt.isVal && !th.isModifiable(t)) {
                return (this, ss)
              }
              var thisL = this
              thisL = thisL(context = context(modifiableIds = context.modifiableIds + res.id))
              return (thisL, ss)
            case _ =>
              reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
              return (this, ISZ(state(status = State.Status.Error)))
          }
        case stmt: AST.Stmt.VarPattern =>
          return evalVarPattern(stmt)
        case stmt: AST.Stmt.Assign =>
          return (this, evalAssign(state, stmt))
        case stmt: AST.Stmt.If =>
          return (this, evalIf(split, smt2, cache, None(), rtCheck, state, stmt, reporter))
        case stmt: AST.Stmt.While =>
          if (config.interp || context.hasInline) {
            return (this, evalWhileUnroll(split, state, stmt))
          } else {
            return (this, evalWhile(state, stmt))
          }
        case stmt: AST.Stmt.For =>
          if (stmt.modifies.isEmpty) {
            reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
            return (this, ISZ(state(status = State.Status.Error)))
          }
          return (this, evalFor(state, stmt))
        case stmt: AST.Stmt.Return =>
          return (this, evalReturn(state, stmt))
        case stmt: AST.Stmt.Block =>
          return (this, evalBlock(split, smt2, cache, None(), rtCheck, state, stmt, reporter))
        case stmt: AST.Stmt.SpecBlock =>
          return (this, evalSpecBlock(split, state, stmt))
        case stmt: AST.Stmt.Match =>
          return (this, evalMatch(split, smt2, cache, None(), rtCheck, state, stmt, reporter))
        case stmt: AST.Stmt.Inv =>
          val s1 = evalInv(None(), F, "Invariant", smt2, cache, rtCheck, state, stmt, HashMap.empty, reporter)
          return (this, ISZ(state(status = s1.status, nextFresh = s1.nextFresh)))
        case stmt: AST.Stmt.DeduceSteps =>
          return (this, evalDeduceSteps(state, stmt))
        case stmt: AST.Stmt.DeduceSequent if stmt.justOpt.isEmpty =>
          return (this, evalDeduceSequent(state, stmt))
        case stmt: AST.Stmt.Induct =>
          return (this, for (sv <- evalExp(split, smt2, cache, rtCheck, state, stmt.exp, reporter)) yield sv._1)
        case _: AST.Stmt.Object => return (this, ISZ(state))
        case _: AST.Stmt.Import => return (this, ISZ(state))
        case _: AST.Stmt.Method => return (this, ISZ(state))
        case _: AST.Stmt.SpecMethod => return (this, ISZ(state))
        case stmt: AST.Stmt.Var if stmt.isSpec => return (this, ISZ(state))
        case _: AST.Stmt.SpecVar => return (this, ISZ(state))
        case _: AST.Stmt.Enum => return (this, ISZ(state))
        case _: AST.Stmt.Adt => return (this, ISZ(state))
        case _: AST.Stmt.Sig => return (this, ISZ(state))
        case _: AST.Stmt.TypeAlias => return (this, ISZ(state))
        case _: AST.Stmt.Fact => return (this, ISZ(state))
        case _: AST.Stmt.Theorem => return (this, ISZ(state))
        case _: AST.Stmt.SubZ => return (this, ISZ(state))
        case _ =>
          reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
          return (this, ISZ(state(status = State.Status.Error)))
      }
    }

    def checkSplits(): (Logika, ISZ[State]) = {
      val p = evalStmtH()
      val ss = p._2
      def check(): B = {
        if (!(ss.size > 0)) {
          return F
        }
        var nextFresh: Z = -1
        for (s <- ss if nextFresh == -1 && s.status != State.Status.Error) {
          nextFresh = s.nextFresh
        }
        return ss.size == 1 || ops.ISZOps(ss).forall((s: State) => s.status == State.Status.Error || nextFresh == s.nextFresh)
      }
      assert(check(),
        st"""${stmt.posOpt.get}:
            |Split statement evaluation does not maintain nextFresh invariant for: ${stmt.prettyST}
            |${(for (s <- ss) yield st"* ${s.toST}", "\n")}""".render)
      if (stmt.isInstruction) {
        reporter.coverage(F, zeroU64, stmt.posOpt.get)
      }
      return p
    }

    return extension.Cancel.cancellable(checkSplits _)
  }

  def logPc(state: State, reporter: Reporter, posOpt: Option[Position]): Unit = {
    reporter.state(jescmPlugins._4, posOpt, context.methodName, th, state, config.atLinesFresh, config.atRewrite)
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

  def checkExp(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, title: String, titleSuffix: String,
               s0: State, exp: AST.Exp, reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp, reporter)) {
      val (s1, v) = p
      val pos = exp.posOpt.get
      val (s2, sym) = value2Sym(s1, v, pos)
      val prop = State.Claim.Prop(T, sym)
      var ok = F
      if (s2.ok) {
        val rvalid = smt2.valid(context.methodName, config, cache, T,
          s"$title$titleSuffix at [${pos.beginLine}, ${pos.beginColumn}]", pos, s2.claims, prop, reporter)
        rvalid.kind match {
          case Smt2Query.Result.Kind.Unsat => ok = T
          case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
          case Smt2Query.Result.Kind.Unknown => error(Some(pos), s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds$titleSuffix", reporter)
          case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
          case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix\n${rvalid.info}", reporter)
        }
      }
      if (ok) {
        r = r :+ s2.addClaim(prop)
      } else {
        r = r :+ s2(status = State.Status.Error)
      }
    }
    return r
  }

  def checkExps(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, title: String, titleSuffix: String,
                s0: State, exps: ISZ[AST.Exp], reporter: Reporter): ISZ[State] = {
    if (config.transitionCache && s0.ok) {
      cache.getTransitionAndUpdateSmt2(th, config, Logika.Cache.Transition.Exps(exps), context.methodName, s0, smt2) match {
        case Some((nextStates, cached)) =>
          for (exp <- exps) {
            reporter.coverage(F, cached, exp.posOpt.get)
          }
          return nextStates
        case _ =>
      }
    }
    var currents = ISZ(s0)
    var done = ISZ[State]()
    for (exp <- exps) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.ok) {
          currents = currents ++ checkExp(split, smt2, cache, rtCheck, title, titleSuffix, current, exp, reporter)
        } else {
          done = done :+ current
        }
      }
    }
    val r = currents ++ done
    if (config.transitionCache && !reporter.hasError) {
      val cached = cache.setTransition(th, config, Logika.Cache.Transition.Exps(exps), context.methodName, s0, r, smt2)
      for (exp <- exps) {
        reporter.coverage(T, cached, exp.posOpt.get)
      }
    } else {
      for (exp <- exps) {
        reporter.coverage(F, zeroU64, exp.posOpt.get)
      }
    }
    return r
  }

  def assumeExp(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, exp: AST.Exp, reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp, reporter)) {
      val (s1, v) = p
      val pos = exp.posOpt.get
      val (s2, sym) = value2Sym(s1, v, pos)
      val prop = State.Claim.Prop(T, sym)
      r = r :+ s2.addClaim(prop)
    }
    return r
  }

  def assumeExps(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rtCheck: B, s0: State, exps: ISZ[AST.Exp],
                 reporter: Reporter): ISZ[State] = {
    val thisL = this
    val l = thisL(config = thisL.config(isAuto = T))
    var currents = ISZ(s0)
    var done = ISZ[State]()
    for (exp <- exps) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.ok) {
          currents = currents ++ l.assumeExp(split, smt2, cache, rtCheck, current, exp, reporter)
        } else {
          done = done :+ current
        }
      }
    }
    return currents ++ done
  }

  def mergeStates(s0: State, cond: State.Value.Sym, sT: State, sF: State, nextFresh: Z): State = {
    @pure def mergeClaimPrefix(i: Z, til: Z): (State.Claim, Z) = {
      var j: Z = i
      var found = F
      while (!found && j < til) {
        if (sT.claims(j) == sF.claims(j)) {
          found = T
        } else {
          j = j + 1
        }
      }
      if (j == i) {
        return (sT.claims(j), j + 1)
      } else {
        return (State.Claim.If(cond, ops.ISZOps(sT.claims).slice(i, j), ops.ISZOps(sF.claims).slice(i, j)), j)
      }
    }

    val size = s0.claims.size
    var prefixClaims = ISZ[State.Claim]()
    var i: Z = 0
    while (i < size) {
      val (c, j) = mergeClaimPrefix(i, size)
      prefixClaims = prefixClaims :+ c
      i = j
    }
    return State(State.statusOf(sT.ok & sF.ok), prefixClaims :+
      State.Claim.If(cond, ops.ISZOps(sT.claims).drop(size + 1),
        ops.ISZOps(sF.claims).drop(size + 1)), nextFresh)
  }

  def evalBody(split: Split.Type, smt2: Smt2, cache: Logika.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
               body: AST.Body, posOpt: Option[Position], reporter: Reporter): ISZ[State] = {
    val s0 = state
    var r = ISZ[State]()
    for (s1 <- evalStmts(this, split, smt2, cache, rOpt, rtCheck, s0, body.stmts, reporter)) {
      if (s1.ok) {
        r = r :+ rewriteLocalVars(this, s1, F, body.undecls, posOpt, reporter)
      } else {
        r = r :+ s1
      }
    }
    return r
  }

  @memoize def retrieveInvs(context: ISZ[String], isObject: B): ISZ[Info.Inv] = {
    if (context.isEmpty) {
      return th.worksheetInvs
    }
    var is = ISZ[Info.Inv]()
    if (isObject) {
      val info = th.nameMap.get(context).get.asInstanceOf[Info.Object]
      for (stmt <- info.ast.stmts) {
        stmt match {
          case stmt: AST.Stmt.Inv => is = is :+ th.nameMap.get(context :+ stmt.id.value).get.asInstanceOf[Info.Inv]
          case _ =>
        }
      }
    } else {
      val (stmts, invs): (ISZ[AST.Stmt], HashSMap[String, Info.Inv]) = th.typeMap.get(context).get match {
        case info: TypeInfo.Adt => (info.ast.stmts, info.invariants)
        case info: TypeInfo.Sig => (info.ast.stmts, info.invariants)
        case info => halt(s"Infeasible: $info")
      }
      for (stmt <- stmts) {
        stmt match {
          case stmt: AST.Stmt.Inv => is = is :+ invs.get(stmt.id.value).get
          case _ =>
        }
      }
    }
    return is
  }

  @pure def singleStateValue(pos: Position, state: State, ps: ISZ[(State, State.Value)]): (State, State.Value) = {
    if (ps.size == 1) {
      return ps(0)
    }
    var svs: ISZ[(State, State.Value)] = for (p <- ps if p._1.ok) yield p
    if (svs.isEmpty) {
      return ps(0)
    }
    if (svs.size == 1) {
      return svs(0)
    }
    val (s0, v0) = svs(0)
    var nextFreshGap = s0.nextFresh - state.nextFresh
    for (i <- 1 until svs.size) {
      val (si, vi) = svs(i)
      val gap = si.nextFresh - state.nextFresh
      assert(gap >= 0)
      val rw = Util.SymAddRewriter(state.nextFresh, nextFreshGap, jescmPlugins._4)
      svs = svs(i ~> (si(claims = for (c <- si.claims) yield rw.transformStateClaim(c).getOrElse(c)),
        rw.transformStateValue(vi).getOrElse(vi)))
      nextFreshGap = nextFreshGap + gap
    }
    val nextFresh = state.nextFresh + nextFreshGap
    val sym = State.Value.Sym(nextFresh, v0.tipe, pos)
    var commonClaims = ISZ[State.Claim]()
    var claimss = ISZ.create(svs.size, ISZ[State.Claim]())
    val s0ClaimsSize = s0.claims.size
    var maxClaims = s0ClaimsSize
    for (i <- 1 until svs.size if svs(i)._1.ok) {
      if (svs(i)._1.claims.size > maxClaims) {
        maxClaims = svs(i)._1.claims.size
      }
    }
    for (j <- 0 until maxClaims) {
      var hasDiff = F
      for (i <- 1 until svs.size) {
        val si = svs(i)._1
        if (j < s0ClaimsSize) {
          if (j < si.claims.size) {
            val c = si.claims(j)
            if (s0.claims(j) != c) {
              hasDiff = T
              claimss = claimss(i ~> (claimss(i) :+ c))
            }
          } else {
            hasDiff = T
          }
        } else {
          hasDiff = T
          if (j < si.claims.size) {
            claimss = claimss(i ~> (claimss(i) :+ si.claims(j)))
          }
        }
      }
      if (hasDiff) {
        if (j < s0ClaimsSize) {
          claimss = claimss(0 ~> (claimss(0) :+ s0.claims(j)))
        }
      } else {
        commonClaims = commonClaims :+ s0.claims(j)
      }
    }
    for (i <- 0 until svs.size) {
      claimss = claimss(i ~> (claimss(i) :+ State.Claim.Let.Def(sym, svs(i)._2)))
    }
    val claims: ISZ[State.Claim] = commonClaims :+ State.Claim.Or(for (claims <- claimss) yield State.Claim.And(claims))
    return (State(status = State.Status.Normal, claims = claims, nextFresh = nextFresh + 1), sym)
  }

  @pure def singleState(ss: ISZ[State]): State = {
    assert(ss.size == 1)
    return ss(0)
  }

  @pure def maxStatesNextFresh(ss: ISZ[State]): Z = {
    var r: Z = -1
    for (s <- ss if r < s.nextFresh) {
      r = s.nextFresh
    }
    assert(r >= 0)
    return r
  }

  @pure def maxStateValuesNextFresh(svs: ISZ[(State, State.Value)]): Z = {
    var r: Z = -1
    for (p <- svs if r < p._1.nextFresh) {
      r = p._1.nextFresh
    }
    assert(r >= 0)
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
