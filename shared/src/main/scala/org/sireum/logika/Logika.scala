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

package org.sireum.logika

import org.sireum._
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.symbol.Resolver.{NameMap, QName, TypeMap}
import org.sireum.lang.{ast => AST}
import org.sireum.message.{Message, Position}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.plugin._
import org.sireum.lang.tipe.TypeOutliner.ExpTypedSubst

object Logika {

  @enum object Split {
    "Default"
    "Enabled"
    "Disabled"
  }

  type Bindings = Map[String, (State.Value.Sym, AST.Typed, Position)]

  type LeafClaims = ISZ[(State.Claim, ISZ[ISZ[State.Claim]])]

  @datatype class Branch(val title: String,
                         val sym: State.Value.Sym,
                         val body: AST.Body,
                         val bindings: Bindings,
                         val bindingIdMap: HashMap[String, (Z, ISZ[Position])])

  object Reporter {
    object Info {
      @enum object Kind {
        "Verified"
      }
    }
    def create: Reporter = {
      return ReporterImpl(ISZ())
    }
  }

  @msig trait Reporter extends message.Reporter {
    def state(plugins: ISZ[logika.plugin.ClaimPlugin], posOpt: Option[Position], context: ISZ[String],
              th: TypeHierarchy, s: State, atLinesFresh: B): Unit

    def query(pos: Position, title: String, time: Z, r: Smt2Query.Result): Unit

    def inform(pos: Position, kind: Reporter.Info.Kind.Type, message: String): Unit

    def empty: Reporter

    def combine(other: Reporter): Reporter

    def illFormed(): Unit
  }

  @record class ReporterImpl(var _messages: ISZ[Message]) extends Reporter {
    var _ignore: B = F

    override def state(plugins: ISZ[logika.plugin.ClaimPlugin], posOpt: Option[Position], context: ISZ[String],
                       th: TypeHierarchy, s: State, atLinesFresh: B): Unit = {
    }

    override def query(pos: Position, title: String, time: Z, r: Smt2Query.Result): Unit = {
    }

    override def inform(pos: Position, kind: Reporter.Info.Kind.Type, message: String): Unit = {
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

  val kind: String = "Logika"
  val parsingDesc: String = "Parsing"
  val libraryDesc: String = "Library"
  val typeCheckingDesc: String = "Type Checking"
  val verifyingDesc: String = "Verifying"
  val defaultPlugins: ISZ[Plugin] = ISZ(AutoPlugin(), Smt2Plugin(), ClaimOfPlugin(), LiftPlugin(), PropNatDedPlugin(),
    PredNatDedPlugin(), InceptionPlugin())
  val builtInByNameMethods: HashSet[(B, QName, String)] = HashSet ++ ISZ(
    (F, AST.Typed.isName, "size"), (F, AST.Typed.msName, "size"),
    (F, AST.Typed.isName, "firstIndex"), (F, AST.Typed.msName, "firstIndex"),
    (F, AST.Typed.isName, "lastIndex"), (F, AST.Typed.msName, "lastIndex"),
    (F, AST.Typed.f32Name, "isNaN"), (F, AST.Typed.f32Name, "isInfinite"),
    (F, AST.Typed.f64Name, "isNaN"), (F, AST.Typed.f64Name, "isInfinite"),
  )
  val indexingFields: HashSet[String] = HashSet ++ ISZ[String]("firstIndex", "lastIndex")
  val emptyBindings: Bindings = Map.empty[String, (State.Value.Sym, AST.Typed, Position)]
  val trueClaim: State.Claim = State.Claim.And(ISZ())
  val idxSuffix: String = "$Idx"

  def checkStmts(initStmts: ISZ[AST.Stmt], typeStmts: ISZ[(ISZ[String], AST.Stmt)], config: Config, th: TypeHierarchy,
                 smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Smt2.Cache, reporter: Reporter,
                 par: Z, plugins: ISZ[Plugin], verifyingStartTime: Z, includeInit: B, line: Z,
                 skipMethods: ISZ[String], skipTypes: ISZ[String]): Unit = {

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
      for (stmt <- stmts) {
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
          case stmt: AST.Stmt.Method if stmt.bodyOpt.nonEmpty && !noMethods(owner, stmt.sig.id.value) =>
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
        r = Task.Stmts(th, config, initStmts, plugins) +: r
      }
      return r
    }

    val tasks = findTasks()

    val smt2 = smt2f(th)

    def combine(r1: Reporter, r2: Reporter): Reporter = {
      val r = r1.combine(r2)
      return r
    }

    def compute(task: Task): Reporter = {
      val r = reporter.empty
      val csmt2 = smt2
      task.compute(csmt2, cache, r)
      return r
    }

    extension.Cancel.cancellable { () =>
      combine(reporter, ops.ISZOps(tasks).mParMapFoldLeftCores[Reporter, Reporter](compute _, combine _, reporter.empty, par))
    }
    if (verifyingStartTime != 0) {
      reporter.timing(verifyingDesc, extension.Time.currentMillis - verifyingStartTime)
    }
  }

  def checkScript(fileUriOpt: Option[String], input: String, config: Config,
                  smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Smt2.Cache, reporter: Reporter,
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
              checkStmts(p.body.stmts, ISZ(), config, th, smt2f, cache, reporter, config.parCores, plugins, verifyingStartTime, T,
                line, skipMethods, skipTypes)
            }
          } else {
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

  def checkPrograms(sources: ISZ[(Option[String], String)], files: ISZ[String], config: Config, th: TypeHierarchy,
                    smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Smt2.Cache, reporter: Reporter,
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

    checkTypedPrograms(verifyingStartTime, fileSet, config, th4, smt2f, cache, reporter, config.parCores, plugins, line,
      skipMethods, skipTypes)
  }

  def checkTypedPrograms(verifyingStartTime: Z, fileSet: HashSSet[String], config: Config, th: TypeHierarchy,
                         smt2f: lang.tipe.TypeHierarchy => Smt2, cache: Smt2.Cache, reporter: Reporter, par: Z,
                         plugins: ISZ[Plugin], line: Z, skipMethods: ISZ[String], skipTypes: ISZ[String]): Unit = {
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
    checkStmts(ISZ(), typeStmts, config, th, smt2f, cache, reporter, par, plugins, verifyingStartTime, F, line,
      skipMethods, skipTypes)
  }
}

import Logika._
import Util._

@datatype class Logika(val th: lang.tipe.TypeHierarchy,
                       val config: Config,
                       val context: Context,
                       val plugins: ISZ[Plugin]) {

  val jescPlugins: (ISZ[plugin.JustificationPlugin], ISZ[plugin.ExpPlugin], ISZ[plugin.StmtPlugin], ISZ[plugin.ClaimPlugin]) = {
    var jps = ISZ[plugin.JustificationPlugin]()
    var eps = ISZ[plugin.ExpPlugin]()
    var sps = ISZ[plugin.StmtPlugin]()
    var cps = ISZ[plugin.ClaimPlugin]()
    for (p <- plugins) {
      p match {
        case p: plugin.JustificationPlugin => jps = jps :+ p
        case p: plugin.ExpPlugin => eps = eps :+ p
        case p: plugin.StmtPlugin => sps = sps :+ p
        case p: plugin.ClaimPlugin => cps = cps :+ p
        case _: plugin.MethodPlugin =>
        case _: plugin.StmtsPlugin =>
        case _ => halt(s"Unexpected plugin: $p")
      }
    }
    (jps, eps, sps, cps)
  }

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

  def checkSeqIndexing(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State, seq: State.Value, i: State.Value,
                       posOpt: Option[Position], reporter: Reporter): State = {
    if (!rtCheck) {
      return s0
    }
    val pos = posOpt.get
    val (s1, v) = s0.freshSym(AST.Typed.b, pos)
    val s2 = s1.addClaim(State.Claim.Let.SeqInBound(v, seq, i))
    val claim = State.Claim.Prop(T, v)
    val (implicitCheckOpt, implicitPosOpt, suffixOpt): (Option[String], Option[Position], Option[String]) =
      context.implicitCheckTitlePosOpt match {
        case Some((t, p)) => (Some(t), Some(p), Some(s" at [${pos.beginLine}, ${pos.beginColumn}]"))
        case _ => (None(), posOpt, None())
      }
    if (s2.status) {
      val r = smt2.valid(cache, T, config.logVc, config.logVcDirOpt, st"${implicitCheckOpt}Implicit Indexing Assertion at [${pos.beginLine}, ${pos.beginColumn}]".render,
        pos, s2.claims, claim, reporter)
      r.kind match {
        case Smt2Query.Result.Kind.Unsat => return s0
        case Smt2Query.Result.Kind.Sat => error(implicitPosOpt, st"${implicitCheckOpt}Possibly out of bound sequence indexing$suffixOpt".render, reporter)
        case Smt2Query.Result.Kind.Unknown => error(implicitPosOpt, st"${implicitCheckOpt}Could not deduce that the sequence indexing is in bound$suffixOpt".render, reporter)
        case Smt2Query.Result.Kind.Timeout => error(implicitPosOpt, st"${implicitCheckOpt}Timed out when deducing that the sequence indexing is in bound$suffixOpt".render, reporter)
        case Smt2Query.Result.Kind.Error => error(implicitPosOpt, st"${implicitCheckOpt}Error encountered when deducing that the sequence indexing is in bound$suffixOpt".render, reporter)
      }
    }
    return s2(status = F)
  }

  def evalLit(smt2: Smt2, lit: AST.Lit, reporter: Reporter): State.Value = {
    lit match {
      case e: AST.Exp.LitB => return State.Value.B(e.value, e.posOpt.get)
      case e: AST.Exp.LitC => return State.Value.C(e.value, e.posOpt.get)
      case e: AST.Exp.LitF32 =>
        smt2.addType(AST.Typed.f32, reporter)
        return State.Value.F32(e.value, e.posOpt.get)
      case e: AST.Exp.LitF64 =>
        smt2.addType(AST.Typed.f64, reporter)
        return State.Value.F64(e.value, e.posOpt.get)
      case e: AST.Exp.LitR => return State.Value.R(e.value, e.posOpt.get)
      case e: AST.Exp.LitString => return State.Value.String(e.value, e.posOpt.get)
      case e: AST.Exp.LitZ => return State.Value.Z(e.value, e.posOpt.get)
      case e: AST.Exp.LitStepId => halt(s"Infeasible: $e")
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

  def evalStringInterpolate(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State,
                            lit: AST.Exp.StringInterpolate, reporter: Reporter): ISZ[(State, State.Value)] = {
    var r = ISZ[(State, State.Value)]()
    val isST = lit.prefix == "st"
    for (p <- evalExps(split, smt2, cache, rtCheck, state, lit.args.size, (n: Z) => lit.args(n), reporter)) {
      val s0 = p._1
      val pos = lit.posOpt.get
      val (s1, v) = s0.freshSym(if (isST) AST.Typed.st else AST.Typed.string, pos)
      r = r :+ ((s1.addClaim(State.Claim.Let.Random(v, pos)), v))
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
      case string"f32" =>
        smt2.addType(AST.Typed.f32, reporter)
        return State.Value.F32(org.sireum.F32(lit.lits(0).value).get, lit.posOpt.get)
      case string"f64" =>
        smt2.addType(AST.Typed.f64, reporter)
        return State.Value.F64(org.sireum.F64(lit.lits(0).value).get, lit.posOpt.get)
      case _ =>
        val t = lit.typedOpt.get
        val ids = t.asInstanceOf[AST.Typed.Name].ids
        th.typeMap.get(ids).get match {
          case ti: TypeInfo.SubZ =>
            smt2.addType(t, reporter)
            return text2SubZVal(ti, lit.lits(0).value, lit.posOpt.get)
          case _ =>
        }
        halt(s"TODO: $lit")
    }
  }

  def evalConstantVar(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State, info: Info.Var, reporter: Reporter): Option[(State, State.Value)] = {
    if (!info.ast.isVal) {
      return None()
    }
    AST.Util.constantInitOpt(info.ast) match {
      case Some(exp) =>
        val r = evalExp(Split.Disabled, smt2, cache, rtCheck, s0, exp, reporter)
        assert(r.size == 1)
        return Some(r(0))
      case _ =>
        return None()
    }
  }

  def evalConstantVarInstance(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State, owner: ISZ[String], id: String,  reporter: Reporter): Option[(State, State.Value)] = {
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


  def evalThisIdH(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, id: String, t: AST.Typed, pos: Position, reporter: Reporter): (State, State.Value) = {
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

  def evalExps(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, numOfExps: Z,
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
          if (s1.status) {
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

  def evalArgs(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, numOfArgs: Z,
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

  def evalExp(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, e: AST.Exp,
              reporter: Reporter): ISZ[(State, State.Value)] = {
    if (!state.status) {
      return ISZ((state, State.errorValue))
    }
    val ePlugins = jescPlugins._2
    if (jescPlugins._2.nonEmpty) {
      for (p <- ePlugins if p.canHandle(this, e)) {
        return p.handle(this, smt2, cache, state, e, reporter)
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
                s1 = evalAssertH(T, smt2, cache, s"Min range check for $t", s3, sym, e.posOpt, reporter)
              }
              if (s1.status && ti.ast.hasMax) {
                val (s4, sym) = s1.freshSym(AST.Typed.b, pos)
                val s5 = s4.addClaim(State.Claim.Let.Binary(sym, value, AST.Exp.BinaryOp.Le, z2SubZVal(ti, ti.ast.max, pos), t))
                s1 = evalAssertH(T, smt2, cache, s"Max range check for $t", s5, sym, e.posOpt, reporter)
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
          return (s0(status = F), State.errorValue)
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

          return for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp.exp, reporter)) yield evalUnaryExpH(p)
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $exp")
          return ISZ((s0(status = F), State.errorValue))
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
        if (!rtCheck || !s0.status) {
          return s0
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
        val r = smt2.valid(cache, T, config.logVc, config.logVcDirOpt,
          st"${implicitCheckOpt}Non-zero second operand of '$op' at [${pos.beginLine}, ${pos.beginColumn}]".render,
          pos, s0.claims :+ claim, State.Claim.Prop(T, sym), reporter)
        r.kind match {
          case Smt2Query.Result.Kind.Unsat => return s1.addClaim(claim)
          case Smt2Query.Result.Kind.Sat => error(implicitPosOpt, st"${implicitCheckOpt}Possibly zero second operand for ${exp.op}$suffixOpt".render, reporter)
          case Smt2Query.Result.Kind.Unknown => error(implicitPosOpt, st"${implicitCheckOpt}Could not deduce non-zero second operand for ${exp.op}$suffixOpt".render, reporter)
          case Smt2Query.Result.Kind.Timeout => error(implicitPosOpt, st"${implicitCheckOpt}Timed out when deducing non-zero second operand for ${exp.op}$suffixOpt".render, reporter)
          case Smt2Query.Result.Kind.Error => error(implicitPosOpt, st"${implicitCheckOpt}Error encountered when deducing non-zero second operand for ${exp.op}$suffixOpt".render, reporter)
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

            return for (p <- evalExp(split, smt2, cache, rtCheck, s1, exp.right, reporter); r <- evalCondAndH(p)) yield r
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

            return for (p <- evalExp(split, smt2, cache, rtCheck, s1, exp.right, reporter); r <- evalCondOrH(p)) yield r
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

            return for (p <- evalExp(split, smt2, cache, rtCheck, s1, exp.right, reporter); r <- evalCondImplyH(p)) yield r
          case _ => halt("Infeasible")
        }
      }

      def evalSeq(s0: State, m: AST.ResolvedInfo.Method): ISZ[(State, State.Value)] = {
        var r = ISZ[(State, State.Value)]()
        for (p1 <- evalExp(split, smt2, cache, rtCheck, s0, exp.left, reporter)) {
          val (s1, v1) = p1
          if (s1.status) {
            for (p2 <- evalExp(split, smt2, cache, rtCheck, s1, exp.right, reporter)) {
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
          var maxFresh = s0.nextFresh
          for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp.left, reporter)) {
            val (s1, v1) = p
            if (s1.status) {
              if (kind == AST.ResolvedInfo.BuiltIn.Kind.BinaryMapsTo) {
                for (svs2 <- evalMapsTo(s1, v1)) {
                  if (maxFresh < svs2._1.nextFresh) {
                    maxFresh = svs2._1.nextFresh
                  }
                  r = r :+ svs2
                }
              } else if (isCond(kind)) {
                val (s2, left) = value2Sym(s1, v1, exp.left.posOpt.get)
                for (svs2 <-evalCond(s2, kind, left)) {
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
                r = r :+ ((s1(status = F), State.errorValue))
              }
            } else {
              r = r :+ ((s1, State.errorValue))
            }
          }
          return for (svs <- r) yield (svs._1(nextFresh = maxFresh), svs._2)
        case m: AST.ResolvedInfo.Method =>
          if (isSeq(m)) {
            return evalSeq(s0, m)
          }
          val posOpt = exp.posOpt
          return evalInvoke(s0, Some(exp.left), AST.Exp.Ident(AST.Id(exp.op, AST.Attr(posOpt)), exp.attr),
            Either.Left(ISZ(exp.right)), exp.attr)
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((s0(status = F), State.errorValue))
      }
    }

    def evalInstanceOfAs(isCast: B, receiverOpt: Option[AST.Exp], tipe: AST.Typed, pos: Position): ISZ[(State, State.Value)] = {
      var r = ISZ[(State, State.Value)]()
      for (p <- evalExp(split, smt2, cache, rtCheck, state, receiverOpt.get, reporter)) {
        val (s0, v) = p
        if (s0.status) {
          val (s1, cond) = s0.freshSym(AST.Typed.b, pos)
          val s2 = s1.addClaim(State.Claim.Let.TypeTest(cond, F, v, tipe))
          if (isCast) {
            if (!rtCheck) {
              val (s3, cv) = s2.freshSym(tipe, pos)
              r = r :+ ((s3.addClaim(State.Claim.Let.Def(cv, v)), cv))
            } else {
              val s3 = evalAssertH(T, smt2, cache, "asInstanceOf", s2, cond, Some(pos), reporter)
              if (s3.status) {
                val (s4, cv) = s3.freshSym(tipe, pos)
                r = r :+ ((s4.addClaim(State.Claim.Let.Def(cv, v)), cv))
              } else {
                r = r :+ ((s3, State.errorValue))
              }
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
                  if (!rtCheck) {
                    // skip
                  } else {
                    val (s1, size) = s0.freshSym(AST.Typed.z, pos)
                    val (s2, cond) = s1.addClaim(State.Claim.Let.FieldLookup(size, o, "size")).freshSym(AST.Typed.b, pos)
                    val s3 = s2.addClaim(State.Claim.Let.Binary(cond, size, AST.Exp.BinaryOp.Gt, State.Value.Z(0, pos), AST.Typed.z))
                    s0 = evalAssertH(T, smt2, cache, s"Non-empty check for $tipe", s3, cond, Some(pos), reporter)
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
          if (s6.status) {
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
          if (s1.status) {
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
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((state(status = F), State.errorValue))
      }
    }

    def evalSelect(exp: AST.Exp.Select): ISZ[(State, State.Value)] = {
      val pos = exp.id.attr.posOpt.get
      @pure def random(tpe: AST.Typed): ISZ[(State, State.Value)] = {
        val s0 = state
        val (s1, sym) = s0.freshSym(tpe, pos)
        val s2 = s1.addClaim(State.Claim.Let.Random(sym, pos))
        return ISZ((Util.assumeValueInv(this, smt2, cache, rtCheck, s2, sym, pos, reporter), sym))
      }
      exp.attr.resOpt.get match {
        case res: AST.ResolvedInfo.BuiltIn if res.kind == AST.ResolvedInfo.BuiltIn.Kind.Random =>
          return random(exp.typedOpt.get)
        case res: AST.ResolvedInfo.BuiltIn if res.kind == AST.ResolvedInfo.BuiltIn.Kind.IsInstanceOf ||
          res.kind == AST.ResolvedInfo.BuiltIn.Kind.AsInstanceOf =>
          return evalInstanceOfAs(res.kind == AST.ResolvedInfo.BuiltIn.Kind.AsInstanceOf, exp.receiverOpt,
            exp.targs(0).typedOpt.get, exp.posOpt.get)
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Ext  =>
          if (res.owner.size == 3 && ops.ISZOps(res.owner).dropRight(1) == AST.Typed.sireumName && res.id == "random") {
            return random(res.tpeOpt.get.ret)
          } else {
            val mType = res.tpeOpt.get
            val attr = AST.ResolvedAttr(exp.id.attr.posOpt, exp.attr.resOpt, Some(mType.ret))
            return evalInvoke(state, None(), AST.Exp.Ident(exp.id, exp.attr), Either.Left(ISZ()), attr)
          }
        case res: AST.ResolvedInfo.Method if res.mode == AST.MethodMode.Method && res.tpeOpt.get.isByName &&
          !Logika.builtInByNameMethods.contains((res.isInObject, res.owner, res.id)) =>
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
        val (s0, sym) = state.freshSym(t, attr.posOpt.get)
        for (p <- evalArgs(sp, smt2, cache, rtCheck, s0, -1, eargs, reporter)) {
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
        for (p <- evalArgs(sp, smt2, cache, rtCheck, s1, params.size, eargs, reporter)) {
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
            val s4 = s3.addClaim(State.Claim.Let.AdtLit(sym, args.toIS[Option[State.Value]].map((vOpt: Option[State.Value]) => vOpt.get)))
            val (s5, vs) = addValueInv(this, smt2, cache, T, s4, sym, attr.posOpt.get, reporter)
            var s6 = s5
            for (v <- vs if s6.status) {
              s6 = evalAssertH(T, smt2, cache, st"Invariant on ${(ti.name, ".")} construction".render, s6, v, attr.posOpt, reporter)
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
            return ISZ(evalThis(AST.Exp.This(AST.TypedAttr(ident.posOpt, context.methodOpt.get.receiverTypeOpt))))
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
      for (p0 <- srcv; p1 <- evalExp(split, smt2, cache, rtCheck, p0._1, exp.args(0), reporter)) {
        val (_, seq) = p0
        val (s1, iv) = p1
        val AST.Typed.Tuple(ISZ(iType, vType)) = iv.tipe
        val pos = exp.posOpt.get
        val (s2, i) = s1.freshSym(iType, pos)
        val (s3, v) = s2.freshSym(vType, pos)
        val (s4, newSeq) = s3.freshSym(seq.tipe, pos)
        r = r :+ ((s4.addClaims(ISZ(
          State.Claim.Let.FieldLookup(i, iv, "_1"),
          State.Claim.Let.FieldLookup(v, iv, "_2"),
          State.Claim.Let.SeqStore(newSeq, seq, i, v)
        )), newSeq))
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
      def rand(num: Z): (State, State.Value) = {
        val t = exp.tipeOpt.get.typedOpt.get
        val finder = Util.RandomFinder(t, num, HashMap.empty, None())
        finder.transformState(state)
        finder.rOpt match {
          case Some(r) =>
            return (state, r.sym)
          case _ =>
            reporter.error(exp.posOpt, kind, st"Could not find .random of $t with the occurrence number $num".render)
            return (state(status = F), State.errorValue)
        }
      }
      def local(res: AST.ResolvedInfo.LocalVar, num: Z): (State, State.Value) = {
        val finder = Util.LocalVarIdFinder(res, num, HashMap.empty, None())
        finder.transformState(state)
        finder.rOpt match {
          case Some(r) =>
            return (state, r.sym)
          case _ =>
            reporter.error(exp.posOpt, kind, st"Could not find ${res.id} with the occurrence number $num".render)
            return (state(status = F), State.errorValue)
        }
      }
      def global(res: AST.ResolvedInfo.Var, num: Z): (State, State.Value) = {
        val finder = Util.VarNameFinder(res, num, HashMap.empty, None())
        finder.transformState(state)
        finder.rOpt match {
          case Some(r) =>
            return (state, r.sym)
          case _ =>
            reporter.error(exp.posOpt, kind, st"Could not find ${(res.owner :+ res.id, ".")} with the occurrence number $num".render)
            return (state(status = F), State.errorValue)
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

    def evalInput(input: AST.Exp.Input): (State, State.Value) = {
      input.exp match {
        case e: AST.Exp.Ref =>
          e.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              context.methodOpt.get.localInMap.get(res.id) match {
                case Some(sym) => return (state, sym)
                case _ =>
                  error(e.posOpt, s"Variable $e was not declared to be read/modified", reporter)
                  return (state(status = F), State.Value.B(F, e.posOpt.get))
              }
            case res: AST.ResolvedInfo.Var =>
              if (res.isInObject) {
                val ids = res.owner :+ res.id
                context.methodOpt.get.objectVarInMap.get(ids) match {
                  case Some(sym) => return (state, sym)
                  case _ =>
                    error(e.posOpt, s"Variable $e was not declared to be read/modified", reporter)
                    return (state(status = F), State.Value.B(F, e.posOpt.get))
                }
              } else {
                context.methodOpt.get.fieldVarInMap.get(res.id) match {
                  case Some(sym) =>
                    return (state, sym)
                  case _ =>
                    error(e.posOpt, s"Variable $e was not declared to be read/modified", reporter)
                    return (state(status = F), State.Value.B(F, e.posOpt.get))
                }
              }
            case _ =>
          }
        case e: AST.Exp.This =>
          context.methodOpt.get.localInMap.get("this") match {
            case Some(sym) => return (state, sym)
            case _ =>
              error(e.posOpt, s"this was not declared to be modified", reporter)
              return (state(status = F), State.Value.B(F, e.posOpt.get))
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
      var nextFresh = s1.nextFresh
      val sp: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
      for (p <- evalAssignExpValue(sp, smt2, cache, AST.Typed.b, rtCheck, s1, quant.fun.exp, reporter)) {
        val (s8, v) = p
        val (s9, expSym) = value2Sym(s8, v, quant.fun.exp.asStmt.posOpt.get)
        if (s9.status) {
          quantClaims = quantClaims ++ ops.ISZOps(s9.claims).slice(s1.claims.size, s9.claims.size) :+ State.Claim.Prop(T, expSym)
        }
        if (nextFresh < s9.nextFresh) {
          nextFresh = s9.nextFresh
        }
      }
      val vars: ISZ[State.Claim.Let.Quant.Var] =
        for (p <- quant.fun.params) yield State.Claim.Let.Quant.Var(quant.fun.context, p.idOpt.get.value, p.typedOpt.get)
      if (quantClaims.isEmpty) {
        return (s0(status = F), State.errorValue)
      }
      val qcs: ISZ[State.Claim] = if (s0.claims.size != s1.claims.size) {
        val p = s1.claims(s0.claims.size)
        if (quant.isForall) ISZ(State.Claim.Imply(ISZ(p, bigAnd(quantClaims)))) else p +: quantClaims
      } else {
        quantClaims
      }
      return (s0(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, qcs)), sym)
    }

    def evalQuantRange(quant: AST.Exp.QuantRange): ISZ[(State, State.Value)] = {
      val qVarType = quant.attr.typedOpt.get
      val qVarRes = quant.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
      val s0 = state
      val sp: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
      var r = ISZ[(State, State.Value)]()
      for (p1 <- evalExp(sp, smt2, cache, rtCheck, s0, quant.lo, reporter);
           p2 <- evalExp(sp, smt2, cache, rtCheck, p1._1, quant.hi, reporter)) {
        val (_, lo) = p1
        val (s2, hi) = p2
        if (s2.status) {
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
          var nextFresh: Z = s8.nextFresh
          for (p <- evalAssignExpValue(sp, smt2, cache, AST.Typed.b, rtCheck, s9.addClaim(rangeProp), quant.fun.exp, reporter)) {
            val (s10, v) = p
            val (s11, vSym) = value2Sym(s10, v, quant.fun.exp.asStmt.posOpt.get)
            val s12 = s11.addClaims(
              if (quant.isForall) ISZ(State.Claim.Imply(ISZ(rangeProp, State.Claim.Prop(T, vSym))))
              else ISZ(rangeProp, State.Claim.Prop(T, vSym))
            )
            if (s12.status) {
              val s12ClaimsOps = ops.ISZOps(s12.claims)
              quantClaims = quantClaims ++ s12ClaimsOps.slice(s2.claims.size, s9.claims.size) ++
                s12ClaimsOps.slice(s9.claims.size + 1, s12.claims.size)
            }
            if (nextFresh < s12.nextFresh) {
              nextFresh = s12.nextFresh
            }
          }
          if (quantClaims.isEmpty) {
            r = r :+ ((s2(status = F), State.errorValue))
          } else {
            r = r :+ ((s2(nextFresh = nextFresh).addClaim(State.Claim.Let.Quant(sym, quant.isForall, vars, quantClaims)), sym))
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
      val sp: Split.Type = if (config.dontSplitPfq) Split.Default else Split.Enabled
      var r = ISZ[(State, State.Value)]()
      for (p1 <- evalExp(sp, smt2, cache, rtCheck, s0, seqExp, reporter)) {
        val (s2, s) = p1
        if (s2.status) {
          val (s3, ident) = evalIdentH(s2, quant.attr.resOpt.get, qVarType, quant.fun.params(0).idOpt.get.attr.posOpt.get)
          val (s4, inBoundSym) = s3.freshSym(AST.Typed.b, seqExp.posOpt.get)
          val s5 = s4.addClaim(State.Claim.Let.SeqInBound(inBoundSym, s, ident))
          val inBoundProp = State.Claim.Prop(T, inBoundSym)
          val (s6, sym) = s5.freshSym(AST.Typed.b, quant.attr.posOpt.get)
          val vars = ISZ[State.Claim.Let.Quant.Var](State.Claim.Let.Quant.Var(quant.fun.context, qVarRes.id, qVarType))
          var quantClaims = ISZ[State.Claim]()
          var nextFresh: Z = s6.nextFresh
          for (p <- evalAssignExpValue(sp, smt2, cache, AST.Typed.b, rtCheck, s6.addClaims(ISZ(inBoundProp)),
            quant.fun.exp, reporter)) {
            val (s7, v) = p
            val (s8, vSym) = value2Sym(s7, v, quant.fun.exp.asStmt.posOpt.get)
            val s9 = s8.addClaims(
              if (quant.isForall) ISZ(State.Claim.Imply(ISZ(inBoundProp, State.Claim.Prop(T, vSym))))
              else ISZ(inBoundProp, State.Claim.Prop(T, vSym))
            )
            if (s9.status) {
              val s9ClaimsOps = ops.ISZOps(s9.claims)
              quantClaims = quantClaims ++ s9ClaimsOps.slice(s2.claims.size, s6.claims.size) ++
                s9ClaimsOps.slice(s6.claims.size + 1, s9.claims.size)
            }
            if (nextFresh < s9.nextFresh) {
              nextFresh = s9.nextFresh
            }
          }
          if (quantClaims.isEmpty) {
            r = r :+ ((s2(status = F), State.errorValue))
          } else {
            r = r :+ ((s2(nextFresh = nextFresh).addClaim(
              State.Claim.Let.Quant(sym, quant.isForall, vars, quantClaims)), sym))
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
      for (p <- evalExp(sp, smt2, cache, rtCheck, state, quant.seq, reporter)) {
        val (s0, seq) = p
        if (s0.status) {
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
          var nextFresh: Z = s10.nextFresh
          for (p <- evalAssignExpValue(sp, smt2, cache, AST.Typed.b, rtCheck, s10.addClaims(ISZ(inBoundProp)), quant.fun.exp, reporter)) {
            val (s11, v) = p
            val (s12, vSym) = value2Sym(s11, v, quant.fun.exp.asStmt.posOpt.get)
            var prop: State.Claim =
              if (quant.isForall) State.Claim.Imply(ISZ(State.Claim.Prop(T, eqSym), State.Claim.Prop(T, vSym)))
              else State.Claim.And(ISZ(State.Claim.Prop(T, eqSym), State.Claim.Prop(T, vSym)))
            if (invSyms.nonEmpty) {
              prop = State.Claim.And(
                (for (invSym <- invSyms) yield State.Claim.Prop(T, invSym).asInstanceOf[State.Claim]) :+ prop)
            }
            val s13 = s12.addClaims(
              if (quant.isForall) ISZ(State.Claim.Imply(ISZ(inBoundProp, prop)))
              else ISZ(inBoundProp, prop))
            if (s13.status) {
              val s13ClaimsOps = ops.ISZOps(s13.claims)
              quantClaims = quantClaims ++ s13ClaimsOps.slice(s0.claims.size, s10.claims.size) ++
                  s13ClaimsOps.slice(s10.claims.size + 1, s13.claims.size
              )
            }
            if (nextFresh < s13.nextFresh) {
              nextFresh = s13.nextFresh
            }
          }
          if (quantClaims.isEmpty) {
            r = r :+ ((s0(status = F), State.errorValue))
          } else {
            r = r :+ ((s0(nextFresh = nextFresh).addClaim(
              State.Claim.Let.Quant(sym, quant.isForall, vars, quantClaims)), sym))
          }
        } else {
          r = r :+ ((s0, State.errorValue))
        }
      }
      return r
    }

    def methodInfo(isInObject: B, owner: QName, id: String): Context.InvokeMethodInfo = {
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
            return Context.InvokeMethodInfo(mi.ast.isHelper, mi.ast.sig, mi.ast.contract,
              extractResolvedInfo(mi.ast.attr), extractAssignExpOpt(mi))
          case Some(mi: lang.symbol.Info.ExtMethod) =>
            return Context.InvokeMethodInfo(T, mi.ast.sig, mi.ast.contract, extractResolvedInfo(mi.ast.attr), None())
          case Some(mi: lang.symbol.Info.SpecMethod) =>
            val typedAttr = AST.TypedAttr(mi.ast.sig.id.attr.posOpt, mi.ast.sig.returnType.typedOpt)
            return Context.InvokeMethodInfo(T, mi.ast.sig, AST.MethodContract.Simple.empty,
              extractResolvedInfo(mi.ast.attr), Some(AST.Stmt.Expr(
                AST.Exp.Result(None(), typedAttr), typedAttr)))
          case info => halt(s"Infeasible: $owner.$id => $info")
        }
      } else {
        th.typeMap.get(owner) match {
          case Some(info: lang.symbol.TypeInfo.Adt) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return Context.InvokeMethodInfo(mi.ast.isHelper, mi.ast.sig, mi.ast.contract,
                  extractResolvedInfo(mi.ast.attr), extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return Context.InvokeMethodInfo(T, mi.ast.sig, AST.MethodContract.Simple.empty,
                      extractResolvedInfo(mi.ast.attr), None())
                  case _ => halt("Infeasible")
                }
            }
          case Some(info: lang.symbol.TypeInfo.Sig) =>
            info.methods.get(id) match {
              case Some(mi) =>
                return Context.InvokeMethodInfo(mi.ast.isHelper, mi.ast.sig, mi.ast.contract,
                  extractResolvedInfo(mi.ast.attr), extractAssignExpOpt(mi))
              case _ =>
                info.specMethods.get(id) match {
                  case Some(mi) =>
                    return Context.InvokeMethodInfo(T, mi.ast.sig, AST.MethodContract.Simple.empty,
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
        val (s2, pf) = strictPureMethod(th, config, plugins, smt2, cache, s1, receiverTypeOpt, funType, mres.owner,
          mres.id, for (p <- info.sig.params) yield p.id, body, reporter, context.implicitCheckTitlePosOpt)
        val (s3, re) = s2.freshSym(retType, pos)
        var args: ISZ[State.Value] = for (q <- paramArgs) yield q._4
        receiverOpt match {
          case Some(receiver) => args = receiver +: args
          case _ =>
        }
        r = r :+ ((s3.addClaim(State.Claim.Let.ProofFunApply(re, pf, args)), re))
      }

      val invs: ISZ[Info.Inv] =
        if (info.isHelper || info.strictPureBodyOpt.nonEmpty) ISZ()
        else retrieveInvs(res.owner, res.isInObject)

      def compositional(s: State, typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed,
                        receiverOpt: Option[State.Value.Sym],
                        paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)],
                        oldVars: HashSMap[String, State.Value.Sym]): Unit = {
        if (context.compMethods.contains(res.owner :+ res.id)) {
          reporter.error(posOpt, kind, st"Cannot use ${(res.owner :+ res.id, ".")}'s contracts cyclicly".render)
          r = r :+ ((s(status = F), State.errorValue))
          return
        }

        var s1 = s
        for (q <- paramArgs) {
          val (l, _, arg, v) = q
          val argPosOpt = arg.posOpt
          val (s3, sym) = idIntro(arg.posOpt.get, s1, l.context, l.id, v.tipe, argPosOpt)
          val (s4, vSym) = value2Sym(s3, v, argPosOpt.get)
          s1 = s4.addClaim(State.Claim.Eq(sym, vSym))
        }

        val lComp: Logika = {
          val l = logikaMethod(th, config, res.owner, res.id, receiverOpt.map(t => t.tipe), info.sig.paramIdTypes,
            info.sig.returnType.typedOpt.get, receiverPosOpt, contract.reads, ISZ(), contract.modifies, ISZ(), ISZ(), ISZ(),
            plugins, Some((s"(${if (res.owner.isEmpty) "" else res.owner(res.owner.size - 1)}${if (res.isInObject) '.' else '#'}${res.id}) ", ident.posOpt.get)),
            this.context.compMethods + (res.owner :+ res.id)
          )
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
            val (id, (ctx, _, t)) = p
            val (s7, sym): (State, State.Value.Sym) = idIntro(pos, s1, ctx, id, t, None())
            localInMap = localInMap + id ~> sym
            s1 = s7
          }
          l(context = l.context(methodOpt = Some(mctx(objectVarInMap = objectVarInMap, fieldVarInMap = fieldVarInMap,
            localInMap = localInMap))))
        }

        val (receiverModified, modLocals) = contract.modifiedLocalVars(lComp.context.receiverLocalTypeOpt)

        def evalContractCase(logikaComp: Logika, callerReceiverOpt: Option[State.Value.Sym], assume: B, cs0: State,
                             labelOpt: Option[AST.Exp.LitString], requires: ISZ[AST.Exp],
                             ensures: ISZ[AST.Exp]): Context.ContractCaseResult = {

          def modVarsResult(ms0: State, mposOpt: Option[Position]): (State, State.Value.Sym) = {
            var ms1 = ms0
            val modObjectVars = contract.modifiedObjectVars
            val mpos = mposOpt.get
            ms1 = rewriteObjectVars(this, smt2, cache, rtCheck, ms1, modObjectVars, mpos, reporter)
            var oldIdMap = HashMap.empty[ISZ[String], State.Value.Sym]
            for (pair <- modLocals.entries) {
              val (info, (t, _)) = pair
              val (ls0, sym) = idIntro(pos, ms1, info.context, info.id, t, None())
              ms1 = ls0
              oldIdMap = oldIdMap + (info.context :+ info.id) ~> sym
            }
            ms1 = rewriteLocalVars(ms1, modLocals.keys, mposOpt, reporter)
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
            ms1 = rewriteLocalVars(ms1, rwLocals, modPosOpt, reporter)
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
            for (require <- requires if csr0.status) {
              val title: String =
                if (requires.size == 1) st"${label}re-condition of $resST".render
                else st"${label}re-condition#$i of $resST".render

              val (csr1, sym): (State, State.Value.Sym) =
                if (assume) {
                  val p = logikaComp.evalAssume(smt2, cache, F, title, csr0, AST.Util.substExp(require, typeSubstMap), posOpt, rep)
                  val size = p._1.claims.size
                  assert(p._1.claims(size - 1) == State.Claim.Prop(T, p._2))
                  (p._1(claims = ops.ISZOps(p._1.claims).slice(0, size - 1)), p._2)
                } else {
                  logikaComp.evalAssert(smt2, cache, F, title, csr0, AST.Util.substExp(require, typeSubstMap), posOpt, rep)
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
            for (ensure <- claims if cse3.status) {
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
          if (!cs2.status) {
            val (cs3, rsym) = cs2.freshSym(AST.Typed.b, pos)
            return Context.ContractCaseResult(F, cs3.addClaim(State.Claim.Let.And(rsym, requireSyms)),
              State.errorValue, State.Claim.Prop(T, rsym), rep.messages)
          }
          val (cs4, result) = modVarsResult(cs2, posOpt)
          val cs5 = evalEnsures(cs4, label, rep)
          if (!cs5.status) {
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
                s1 = rewriteLocal(s1, lcontext, "this", posOpt, reporter)
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
          case contract: AST.MethodContract.Simple if s1.status =>
            val ccr = evalContractCase(lComp, callerReceiverOpt, F, s1, None(), contract.requires, contract.ensures)
            reporter.reports(ccr.messages)
            r = r :+ ((ccr.state, ccr.retVal))
          case contract: AST.MethodContract.Cases if s1.status =>
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
                val implies: ISZ[State.Claim] = for (ccr <- okCcrs) yield State.Claim.Imply(ISZ(ccr.requiresClaim,
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
                    for (ccr <- okCcrs) yield State.Claim.Imply(ISZ(ccr.requiresClaim,
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
      }

      for (t <- stateSubstMapReceiverOpts) {
        var typeSubstMap = t._2
        val receiverOpt = t._3
        for (p <- evalArgs(split, smt2, cache, rtCheck, t._1, info.sig.params.size, eargs, reporter)) {
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
            TypeChecker.unifyFun(Logika.kind, th, posOpt, TypeChecker.TypeRelation.Subtype, invokeType, mType, reporter) match {
              case Some(sm) =>
                typeSubstMap = typeSubstMap ++ sm.entries
                val retType = info.res.tpeOpt.get.ret.subst(typeSubstMap)

                if (info.strictPureBodyOpt.nonEmpty) {
                  strictPure(s1, typeSubstMap, retType, receiverOpt, paramArgs)
                } else {
                  var s2 = s1
                  var oldVars = HashSMap.empty[String, State.Value.Sym]
                  if (ctx == context.methodName) {
                    for (paramArg <- paramArgs) {
                      val id = paramArg._1.id
                      val (s3, sym) = idIntro(pos, s2, ctx, paramArg._1.id, paramArg._2, None())
                      oldVars = oldVars + id ~> sym
                      s2 = s3
                    }
                    s2 = rewriteLocals(s2, ctx, oldVars.keys ++ (if (receiverOpt.isEmpty) ISZ[String]() else ISZ[String]("this")))._1
                  }

                  compositional(s2, typeSubstMap, retType, receiverOpt, paramArgs, oldVars)

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
        if (s0.status) {
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

    def evalIfExp(sp: Split.Type, ifExp: AST.Exp.If): ISZ[(State, State.Value)] = {
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
        if (s0.status) {
          val (s1, sym) = value2Sym(s0, cond, ifExp.cond.posOpt.get)
          val prop = State.Claim.Prop(T, sym)
          val negProp = State.Claim.Prop(F, sym)
          val thenBranch = smt2.sat(cache, T, config.logVc, config.logVcDirOpt,
            s"if-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims :+ prop, reporter)
          val elseBranch = smt2.sat(cache, T, config.logVc, config.logVcDirOpt,
            s"if-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims :+ negProp, reporter)
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
                  r = r :+ ((s5.addClaim(State.Claim.If(sym,
                    ISZ(State.Claim.Let.Def(re, tv)),
                    ISZ(State.Claim.Let.Def(re, ev)))), re))
                }
              }
            case (T, F) => r = r ++ evalExp(sp, smt2, cache, rtCheck, s1, ifExp.thenExp, reporter)
            case (F, T) => r = r ++ evalExp(sp, smt2, cache, rtCheck, s1, ifExp.elseExp, reporter)
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
      return ISZ((s1.addClaim(State.Claim.Let.Random(sym, pos)), sym))
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
        if (s0.status && ops.ISZOps(valueOpts).forall((vOpt: Option[State.Value]) => vOpt.nonEmpty)) {
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
          val s8ClaimOps = ops.ISZOps(s7.claims)
          r = r :+ ((s7(claims = s8ClaimOps.slice(0, s1.claims.size) ++ s8ClaimOps.slice(s1.claims.size + 1, s7.claims.size)), res))
        }
      }
      for (p <- evalArgs(split, smt2, cache, rtCheck, state, cond.args.size, Either.Left[ISZ[AST.Exp], ISZ[AST.NamedArg]](cond.args), reporter)) {
        val (s0, argOpts) = p
        if (!s0.status) {
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
        case _: AST.Exp.LitStepId => return ISZ((s0(status = F), State.errorValue))
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
        case e: AST.Exp.If => return evalIfExp(split, e)
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
              e.attr.typedOpt.get match {
                case t: AST.Typed.Fun if t.isPureFun => return evalApplyFun(e.posOpt.get, T, res.context, res.id, t, e.args)
                case _ =>
              }
            case _ =>
          }
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((s0(status = F), State.errorValue))
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
          return ISZ((s0(status = F), State.errorValue))
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
        case e: AST.Exp.At => return ISZ(evalAt(e))
        case e: AST.Exp.TypeCond => return evalTypeCond(e)
        case e: AST.Exp.Sym => return ISZ[(State, State.Value)]((state, State.Value.Sym(e.num, e.typedOpt.get, e.posOpt.get)))
        case _ =>
          reporter.warn(e.posOpt, kind, s"Not currently supported: $e")
          return ISZ((s0(status = F), State.errorValue))
      }
    }

    def checkSplits(): ISZ[(State, State.Value)] = {
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
        return svs.size == 1 || ops.ISZOps(svs).forall((p: (State, State.Value)) => !p._1.status || nextFresh == p._1.nextFresh)
      }
      assert(check())
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

  def evalAssumeH(reportQuery: B, smt2: Smt2, cache: Smt2.Cache, title: String, s0: State, sym: State.Value.Sym,
                  posOpt: Option[Position], reporter: Reporter): State = {
    val s1 = s0(claims = s0.claims :+ State.Claim.Prop(T, sym))
    if (config.sat && s1.status) {
      val pos = posOpt.get
      val sat = smt2.sat(cache, reportQuery, config.logVc, config.logVcDirOpt,
        s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s1.claims, reporter)
      return s1(status = sat)
    } else {
      return s1
    }
  }

  def evalAssume(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, title: String, s0: State, cond: AST.Exp, posOpt: Option[Position],
                 reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = singleStateValue(evalExp(Split.Disabled, smt2, cache, rtCheck, s0, cond, reporter))
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssumeH(T, smt2, cache, title, s2, sym, posOpt, reporter), sym)
  }

  def evalAssertH(reportQuery: B, smt2: Smt2, cache: Smt2.Cache, title: String, s0: State, sym: State.Value.Sym,
                  posOpt: Option[Position], reporter: Reporter): State = {
    if (s0.status) {
      val conclusion = State.Claim.Prop(T, sym)
      val pos = posOpt.get
      val r = smt2.valid(cache, reportQuery, config.logVc, config.logVcDirOpt,
        s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s0.claims, conclusion, reporter)
      r.kind match {
        case Smt2Query.Result.Kind.Unsat => return s0.addClaim(conclusion)
        case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}", reporter)
        case Smt2Query.Result.Kind.Unknown => error(posOpt, s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds", reporter)
        case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower} holds", reporter)
        case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower} holds", reporter)
      }
    }
    return s0(status = F)
  }

  def evalAssert(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, title: String, s0: State, cond: AST.Exp,
                 posOpt: Option[Position], reporter: Reporter): (State, State.Value.Sym) = {
    val (s1, v) = singleStateValue(evalExp(Split.Disabled, smt2, cache, rtCheck, s0, cond, reporter))
    if (!s1.status) {
      return value2Sym(s1, v, cond.posOpt.get)
    }
    val (s2, sym): (State, State.Value.Sym) = value2Sym(s1, v, cond.posOpt.get)
    return (evalAssertH(T, smt2, cache, title, s2, sym, posOpt, reporter), sym)
  }

  def evalAssignExp(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rOpt: Option[State.Value.Sym], rtCheck: B,
                    s0: State, ae: AST.AssignExp, reporter: Reporter): ISZ[State] = {
    ae match {
      case ae: AST.Stmt.Expr =>
        ae.exp match {
          case e: AST.Exp.Invoke =>
            var r = ISZ[State]()
            for (p <- evalExprInvoke(split, smt2, cache, rtCheck, s0, ae, e, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.status => r = r :+ s1.addClaim(State.Claim.Let.Def(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
          case _ =>
            var r = ISZ[State]()
            for (p <- evalExp(split, smt2, cache, rtCheck, s0, ae.exp, reporter)) {
              val (s1, v) = p
              rOpt match {
                case Some(re) if s1.status => r = r :+ s1.addClaim(State.Claim.Let.Def(re, v))
                case _ => r = r :+ s1
              }
            }
            return r
        }
      case ae: AST.Stmt.Block => return evalBlock(split, smt2, cache, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.If => return evalIf(split, smt2, cache, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Match => return evalMatch(split, smt2, cache, rOpt, rtCheck, s0, ae, reporter)
      case ae: AST.Stmt.Return => return evalStmt(split, smt2, cache, rtCheck, s0, ae, reporter)
    }
  }

  def evalAssignExpValue(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, t: AST.Typed, rtCheck: B, s0: State,
                         ae: AST.AssignExp, reporter: Reporter): ISZ[(State, State.Value)] = {
    ae match {
      case ae: AST.Stmt.Expr => return evalExp(split, smt2, cache, rtCheck, s0, ae.exp, reporter)
      case _ =>
        val (s1, sym) = s0.freshSym(t, ae.asStmt.posOpt.get)
        return for (s2 <- evalAssignExp(split, smt2, cache, Some(sym), rtCheck, s1, ae, reporter)) yield (s2, sym)
    }
  }

  def evalAssignLocalH(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: State.Value.Sym,
                       idPosOpt: Option[Position], reporter: Reporter): State = {
    val s1: State = if (decl) s0 else rewriteLocal(s0, lcontext, id, idPosOpt, reporter)
    val (s2, lhs) = idIntro(idPosOpt.get, s1, lcontext, id, rhs.tipe, idPosOpt)
    return s2.addClaim(State.Claim.Eq(lhs, rhs))
  }

  def evalAssignObjectVarH(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State, ids: ISZ[String], rhs: State.Value.Sym,
                           namePosOpt: Option[Position], reporter: Reporter): State = {
    val poss = StateTransformer(CurrentNamePossCollector(ids)).transformState(ISZ(), s0).ctx
    if (poss.isEmpty) {
      reporter.error(namePosOpt, Logika.kind, st"Missing Modifies clause for ${(ids, ".")}.".render)
      return s0(status = F)
    }
    val (s1, num) = s0.fresh
    val objectVars = HashMap.empty[ISZ[String], (ISZ[Position], Z)] + ids ~> ((poss, num))
    val rt = StateTransformer(CurrentNameRewriter(objectVars)).transformState(HashMap.empty, s1)
    val s2 = rt.resultOpt.get
    val pos = namePosOpt.get
    val (s3, lhs) = nameIntro(namePosOpt.get, s2, ids, rhs.tipe, namePosOpt)
    val s4 = s3.addClaim(State.Claim.Eq(lhs, rhs))
    val tipe = rhs.tipe
    val s8: State = if (AST.Util.isSeq(tipe)) {
      val (s5, size1) = s4.freshSym(AST.Typed.z, pos)
      val (s6, size2) = s5.freshSym(AST.Typed.z, pos)
      val (s7, cond) = s6.freshSym(AST.Typed.b, pos)
      val o1 = rt.ctx.get(ids).get
      s7.addClaims(ISZ(
        State.Claim.Let.FieldLookup(size1, o1, "size"),
        State.Claim.Let.FieldLookup(size2, rhs, "size"),
        State.Claim.Let.Binary(cond, size2, AST.Exp.BinaryOp.Eq, size1, AST.Typed.z),
        State.Claim.Prop(T, cond)
      ))
    } else {
      s4
    }
    val objectName = ops.ISZOps(ids).dropRight(1)
    if (notInContext(objectName, T)) {
      return Util.checkInvs(this, namePosOpt, F, "Invariant after an object field assignment", smt2, cache, rtCheck, s8,
        None(), None(), retrieveInvs(objectName, T), TypeChecker.emptySubstMap, reporter)
    } else {
      return s8
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

  def assignRec(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State, lhs: AST.Exp,
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
              case Some(mctx) if mctx.paramIds.contains(res.id) && !mctx.modLocalIds.contains(res.id) && res.context == mctx.name =>
                reporter.error(lhs.posOpt, kind, s"Missing Modifies clause for ${res.id}")
              case _ =>
            }
            return ISZ(evalAssignLocalH(F, s0, res.context, res.id, rhs, lhs.posOpt, reporter))
          case res: AST.ResolvedInfo.Var =>
            if (res.isInObject) {
              return ISZ(evalAssignObjectVarH(smt2, cache, rtCheck, s0, res.owner :+ res.id, rhs, lhs.posOpt, reporter))
            } else {
              return ISZ(evalAssignThisVarH(s0, lhs.id.value, rhs, lhs.posOpt.get, reporter))
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
          if (s3.status) {
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
          case res: AST.ResolvedInfo.Var if res.isInObject =>
            return ISZ(evalAssignObjectVarH(smt2, cache, rtCheck, s0, res.owner :+ res.id, rhs, lhs.posOpt, reporter))
          case _ =>
        }
        val receiver = lhs.receiverOpt.get
        val t = receiver.typedOpt.get.asInstanceOf[AST.Typed.Name]
        val receiverPos = receiver.posOpt.get
        var r = ISZ[State]()
        for (p <- evalExp(split, smt2, cache, T, s0, receiver, reporter)) {
          val (s1, o) = p
          if (s1.status) {
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
                rtCheck, s4, Some(t), Some(oSym), retrieveInvs(t.ids, T), sm, reporter)
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

  def evalPattern(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State, v: State.Value, pattern: AST.Pattern, reporter: Reporter): (State, State.Value, Bindings) = {
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

  def addBindings(smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State, lcontext: ISZ[String],
                  m: Bindings, reporter: Reporter): (State, ISZ[State.Value.Sym]) = {
    val ids = m.keys
    val s1 = rewriteLocals(s0, lcontext, ids)._1
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
        State.Claim.Let.Id(reX, lcontext, id, num, poss),
        State.Claim.Eq(reX, x),
        State.Claim.Eq(x, v)
      ))
    }
    return s1
  }

  def evalBranch(isMatch: B, split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, s0: State,
                 lcontext: ISZ[String], branches: ISZ[Branch], i: Z, rOpt: Option[State.Value.Sym],
                 reporter: Reporter): (Z, Option[(State.Claim, ISZ[ISZ[State.Claim]])]) = {
    val shouldSplit: B = split match {
      case Split.Default => config.splitAll || (isMatch && config.splitMatch)
      case Split.Enabled => T
      case Split.Disabled => F
    }
    var nextFresh = s0.nextFresh
    val s1 = s0
    val Branch(title, sym, body, m, bidMap) = branches(i)
    val cond = State.Claim.And(
      (for (j <- 0 until i) yield State.Claim.Prop(F, branches(j).sym).asInstanceOf[State.Claim]) :+
        State.Claim.Prop(T, sym))
    val pos = sym.pos
    val posOpt: Option[Position] = Some(pos)
    val s10 = s1.addClaim(cond)
    if (s10.status) {
      if (smt2.sat(cache, T, config.logVc, config.logVcDirOpt,
        s"$title at [${pos.beginLine}, ${pos.beginColumn}]", pos, s10.claims, reporter)) {
        val s11 = assumeBindings(s10, lcontext, m, bidMap)
        var claims = ISZ[ISZ[State.Claim]]()
        for (s12 <- evalBody(split, smt2, cache, rOpt, rtCheck, s11, body, posOpt, reporter)) {
          val s13 = rewriteLocals(s12, lcontext, m.keys)._1
          if (nextFresh < s13.nextFresh) {
            nextFresh = s13.nextFresh
          }
          if (s13.status) {
            claims = claims :+ s13.claims
          }
        }
        if (claims.nonEmpty) {
          return (nextFresh, Some((cond, claims)))
        }
      } else {
        if (isMatch && config.checkInfeasiblePatternMatch && !shouldSplit) {
          warn(posOpt, "Infeasible pattern matching case", reporter)
        }
      }
    }
    return (nextFresh, None())
  }

  def evalBranches(isMatch: B, split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B,
                   rOpt: Option[State.Value.Sym], lcontext: ISZ[String], s0: State, branches: ISZ[Branch],
                   reporter: Reporter): (State, LeafClaims) = {
    @pure def allReturns: B = {
      for (branch <- branches if !branch.body.allReturns) {
        return F
      }
      return T
    }
    var leafClaims: LeafClaims = ISZ()
    if (config.branchPar != Config.BranchPar.Disabled && config.branchParCores > 1) {
      val inputs: ISZ[Z] = branches.indices
      if (allReturns) {
        def computeBranch(i: Z): (Option[(State.Claim, ISZ[ISZ[State.Claim]])], Z, ISZ[Message]) = {
          val rep = reporter.empty
          val lsmt2 = smt2
          val (nextFresh, lcsOpt) = evalBranch(isMatch, split, lsmt2, cache, rtCheck, s0, lcontext, branches, i, rOpt, rep)
          return (lcsOpt, nextFresh, rep.messages)
        }
        val outputs = ops.ISZOps(inputs).mParMapCores(computeBranch _, config.branchParCores)
        for (i <- 0 until outputs.size) {
          reporter.reports(outputs(i)._3)
        }
        return (s0, leafClaims)
      } else if (!(branches.size == 2 && (branches(1).body.stmts.isEmpty || branches(0).body.stmts.isEmpty))) {
        def computeBranchSmt2(i: Z): (Option[(State.Claim, ISZ[ISZ[State.Claim]])], Z, Smt2, ISZ[Message]) = {
          val rep = reporter.empty
          val lsmt2 = smt2
          val (nextFresh, lcsOpt) = evalBranch(isMatch, split, lsmt2, cache, rtCheck, s0, lcontext, branches, i, rOpt, rep)
          return (lcsOpt, nextFresh, lsmt2, rep.messages)
        }
        var first: Z = -1
        val outputs = ops.MSZOps(inputs.toMS).mParMapCores(computeBranchSmt2 _, config.branchParCores)
        for (i <- 0 until outputs.size) {
          smt2.combineWith(outputs(i)._3)
          reporter.reports(outputs(i)._4)
        }
        for (i <- 0 until outputs.size if first < 0) {
          if (outputs(i)._1.nonEmpty) {
            first = i
          }
        }
        if (first < 0) {
          return (s0(status = F), leafClaims)
        }
        leafClaims = leafClaims :+ outputs(first)._1.get
        var nextFreshGap = outputs(first)._2 - s0.nextFresh
        for (i <- first + 1 until outputs.size) {
          outputs(i)._1 match {
            case Some((cond, claimss)) =>
              val gap = outputs(i)._2 - s0.nextFresh
              if (gap > 0) {
                val rw = Util.SymAddRewriter(s0.nextFresh, nextFreshGap, jescPlugins._4)
                val newCond = rw.transformStateClaim(cond).getOrElseEager(cond)
                var newClaimss = ISZ[ISZ[State.Claim]]()
                for (claims <- claimss) {
                  newClaimss = newClaimss :+ (for (claim <- claims) yield
                    rw.transformStateClaim(claim).getOrElseEager(claim))
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
      return ISZ(s0(status = F))
    } else if (leafClaims.size == 1) {
      val (cond, claimss) = leafClaims(0)
      val s1 = s0.addClaim(cond)
      return for (claims <- claimss) yield s1.addClaims(claims)
    } else if (shouldSplit) {
      return for (p <- leafClaims; cs <- p._2) yield s0(claims = (ops.ISZOps(cs).slice(0, s0.claims.size) :+ p._1) ++
        ops.ISZOps(cs).slice(s0.claims.size + 1, cs.size))
    }
    @pure def computeDiffIndices(): (ISZ[State.Claim], HashSet[Z]) = {
      var commonClaimPrefix = ISZ[State.Claim]()
      var diffIndices = HashSet.empty[Z]
      val css: ISZ[ISZ[State.Claim]] = for (p <- leafClaims; cs <- p._2) yield cs
      for (i <- 0 until s0.claims.size) {
        val c = css(0)(i)
        var ok = T
        var j = 1
        while (ok && j < css.size) {
          if (c != css(j)(i)) {
            ok = F
          }
          j = j + 1
        }
        if (ok) {
          commonClaimPrefix = commonClaimPrefix :+ c
        } else {
          commonClaimPrefix = commonClaimPrefix :+ trueClaim
          diffIndices = diffIndices + i
        }
      }
      return (commonClaimPrefix, diffIndices)
    }
    var r = ISZ[State]()
    val (commonClaimPrefix, diffIndices) = computeDiffIndices()
    var andClaims = ISZ[State.Claim]()
    for (p <- leafClaims) {
      var orClaims = ISZ[State.Claim]()
      for (cs <- p._2) {
        var claims = ISZ[State.Claim]()
        for (i <- 0 until s0.claims.size if diffIndices.contains(i)) {
          claims = claims :+ cs(i)
        }
        claims = claims ++ ops.ISZOps(cs).slice(s0.claims.size + 1, cs.size)
        orClaims = orClaims :+ bigAnd(claims)
      }
      if (orClaims.size == 1) {
//        andClaims = andClaims :+ State.Claim.Imply(ISZ(p._1, orClaims(0)))
        orClaims(0) match {
          case oc: State.Claim.And =>
            andClaims = andClaims ++ (for (c <- oc.claims) yield State.Claim.Imply(ISZ(p._1, c)).asInstanceOf[State.Claim])
          case oc => andClaims = andClaims :+ State.Claim.Imply(ISZ(p._1, oc))
        }
      } else {
        andClaims = andClaims :+ State.Claim.Imply(ISZ(p._1, State.Claim.Or(orClaims)))
      }
    }
    r = r :+ s0(claims = commonClaimPrefix ++ andClaims)
    return r
  }

  def evalMatch(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
                stmt: AST.Stmt.Match, reporter: Reporter): ISZ[State] = {

    def evalCasePattern(s1: State, lcontext: ISZ[String], c: AST.Case, v: State.Value): (State, State.Value.Sym, Bindings, HashMap[String, (Z, ISZ[Position])]) = {
      val (s2, pcond, m) = evalPattern(smt2, cache, rtCheck, s1, v, c.pattern, reporter)
      val (s3, bindings) = addBindings(smt2, cache, rtCheck, s2, lcontext, m, reporter)
      var conds = ISZ(pcond)
      val s6: State = c.condOpt match {
        case Some(cond) =>
          val (s4, ccond) = singleStateValue(evalExp(Split.Disabled, smt2, cache, rtCheck, s3, cond, reporter))
          if (bindings.nonEmpty) {
            val (s5, sym) = s4.freshSym(AST.Typed.b, cond.posOpt.get)
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
      val (s9, locals) = rewriteLocals(s8, lcontext, m.keys)
      return (s9, sym, m, HashMap.empty[String, (Z, ISZ[Position])] ++ (for (p <- locals.entries) yield (p._1._2, (p._2._2, p._2._1))))
    }

    var r = ISZ[State]()
    val lcontext: ISZ[String] = context.methodOpt match {
      case Some(mctx) => mctx.name
      case _ => ISZ()
    }

    for (p <- evalExp(split, smt2, cache, rtCheck, state, stmt.exp, reporter)) {
      val (s0, v) = p
      if (s0.status) {
        var branches = ISZ[Branch]()
        var s1 = s0
        for (c <- stmt.cases) {
          val (s2, sym, m, bidMap) = evalCasePattern(s1, lcontext, c, v)
          s1 = s2
          branches = branches :+ Branch("match case pattern", sym, c.body, m, bidMap)
        }
        val stmtPos = stmt.posOpt.get
        if (smt2.satResult(cache, T, config.logVc, config.logVcDirOpt,
          s"pattern match inexhaustiveness at [${stmtPos.beginLine}, ${stmtPos.beginColumn}]", stmtPos,
          s1.claims :+ State.Claim.And(for (p <- branches) yield State.Claim.Prop(F, p.sym)), reporter)._2.kind == Smt2Query.Result.Kind.Sat) {
          error(stmt.exp.posOpt, "Inexhaustive pattern match", reporter)
          r = r :+ s1(status = F)
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

  def evalBlock(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, s0: State,
                block: AST.Stmt.Block,
                reporter: Reporter): ISZ[State] = {
    return evalBody(split, smt2, cache, rOpt, rtCheck, s0, block.body, block.attr.posOpt, reporter)
  }

  def evalIf(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
             stmt: AST.Stmt.If, reporter: Reporter): ISZ[State] = {
    var branches = ISZ[Branch]()
    def evalConds(s0: State, ifStmt: AST.Stmt.If): State = {
      val (s1, cond) = singleStateValue(evalExp(Split.Disabled, smt2, cache, rtCheck, s0, ifStmt.cond, reporter))
      val pos = ifStmt.cond.posOpt.get
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

  def evalExprInvoke(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, stmt: AST.Stmt,
                     e: AST.Exp.Invoke, reporter: Reporter): ISZ[(State, State.Value)] = {
    def printH(): ISZ[(State, State.Value)] = {
      val pos = e.posOpt.get
      var ss = ISZ[State](state)
      var nextFresh: Z = -1
      for (arg <- e.args) {
        var newSS = ISZ[State]()
        for (s <- ss) {
          if (s.status) {
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
            val (s0, v) = evalAssert(smt2, cache, T, "Assertion", state, exp, exp.posOpt, reporter)
            return ISZ((s0, v))
          case AST.ResolvedInfo.BuiltIn.Kind.AssertMsg =>
            val exp = e.args(0)
            val (s0, v) = evalAssert(smt2, cache, T, "Assertion", state, exp, exp.posOpt, reporter)
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
            val s0 = state(status = F)
            return ISZ((s0, State.errorValue))
          case _ =>
            reporter.warn(e.posOpt, Logika.kind, s"Not currently supported: $stmt")
            return ISZ((state(status = F), State.errorValue))
        }
      case _ =>
        return evalExp(split, smt2, cache, rtCheck, state, e, reporter)
    }
  }

  def evalProofStep(smt2: Smt2,
                    cache: Smt2.Cache,
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
        for (plugin <- jescPlugins._1 if plugin.canHandle(this, step.just)) {
          val Plugin.Result(r, nextFresh, claims) =
            plugin.handle(this, smt2, cache, m, s0, step, reporter)
          return (s0(status = r, nextFresh = nextFresh).addClaims(claims),
            m + stepNo ~> StepProofContext.Regular(stepNo, step.claim, claims))
        }
        reporter.error(step.just.posOpt, Logika.kind, "Could not recognize justification form")
        return (s0(status = F), m)
      case step: AST.ProofAst.Step.Assume =>
        val (status, nextFresh, claims, claim) = evalRegularStepClaim(smt2, cache, s0, step.claim, step.id.posOpt, reporter)
        return (s0(status = status, nextFresh = nextFresh, claims = (s0.claims ++ claims) :+ claim),
          m + stepNo ~> StepProofContext.Regular(stepNo, step.claim, claims :+ claim))
      case step: AST.ProofAst.Step.SubProof =>
        for (sub <- step.steps if s0.status) {
          val p = evalProofStep(smt2, cache, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
        }
        s0 = stateMap._1(status = s0.status, nextFresh = s0.nextFresh)
        if (s0.status) {
          m = stateMap._2 + stepNo ~> StepProofContext.SubProof(stepNo,
            th.normalizeExp(step.steps(0).asInstanceOf[AST.ProofAst.Step.Assume].claim), extractClaims(step.steps))
          return (s0, m)
        } else {
          return (s0, stateMap._2)
        }
      case step: AST.ProofAst.Step.Assert =>
        var provenClaims = HashSet.empty[AST.Exp]
        for (sub <- step.steps if s0.status) {
          val p = evalProofStep(smt2, cache, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
          sub match {
            case sub: AST.ProofAst.Step.Regular if s0.status => provenClaims = provenClaims +
              th.normalizeExp(sub.claim)
            case _ =>
          }
        }
        s0 = stateMap._1(nextFresh = s0.nextFresh)
        if (!s0.status) {
          return (s0(status = F), stateMap._2)
        }
        if (!provenClaims.contains(th.normalizeExp(step.claim))) {
          reporter.error(step.claim.posOpt, Logika.kind, "The claim is not proven in the assertion's sub-proof")
          return (s0(status = F), stateMap._2)
        }
        val (status, nextFresh, claims, claim) = evalRegularStepClaim(smt2, cache, s0, step.claim, step.id.posOpt, reporter)
        return (s0(status = status, nextFresh = nextFresh, claims = (s0.claims ++ claims) :+ claim),
          m + stepNo ~> StepProofContext.Regular(stepNo, step.claim, claims :+ claim))
      case step: AST.ProofAst.Step.Let =>
        for (sub <- step.steps if s0.status) {
          val p = evalProofStep(smt2, cache, (s0, m), sub, reporter)
          s0 = p._1
          m  = p._2
        }
        s0 = stateMap._1(status = s0.status, nextFresh = s0.nextFresh)
        if (s0.status) {
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
      case step: AST.ProofAst.Step.StructInduction =>
        reporter.warn(step.id.posOpt, kind, s"Not currently supported: $step")
        return (s0(status = F), HashSMap.empty)
    }
  }

  def evalRegularStepClaim(smt2: Smt2, cache: Smt2.Cache, s0: State, claim: AST.Exp, posOpt: Option[Position],
                           reporter: Reporter): (B, Z, ISZ[State.Claim], State.Claim) = {
    val svs = evalExp(Logika.Split.Disabled, smt2, cache, T, s0, claim, reporter)
    for (sv <- svs) {
      val (s1, v) = sv
      val (s2, sym) = value2Sym(s1, v, posOpt.get)
      val vProp = State.Claim.Prop(T, sym)
      return (s2.status, s2.nextFresh, ops.ISZOps(s2.claims).slice(s0.claims.size, s2.claims.size), vProp)
    }
    return (F, s0.nextFresh, s0.claims, trueClaim)
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
      claim = AST.Exp.Binary(exp, AST.Exp.BinaryOp.CondAnd, claim, attr)
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

  def evalInv(posOpt: Option[Position], isAssume: B, title: String, smt2: Smt2, cache: Smt2.Cache, rtCheck: B,
              s0: State, invStmt: AST.Stmt.Inv, substMap: HashMap[String, AST.Typed], reporter: Reporter): State = {
    var s1 = s0
    var i = 0
    val isSingle = invStmt.claims.size == 1
    val id = invStmt.id.value
    for (c <- invStmt.claims if s1.status) {
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
        else evalAssert(smt2, cache, rtCheck, titl, s1, claim, pOpt, reporter)._1
      i = i + 1
    }
    return s1
  }

  def evalStmt(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, state: State, stmt: AST.Stmt, reporter: Reporter): ISZ[State] = {
    if (!state.status) {
      return ISZ(state)
    }
    val sPlugins = jescPlugins._3
    if (sPlugins.nonEmpty) {
      for (p <- sPlugins if p.canHandle(this, stmt)) {
        return p.handle(this, smt2, cache, state, stmt, reporter)
      }
    }

    def evalAssignLocal(decl: B, s0: State, lcontext: ISZ[String], id: String, rhs: AST.AssignExp, lhsType: AST.Typed,
                        idPosOpt: Option[Position]): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, cache, lhsType, rtCheck, s0, rhs, reporter)) {
        val (s1, init) = p
        if (s1.status) {
          val (s2, sym) = value2Sym(s1, init, rhs.asStmt.posOpt.get)
          r = r :+ evalAssignLocalH(decl, s2, lcontext, id, sym, idPosOpt, reporter)
        } else {
          r = r :+ s1
        }
      }
      return r
    }

    def evalAssign(s0: State, assignStmt: AST.Stmt.Assign): ISZ[State] = {
      var r = ISZ[State]()
      for (p <- evalAssignExpValue(split, smt2, cache, assignStmt.lhs.typedOpt.get, rtCheck, s0, assignStmt.rhs, reporter)) {
        val (s1, init) = p
        if (s1.status) {
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

      reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
      return ISZ(s0(status = F))
    }

    def evalWhile(s0: State, whileStmt: AST.Stmt.While): ISZ[State] = {
      var r = ISZ[State]()
      for (s0w <- checkExps(split, smt2, cache, F, "Loop invariant", " at the beginning of while-loop", s0,
        whileStmt.invariants, reporter)) {
        if (s0w.status) {
          val s1 = s0w
          val s0R: State = {
            val modObjectVars = whileStmt.contract.modifiedObjectVars
            var srw = rewriteObjectVars(this, smt2, cache, rtCheck, s0(nextFresh = s1.nextFresh),
              whileStmt.contract.modifiedObjectVars, whileStmt.posOpt.get, reporter)
            for (p <- modObjectVars.entries) {
              val (res, (tipe, pos)) = p
              val (srw1, sym) = srw.freshSym(tipe, pos)
              val srw2 = assumeValueInv(this, smt2, cache, rtCheck, srw1, sym, pos, reporter)
              srw = srw2.addClaim(State.Claim.Let.CurrentName(sym, res.owner :+ res.id, Some(pos)))
            }
            val (receiverModified, modLocalVars) = whileStmt.contract.modifiedLocalVars(context.receiverLocalTypeOpt)
            val receiverOpt: Option[State.Value.Sym] = if (receiverModified) {
              val (srw3, sym) = idIntro(whileStmt.posOpt.get, srw, context.methodName, "this",
                context.receiverLocalTypeOpt.get._2, None())
              srw = srw3
              Some(sym)
            } else {
              None()
            }
            srw = rewriteLocalVars(srw, modLocalVars.keys, whileStmt.posOpt, reporter)
            for (p <- modLocalVars.entries) {
              val (res, (tipe, pos)) = p
              val (srw4, sym) = idIntro(pos, srw, res.context, res.id, tipe, Some(pos))
              srw = assumeValueInv(this, smt2, cache, rtCheck, srw4, sym, pos, reporter)
            }
            if (receiverModified) {
              val srw6 = evalAssignReceiver(whileStmt.contract.modifies, this, this, smt2, cache, rtCheck, srw,
                Some(AST.Exp.This(AST.TypedAttr(whileStmt.posOpt, Some(receiverOpt.get.tipe)))), receiverOpt,
                HashMap.empty, reporter)
              val (srw7, sym) = idIntro(whileStmt.posOpt.get, srw6, context.methodName, "this",
                context.receiverLocalTypeOpt.get._2, None())
              srw = assumeValueInv(this, smt2, cache, rtCheck, srw7, sym, sym.pos, reporter)
            }
            srw
          }
          val s2 = State(T, s0R.claims ++ (for (i <- s0.claims.size until s1.claims.size) yield s1.claims(i)), s0R.nextFresh)
          for (p <- evalExp(split, smt2, cache, rtCheck, s2, whileStmt.cond, reporter)) {
            val (s3, v) = p
            if (s3.status) {
              val pos = whileStmt.cond.posOpt.get
              val (s4, cond) = value2Sym(s3, v, pos)
              val prop = State.Claim.Prop(T, cond)
              val thenClaims = s4.claims :+ prop
              val thenSat = smt2.sat(cache, T, config.logVc, config.logVcDirOpt,
                s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, thenClaims, reporter)
              var nextFresh: Z = s4.nextFresh
              if (thenSat) {
                for (s5 <- evalStmts(split, smt2, cache, None(), rtCheck, s4(claims = thenClaims), whileStmt.body.stmts, reporter)) {
                  if (s5.status) {
                    for (s6 <- checkExps(split, smt2, cache, F, "Loop invariant", " at the end of while-loop",
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
              val elseSat = smt2.sat(cache, T, config.logVc, config.logVcDirOpt,
                s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, elseClaims, reporter)
              r = r :+ State(status = elseSat, claims = elseClaims, nextFresh = nextFresh)
            } else {
              r = r :+ s3
            }
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
        for (s1 <- checkExps(sp, smt2, cache, F, "Loop invariant", " at the beginning of while-loop", current,
          whileStmt.invariants, reporter)) {
          if (s1.status) {
            for (p <- evalExp(sp, smt2, cache, rtCheck, s1, whileStmt.cond, reporter)) {
              val (s2, v) = p
              if (s2.status) {
                val pos = whileStmt.cond.posOpt.get
                val (s2w, cond) = value2Sym(s2, v, pos)
                val s3 = s2w
                val prop = State.Claim.Prop(T, cond)
                val thenClaims = s3.claims :+ prop
                val thenSat = smt2.sat(cache, T, config.logVc, config.logVcDirOpt,
                  s"while-true-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, thenClaims, reporter)
                for (s4 <- evalStmts(sp, smt2, cache, None(), rtCheck, s3(claims = thenClaims), whileStmt.body.stmts, reporter)) {
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
                    if (s6.status) {
                      val negProp = State.Claim.Prop(F, cond)
                      val elseClaims = s3.claims :+ negProp
                      val elseSat = smt2.sat(cache, T, config.logVc, config.logVcDirOpt,
                        s"while-false-branch at [${pos.beginLine}, ${pos.beginColumn}]", pos, elseClaims, reporter)
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
                    } else {
                      r = r :+ s6
                    }
                  }
                }
              } else {
                r = r :+ s2
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
      val mcontext = context.methodOpt.get
      val invs = retrieveInvs(mcontext.owner, mcontext.isInObject)
      val ss = Util.checkMethodPost(this, smt2, cache, reporter,  evalReturnH(), mcontext.posOpt, invs,
        mcontext.ensures, config.logPc, config.logRawPc, returnStmt.posOpt)
      return for (s <- ss) yield s(status = F)
    }

    def evalSpecBlock(sp: Split.Type, s0: State, block: AST.Stmt.SpecBlock): ISZ[State] = {
      return evalBlock(sp, smt2, cache, None(), rtCheck, s0, block.block, reporter)
    }

    def evalDeduceSteps(s0: State, deduceStmt: AST.Stmt.DeduceSteps): ISZ[State] = {
      var p = (s0, HashSMap.empty[AST.ProofAst.StepId, StepProofContext])
      var stepIds = ISZ[AST.ProofAst.StepId]()
      for (step <- deduceStmt.steps if p._1.status) {
        p = evalProofStep(smt2, cache, p, step, reporter)
        step match {
          case step: AST.ProofAst.Step.Regular if p._1.status => stepIds = stepIds :+ step.id
          case _ =>
        }
      }
      val m = p._2
      var s1 = s0(nextFresh = p._1.nextFresh)
      if (p._1.status) {
        for (stepId <- stepIds) {
          val spc = m.get(stepId).get.asInstanceOf[StepProofContext.Regular]
          s1 = s1.addClaims(spc.claims)
        }
      }
      return ISZ(s1)
    }

    def evalDeduceSequent(s0: State, deduceStmt: AST.Stmt.DeduceSequent): ISZ[State] = {
      @pure def premises(st: State, sequent: AST.Sequent): (State, HashSMap[AST.ProofAst.StepId, StepProofContext]) = {
        var r = HashSMap.empty[AST.ProofAst.StepId, StepProofContext]
        var id = AST.ProofAst.StepId.Num(-1, AST.Attr(None()))
        var st0 = st
        for (premise <- sequent.premises if st0.status) {
          val (status, nextFresh, claims, claim) = evalRegularStepClaim(smt2, cache, st0, premise, premise.posOpt, reporter)
          r = r + id ~> StepProofContext.Regular(id(attr = AST.Attr(premise.posOpt)), premise, claims :+ claim)
          id = id(no = id.no - 1)
          st0 = st0(status = status, nextFresh = nextFresh, claims = (st0.claims ++ claims) :+ claim)
        }
        return (st0, r)
      }
      var st0 = s0
      for (sequent <- deduceStmt.sequents if st0.status) {
        if (deduceStmt.justOpt.isEmpty && sequent.steps.isEmpty) {
          var i = 0
          for (premise <- sequent.premises if st0.status) {
            st0 = evalAssume(smt2, cache, rtCheck, s"Premise #$i", st0, premise, premise.posOpt, reporter)._1
            i = i + 1
          }
          if (st0.status) {
            st0 = evalAssert(smt2, cache, rtCheck, "Conclusion", st0, sequent.conclusion, sequent.conclusion.posOpt, reporter)._1
          }
        } else {
          var p = premises(st0, sequent)
          for (step <- sequent.steps if p._1.status) {
            p = evalProofStep(smt2, cache, p, step, reporter)
          }
          st0 = s0(status = p._1.status, nextFresh = p._1.nextFresh, claims = s0.claims)
          val provenClaims = HashSet ++ (for (spc <- p._2.values if spc.isInstanceOf[StepProofContext.Regular]) yield
            th.normalizeExp(spc.asInstanceOf[StepProofContext.Regular].exp))
          if (st0.status && !provenClaims.contains(th.normalizeExp(sequent.conclusion))) {
            reporter.error(sequent.conclusion.posOpt, Logika.kind, "The sequent's conclusion has not been proven")
            st0 = st0(status = F)
          }
        }
      }
      if (st0.status) {
        st0 = st0(claims = s0.claims)
        @strictpure def bin(e1: AST.Exp, op: String, opKind: AST.ResolvedInfo.BuiltIn.Kind.Type, e2: AST.Exp,
                            posOpt: Option[Position]): AST.Exp =
          AST.Exp.Binary(e1, op, e2, AST.ResolvedAttr(posOpt, Some(AST.ResolvedInfo.BuiltIn(opKind)), Some(AST.Typed.b)))
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
          val thisL = this
          st0 = thisL(config = config(sat = F)).evalAssume(smt2, cache, F, s"Sequent #$i", st0, seqClaim, seqClaim.posOpt, reporter)._1
          i = i + 1
        }
      }
      val s1: State = if (s0.claims.size != st0.claims.size) s0.addClaims(
        ops.ISZOps(st0.claims).slice(s0.claims.size, st0.claims.size)) else s0
      return ISZ(s1(status = st0.status, nextFresh = st0.nextFresh))
    }

    def evalVarPattern(varPattern: AST.Stmt.VarPattern): ISZ[State] = {
      var r = ISZ[State]()
      var nextFresh = state.nextFresh
      for (p <- evalAssignExpValue(split, smt2, cache, varPattern.pattern.typedOpt.get, rtCheck, state, varPattern.init,
        reporter)) {
        val (s1, init) = p
        val s9: State = if (s1.status) {
          val (s2, sym) = value2Sym(s1, init, varPattern.init.asStmt.posOpt.get)
          val (s3, cond, m) = evalPattern(smt2, cache, rtCheck, s2, sym, varPattern.pattern, reporter)
          var s4 = s3
          for (p <- m.entries) {
            val (id, (v, _, pos)) = p
            val (s5, rhs) = value2Sym(s4, v, pos)
            val s6 = Util.assumeValueInv(this, smt2, cache, rtCheck, s5, rhs, pos, reporter)
            val (s7, lhs) = idIntro(pos, s6, context.methodName, id, rhs.tipe, Some(pos))
            s4 = s7.addClaim(State.Claim.Eq(lhs, rhs))
          }
          val (s8, condSym) = value2Sym(s4, cond, varPattern.pattern.posOpt.get)
          evalAssertH(T, smt2, cache, "Variable Pattern Matching", s8, condSym, varPattern.pattern.posOpt, reporter)
        } else {
          s1
        }
        r = r :+ s9
        if (nextFresh < s9.nextFresh) {
          nextFresh = s9.nextFresh
        }

      }
      return for (s <- r) yield s(nextFresh = nextFresh)
    }

    def evalStmtH(): ISZ[State] = {
      stmt match {
        case stmt: AST.Stmt.Expr =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          stmt.exp match {
            case e: AST.Exp.Invoke =>
              return for (p <- evalExprInvoke(split, smt2, cache, rtCheck, state, stmt, e, reporter)) yield p._1
            case e =>
              return for (p <- evalExp(split, smt2, cache, rtCheck, state, e, reporter)) yield p._1
          }
        case stmt: AST.Stmt.Var if stmt.initOpt.nonEmpty =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          stmt.attr.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              return evalAssignLocal(T, state, res.context, res.id, stmt.initOpt.get, stmt.attr.typedOpt.get,
                stmt.id.attr.posOpt)
            case _ =>
              reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
              return ISZ(state(status = F))
          }
        case stmt: AST.Stmt.VarPattern =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalVarPattern(stmt)
        case stmt: AST.Stmt.Assign =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalAssign(state, stmt)
        case stmt: AST.Stmt.If =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalIf(split, smt2, cache, None(), rtCheck, state, stmt, reporter)
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
          if (stmt.modifies.isEmpty) {
            reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
            return ISZ(state(status = F))
          }
          return evalFor(state, stmt)
        case stmt: AST.Stmt.Return =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalReturn(state, stmt)
        case stmt: AST.Stmt.Block =>
          return evalBlock(split, smt2, cache, None(), rtCheck, state, stmt, reporter)
        case stmt: AST.Stmt.SpecBlock =>
          return evalSpecBlock(split, state, stmt)
        case stmt: AST.Stmt.Match =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalMatch(split, smt2, cache, None(), rtCheck, state, stmt, reporter)
        case stmt: AST.Stmt.Inv =>
          val s1 = evalInv(None(), F, "Invariant", smt2, cache, rtCheck, state, stmt, HashMap.empty, reporter)
          return ISZ(state(status = s1.status, nextFresh = s1.nextFresh))
        case stmt: AST.Stmt.DeduceSteps =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalDeduceSteps(state, stmt)
        case stmt: AST.Stmt.DeduceSequent if stmt.justOpt.isEmpty =>
          logPc(config.logPc, config.logRawPc, state, reporter, stmt.posOpt)
          return evalDeduceSequent(state, stmt)
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
        case _: AST.Stmt.Fact => return ISZ(state)
        case _: AST.Stmt.Theorem => return ISZ(state)
        case _ =>
          reporter.warn(stmt.posOpt, kind, s"Not currently supported: $stmt")
          return ISZ(state(status = F))
      }
    }

    def checkSplits(): ISZ[State] = {
      val ss = evalStmtH()
      def check(): B = {
        if (!(ss.size > 0)) {
          return F
        }
        var nextFresh: Z = -1
        for (s <- ss if nextFresh == -1) {
          nextFresh = s.nextFresh
        }
        if (nextFresh < 0) {
          return F
        }
        return ss.size == 1 || ops.ISZOps(ss).forall((s: State) => !s.status || nextFresh == s.nextFresh)
      }
      assert(check())
      return ss
    }

    return extension.Cancel.cancellable(checkSplits _)
  }

  def logPc(enabled: B, raw: B, state: State, reporter: Reporter, posOpt: Option[Position]): Unit = {
    reporter.state(jescPlugins._4, posOpt, context.methodName, th, state, config.atLinesFresh)
    if (enabled || raw) {
      val sts: ISZ[ST] =
        if (raw) {
          State.Claim.claimsRawSTs(state.claims)
        } else {
          val es = Util.claimsToExps(jescPlugins._4, posOpt.get, context.methodName, state.claims, th, config.atLinesFresh)
          for (e <- es) yield e.prettyST
        }
      if (sts.isEmpty) {
        reporter.info(posOpt, Logika.kind, "Path conditions = {}")
      } else {
        reporter.info(posOpt, Logika.kind,
          st"""Path conditions = {
              |  ${(sts, ",\n")}
              |}""".
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

  def checkExp(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, title: String, titleSuffix: String,
               s0: State, exp: AST.Exp, reporter: Reporter): ISZ[State] = {
    var r = ISZ[State]()
    for (p <- evalExp(split, smt2, cache, rtCheck, s0, exp, reporter)) {
      val (s1, v) = p
      val pos = exp.posOpt.get
      val (s2, sym) = value2Sym(s1, v, pos)
      val prop = State.Claim.Prop(T, sym)
      var ok = F
      if (s2.status) {
        val rvalid = smt2.valid(cache, T, config.logVc, config.logVcDirOpt,
          s"$title$titleSuffix at [${pos.beginLine}, ${pos.beginColumn}]", pos, s2.claims, prop, reporter)
        rvalid.kind match {
          case Smt2Query.Result.Kind.Unsat => ok = T
          case Smt2Query.Result.Kind.Sat => error(Some(pos), s"Invalid ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
          case Smt2Query.Result.Kind.Unknown => error(Some(pos), s"Could not deduce that the ${ops.StringOps(title).firstToLower} holds$titleSuffix", reporter)
          case Smt2Query.Result.Kind.Timeout => error(Some(pos), s"Timed out when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
          case Smt2Query.Result.Kind.Error => error(Some(pos), s"Error encountered when deducing that the ${ops.StringOps(title).firstToLower}$titleSuffix", reporter)
        }
      }
      if (ok) {
        r = r :+ s2.addClaim(prop)
      } else {
        r = r :+ s2(status = F)
      }
    }
    return r
  }

  def checkExps(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rtCheck: B, title: String, titleSuffix: String,
                s0: State, exps: ISZ[AST.Exp], reporter: Reporter): ISZ[State] = {
    var currents = ISZ(s0)
    var done = ISZ[State]()
    for (exp <- exps) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.status) {
          currents = currents ++ checkExp(split, smt2, cache, rtCheck, title, titleSuffix, current, exp, reporter)
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
    return State(sT.status && sF.status, prefixClaims :+
      State.Claim.If(cond, ops.ISZOps(sT.claims).drop(size + 1),
        ops.ISZOps(sF.claims).drop(size + 1)), nextFresh)
  }

  def evalStmts(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rOpt: Option[State.Value.Sym],
                rtCheck: B, state: State, stmts: ISZ[AST.Stmt], reporter: Reporter): ISZ[State] = {
    var currents = ISZ(state)
    var done = ISZ[State]()

    val size: Z = if (rOpt.nonEmpty) stmts.size - 1 else stmts.size
    for (i <- 0 until size) {
      val cs = currents
      currents = ISZ()
      for (current <- cs) {
        if (current.status) {
          currents = currents ++ evalStmt(split, smt2, cache, rtCheck, current, stmts(i), reporter)
        } else {
          done = done :+ current
        }
      }
    }

    if (rOpt.nonEmpty) {
      return (for (current <- currents;
                   s <- evalAssignExp(split, smt2, cache, rOpt, rtCheck, current, stmts(stmts.size - 1).asAssignExp, reporter))
      yield s) ++ done
    } else {
      return currents ++ done
    }
  }

  def evalBody(split: Split.Type, smt2: Smt2, cache: Smt2.Cache, rOpt: Option[State.Value.Sym], rtCheck: B, state: State,
               body: AST.Body, posOpt: Option[Position], reporter: Reporter): ISZ[State] = {
    val s0 = state
    var r = ISZ[State]()
    for (s1 <- evalStmts(split, smt2, cache, rOpt, rtCheck, s0, body.stmts, reporter)) {
      if (s1.status) {
        r = r :+ rewriteLocalVars(s1, body.undecls, posOpt, reporter)
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

  @pure def singleStateValue(ps: ISZ[(State, State.Value)]): (State, State.Value) = {
    assert(ps.size == 1)
    return ps(0)
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
