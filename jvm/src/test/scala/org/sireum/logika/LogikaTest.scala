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
import org.sireum.message.Reporter
import org.sireum.test._

object LogikaTest {

  val sireumHome: Os.Path = Os.path(Os.env("SIREUM_HOME").get).canon

  val rlimit: Z = {
    var r: Z = 1000000
    Os.env("SIREUM_LOGIKA_RLIMIT") match {
      case Some(n) => r = Z(n).getOrElse(r)
      case _ =>
    }
    r
  }

  val timeoutInMs: Z = {
    var r: Z = 2000
    Os.env("SIREUM_LOGIKA_TIMEOUT") match {
      case Some(n) => r = Z(n).getOrElse(r)
      case _ =>
    }
    r
  }

  val config: Config =
    Config(
      smt2Configs =
        Smt2.parseConfigs(Smt2Invoke.nameExePathMap(sireumHome), F, s"${Smt2.cvc4DefaultValidOpts}; ${Smt2.z3DefaultValidOpts}; ${Smt2.cvc5DefaultValidOpts}; ${Smt2.altErgoDefaultValidOpts}").left ++
          Smt2.parseConfigs(Smt2Invoke.nameExePathMap(sireumHome), T, Smt2.defaultSatOpts).left,
      parCores = Runtime.getRuntime.availableProcessors,
      sat = T,
      rlimit = rlimit,
      timeoutInMs = timeoutInMs,
      charBitWidth = 32,
      intBitWidth = 0,
      useReal = F,
      logPc = F,
      logRawPc = F,
      logVc = F,
      logVcDirOpt = None(),
      //logVcDirOpt = Some((Os.home / "Temp" / "worksheet").string),
      dontSplitPfq = F,
      splitAll = F,
      splitContract = F,
      splitIf = F,
      splitMatch = F,
      simplifiedQuery = F,
      checkInfeasiblePatternMatch = T,
      fpRoundingMode = "RNE",
      smt2Caching = F,
      smt2Seq = F,
      branchPar = Config.BranchPar.All,
      atLinesFresh = T,
      interp = F,
      loopBound = 3,
      callBound= 3,
      interpContracts = F,
      elideEncoding = F,
      rawInscription = F,
      strictPureMode = Config.StrictPureMode.Default,
      transitionCache = F,
      patternExhaustive = T,
      pureFun = F,
      detailedInfo = F,
      satTimeout = F,
      isAuto = T,
      background = Config.BackgroundMode.Type,
      atRewrite = T,
      searchPc = T,
      rwTrace = T,
      rwMax = 100,
      rwPar = T,
      rwEvalTrace = T
    )

  lazy val isInGithubAction: B = Os.env("GITHUB_ACTION").nonEmpty
}

import LogikaTest._

class LogikaTest extends TestSuite {

  val tests = Tests {

    "Passing" - {

      * - passingWorksheet(
        """// #Sireum #Logika
          |import org.sireum._
          |
          |def foo(a: ZS): Unit = {
          |  Contract(Modifies(a))
          |}
          |
          |def baz(): Unit = {
          |  val s = ZS(0)
          |  foo(s)
          |}""".stripMargin)

      * - passingWorksheet(
        """// #Sireum #Logika
          |import org.sireum._
          |
          |var x: Z = 1
          |
          |def foo(): Unit = {
          |  Contract(Modifies(x))
          |}
          |
          |def baz(): Unit = {
          |  Contract(Modifies(x))
          |  foo()
          |  foo()
          |}""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |val v = Z.random
          |val zs = ZS.create(3, v)
          |assert(zs.size == 3 & zs(0) == v & zs(1) == v & zs(2) == v)""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |def foo(): Unit = {
          |  Contract(
          |    Ensures(seqIndexValidSize[Z8](100))
          |  )
          |}""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |var x = randomInt()
          |x = x * x
          |assert(x >= 0)""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |var x = Z.random
          |x = x * x
          |assert(x >= 0)""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |assert(T)""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |assume(T)""".stripMargin)

    }

    "Failing" - {

      * - failingWorksheet(
        """import org.sireum._
          |val b = B.random
          |b match {
          |  case true => assert(false)
          |  case false =>
          |}""".stripMargin, "Cannot deduce")

    }

  }

  def passingWorksheet(worksheet: String): Unit = {
    val reporter = logika.ReporterImpl.create(config.logPc, config.logRawPc, config.logVc, config.detailedInfo)
    val r = testWorksheet(worksheet, reporter, None())
    assert(r)
  }

  def failingWorksheet(worksheet: String, msg: String): Unit = {
    val reporter = logika.ReporterImpl.create(config.logPc, config.logRawPc, config.logVc, config.detailedInfo)
    val r = testWorksheet(worksheet, reporter, Some(msg))
    assert(!r)
  }

  def testWorksheet(input: String, reporter: Logika.Reporter, msgOpt: Option[String]): B = {
    Smt2Invoke.haltOnError = T
    val nameExePathMap = Smt2Invoke.nameExePathMap(sireumHome)
    Logika.checkScript(None(), input, config, nameExePathMap, Os.numOfProcessors, th => Smt2Impl.create(config, ISZ(),
      th, reporter), NoTransitionSmt2Cache.create, reporter, T, Logika.defaultPlugins, 0, ISZ(), ISZ())
    if (reporter.hasIssue) {
      msgOpt match {
        case Some(msg) =>
          val r = logika.ReporterImpl.create(config.logPc, config.logRawPc, config.logVc, config.detailedInfo)
          r.reports(ops.ISZOps(reporter.messages).filter((m: message.Message) => m.isInfo))
          r.printMessages()
          return reporter.messages.elements.exists(_.text.value.contains(msg))
        case _ =>
          reporter.printMessages()
          return false
      }
    }
    assert(msgOpt.isEmpty)
    reporter.printMessages()
    !reporter.hasIssue
  }

}
