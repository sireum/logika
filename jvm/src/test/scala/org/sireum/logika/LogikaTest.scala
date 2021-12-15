/*
 Copyright (c) 2017-2021, Robby, Kansas State University
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
  val platform: String = Os.kind match {
    case Os.Kind.Win => "win"
    case Os.Kind.Linux => "linux"
    case Os.Kind.Mac => "mac"
    case _ => "unsupported"
  }

  val z3Exe: String = Os.env("SIREUM_HOME") match {
    case Some(p) if Os.kind != Os.Kind.Unsupported =>
      (Os.path(p) / "bin" / platform / "z3" / "bin" / (if (Os.isWin) "z3.exe" else "z3")).canon.string
    case _ => "z3"
  }

  val cvcExe: String = Os.env("SIREUM_HOME") match {
    case Some(p) if Os.kind != Os.Kind.Unsupported =>
      (Os.path(p) / "bin" / platform / (if (Os.isWin) "cvc.exe" else "cvc")).canon.string
    case _ => "cvc5"
  }

  val timeoutInMs: Z = 2000

  val config: Config =
    Config(
      smt2Configs = ISZ(CvcConfig(cvcExe, ISZ("--full-saturate-quant"), ISZ()), Z3Config(z3Exe, ISZ(), ISZ())),
      sat = T,
      timeoutInMs = timeoutInMs,
      defaultLoopBound = 10,
      loopBounds = HashMap.empty,
      unroll = T,
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
      cvcRLimit = 1000000,
      fpRoundingMode = "RNE",
      caching = F
    )
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

      * - failingWorksheet(
        s"""import org.sireum._
           |val m = Z.random
           |val n = 11
           |var i = 0
           |var r = 0
           |while (i < n) { // loop unrolling (no modify clause)
           |  Invariant(
           |    0 <= i,
           |    i <= n,
           |    r == m * i
           |  )
           |  r = r + m
           |  i = i + 1
           |}
           |assert(r == m * n)""".stripMargin, "loop unrolling capped")

    }

  }

  def passingWorksheet(worksheet: String): Unit = {
    val reporter = Logika.Reporter.create
    val r = testWorksheet(worksheet, reporter, None())
    assert(r)
  }

  def failingWorksheet(worksheet: String, msg: String): Unit = {
    val reporter = Logika.Reporter.create
    val r = testWorksheet(worksheet, reporter, Some(msg))
    assert(!r)
  }

  def testWorksheet(input: String, reporter: Logika.Reporter, msgOpt: Option[String]): B = {
    Logika.checkScript(None(), input, config,
      th => Smt2Impl.create(config.smt2Configs, th, config.timeoutInMs, config.cvcRLimit, config.fpRoundingMode,
        config.charBitWidth, config.intBitWidth, config.useReal, config.simplifiedQuery, reporter),
      Smt2.NoCache(), reporter, 1, T, Logika.defaultPlugins, 0, ISZ(), ISZ())
    if (reporter.hasIssue) {
      msgOpt match {
        case Some(msg) =>
          val r = Logika.Reporter.create
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
