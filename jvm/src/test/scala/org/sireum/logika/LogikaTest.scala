/*
 Copyright (c) 2019, Robby, Kansas State University
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
    case Os.Kind.Unsupported => "unsupported"
  }

  val z3Exe: String = Os.env("SIREUM_HOME") match {
    case Some(p) if Os.kind != Os.Kind.Unsupported =>
      (Os.path(p) / "bin" / platform / "z3" / "bin" / (if (Os.isWin) "z3.exe" else "z3")).string
    case _ => "z3"
  }

  val config: Logika.Config =
    Logika.Config(
      defaultLoopBound = 10,
      loopBounds = HashMap.empty,
      smt2TimeoutInSeconds = 5,
      logPc = F,
      logRawPc = F,
      logVc = F)
}

import LogikaTest._

class LogikaTest extends TestSuite {

  val tests = Tests {

    "Passing" - {

      * - passingWorksheet(
        """import org.sireum._
          |var zOpt: Option[Z] = None[Z]()
          |if (B.random) {
          |  zOpt = Some(Z.random)
          |}
          |zOpt match {
          |  case Some(x) =>
          |  case _ =>
          |}
          |zOpt = Some(Z.random)
          |zOpt match {
          |  case Some(_) =>
          |}""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |ISZ(1, 2, 3) match {
          |  case ISZ(x, y, _*) => assert(x < y)
          |}
          |""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |(Z.random, Z.random) match {
          |  case (0, x) =>
          |  case (_, _) =>
          |}
          |(Z.random, Z.random) match {
          |  case (x, y) =>
          |}""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |@enum object Bool {
          |  'True
          |  'False
          |}
          |
          |var b = Bool.True
          |if (B.random) {
          |  b = Bool.False
          |}
          |
          |b match {
          |  case Bool.True =>
          |  case Bool.False =>
          |}
          |
          |b match {
          |  case Bool.True =>
          |  case _ =>
          |}
          |
          |b match {
          |  case _ =>
          |}
          |
          |b match {
          |  case Bool.False => b = Bool.True
          |  case _ =>
          |}
          |
          |assert(b == Bool.True)""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |var b = B.random
          |b match {
          |  case T =>
          |  case F =>
          |}
          |
          |b match {
          |  case T =>
          |  case _ =>
          |}
          |
          |b match {
          |  case _ =>
          |}
          |
          |b match {
          |  case F => b = T
          |  case _ =>
          |}
          |
          |assert(b)""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |val x = Z.random
          |val y = Z.random
          |val z = (x, y)
          |assert(z._1 == x)
          |assert(z._2 == y)
          |assert(z == ((x, y)))""".stripMargin)

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
          |ISZ(1, 2, 3) match {
          |  case ISZ(x, y, _*) if x < y =>
          |  case _ =>
          |}
          |""".stripMargin, "Impossible")

      * - failingWorksheet(
        """import org.sireum._
          |(Z.random, Z.random) match {
          |  case (0, x) =>
          |}""".stripMargin, "Inexhaustive")

      * - failingWorksheet(
        """import org.sireum._
          |val b = B.random
          |b match {
          |  case true =>
          |}""".stripMargin, "Inexhaustive")

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
    val reporter = Reporter.create
    val r = testWorksheet(worksheet, reporter, None())
    assert(r)
  }

  def failingWorksheet(worksheet: String, msg: String): Unit = {
    val reporter = Reporter.create
    val r = testWorksheet(worksheet, reporter, Some(msg))
    assert(!r)
  }

  def testWorksheet(input: String, reporter: Reporter, msgOpt: Option[String]): B = {
    Logika.checkWorksheet(None(), input, config,
      th => Z3(LogikaTest.z3Exe, th), reporter)
    if (reporter.hasIssue) {
      msgOpt match {
        case Some(msg) =>
          reporter(messages = ops.ISZOps(reporter.messages).filter((m: message.Message) => m.isInfo)).printMessages()
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
