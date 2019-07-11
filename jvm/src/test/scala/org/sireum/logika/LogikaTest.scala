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
import org.sireum.lang.{FrontEnd, LibraryTypeCheckingTest}
import org.sireum.lang.ast.TopUnit
import org.sireum.lang.parser.Parser
import org.sireum.lang.tipe.{PostTipeAttrChecker, TypeChecker}
import org.sireum.message.Reporter
import org.sireum.test._

class LogikaTest extends TestSuite {

  lazy val typeChecker: TypeChecker = LibraryTypeCheckingTest.tc

  val tqs: String = "\"\"\""

  val config: Logika.Config =
    Logika.Config(
      defaultLoopBound = 10,
      loopBounds = HashMap.empty,
      smt2TimeoutInSeconds = 2)

  val tests = Tests {

    "Passing" - {

      * - passingWorksheet(
        s"""import org.sireum._
           |val s1 = ISZ(1, 2, 3)
           |assert(T)
           |assert(s1(0) == 1)
           |assert(s1(1) == 2)
           |assert(s1(2) == 3)
           |assert(s1.size == 3)
           |val s2 = ISZ(Some(3))
           |assert(s2(0).value == 3)""".stripMargin)

      * - passingWorksheet(
        s"""import org.sireum._
           |val x = Z.random
           |val xOpt = Some(Some(x))
           |assert(xOpt.value.value == x)""".stripMargin)

      * - passingWorksheet(
        s"""import org.sireum._
           |val m = Z.random
           |val n = 3
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
           |assert(r == m * n)""".stripMargin)

      * - passingWorksheet(
        s"""import org.sireum._
           |val m = Z.random
           |val n = Z.random
           |assume(n >= 0)
           |var i = 0
           |var r = 0
           |while (i < n) {
           |  Invariant(
           |    Modifies(i, r),
           |    0 <= i,
           |    i <= n,
           |    r == m * i
           |  )
           |  r = r + m
           |  i = i + 1
           |}
           |assert(r == m * n)""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |val x = Z.random
          |val y = Z.random
          |var max = x
          |if (x < y) {
          |  max = y
          |}
          |assert(max >= x & max >= y & (max == x | max == y))""".stripMargin)

      * - passingWorksheet(
        """import org.sireum._
          |var x = Z.random
          |if (x < 0) {
          |  x = -x
          |}
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
    Parser(input).parseTopUnit[TopUnit.Program](allowSireum = F, isWorksheet = T, isDiet = F, None(), reporter) match {
      case Some(program) if !reporter.hasIssue =>
        val p = FrontEnd.checkWorksheet(Some(typeChecker.typeHierarchy), program, reporter)
        if (!reporter.hasIssue) {
          PostTipeAttrChecker.checkProgram(p._2, reporter)
        }
        if (!reporter.hasIssue) {
          try {
            val th = p._1
            val logika = Logika(config, Z3(th, config.smt2TimeoutInSeconds))
            logika.evalStmts(State.create, p._2.body.stmts, reporter)
          } catch {
            case t: Throwable =>
              t.printStackTrace()
              return false
          }
        }
      case _ =>
    }
    if (reporter.hasIssue) {
      msgOpt match {
        case Some(msg) =>
          return reporter.messages.elements.exists(_.text.value.contains(msg))
        case _ =>
          reporter.printMessages()
          return false
      }
    }
    assert(msgOpt.isEmpty)
    !reporter.hasIssue
  }

}
