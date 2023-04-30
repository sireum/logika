/*
 Copyright (c) 2017-2023, Robby, Kansas State University
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
import org.sireum.test._
import LogikaTest._

object LogikaRcTest {

  val failPrefix: Predef.String = "zfail$"
  val failDemoSuffix: Predef.String = "-demo-fail.sc"
  val simplifiedSuffix: Predef.String = " (simplified)"

}

import LogikaRcTest._

class LogikaRcTest extends SireumRcSpec {

  def shouldIgnore(name: Predef.String, isSimplified: Boolean): Boolean = name match {
    case "collection.sc" => (Os.isMac || !isSimplified) && isInGithubAction
    case "opsem.sc" | "opsem-alt.sc" => Os.isMac && isInGithubAction
    case "conformance-swap.sc" => isSimplified
    case "strictpure.sc" => Os.isWin && isInGithubAction && !isSimplified
    case _ => false
  }

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, f) => p.last.endsWith(".sc") && !p.last.startsWith("wip-") }
    implicit val ordering: Ordering[Vector[Predef.String]] = m.ordering
    for ((k, v) <- m; pair <- {
      var r = Vector[(Vector[Predef.String], Predef.String)]()
      if (!shouldIgnore(k.last, F)) {
        r = r :+ (k, v)
      }
      if (!shouldIgnore(k.last, T)) {
        r = r :+ (k.dropRight(1) :+ s"${k.last}$simplifiedSuffix", v)
      }
      r
    }) yield pair
  }

  def check(path: scala.Vector[Predef.String], content: Predef.String): scala.Boolean = {
    def filterSmt2Config(c: Config, p: Smt2Config => B): Config =
      c(smt2Configs = for (sc <- c.smt2Configs if p(sc)) yield sc)
    Smt2Invoke.haltOnError = T
    val isSimplified = path.last.endsWith(simplifiedSuffix)
    val p = if (isSimplified) path.dropRight(1) :+ path.last.replace(simplifiedSuffix, "") else path
    val reporter = Logika.Reporter.create
    var c = config(simplifiedQuery = isSimplified)
    var line = 0
    p(p.size - 1) match {
      case "collection.sc" if isInGithubAction => c = filterSmt2Config(c, (c: Smt2Config) => c.isSat | c.name.value == "cvc5")(timeoutInMs = c.timeoutInMs * 3)
      case "loop-unroll.sc"  => c = c(interp = T)
      case "opsem.sc" => c = filterSmt2Config(c, !_.name.value.startsWith("alt-ergo"))(timeoutInMs = if (isInGithubAction) c.timeoutInMs * 2 else c.timeoutInMs)
      case "opsem-alt.sc"  => c = filterSmt2Config(c, (c: Smt2Config) => c.isSat | c.name.value == "cvc5")
      case "interprocedural-1.sc"  => c = c(interp = T); line = 10
      case "interprocedural-2.sc"  => c = c(interp = T); line = 10
      case "interprocedural-contract.sc"  => c = c(interp = T, interpContracts = T); line = 14
      case "interprocedural-instance.sc"  => c = c(interp = T); line = 9
      case _ =>
    }
    //c = c(logVcDirOpt = Some((Os.home / "Temp" / path.last.replace("(", "").replace(")", "").replace(' ', '.')).string))
    val f = Os.path(p.mkString(Os.fileSep.value))
    Logika.checkScript(Some(f.string), content, c,
      th => Smt2Impl.create(c, ISZ(), th, reporter),
      NoTransitionSmt2Cache.create, reporter, T, Logika.defaultPlugins, line, ISZ(), ISZ())
    reporter.printMessages()
    val name = f.name.value
    if (name.startsWith(failPrefix)) {
      val j = name.indexOf('$', failPrefix.length)
      val key = name.substring(failPrefix.length, j)
      reporter.messages.elements.filter(m => !m.isInfo).exists(m => m.text.value.contains(key))
    } else if (name.endsWith(failDemoSuffix)) {
      reporter.hasIssue
    } else {
      !reporter.hasIssue
    }
  }

}
