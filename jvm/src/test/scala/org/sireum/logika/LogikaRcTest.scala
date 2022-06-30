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
import org.sireum.test._
import LogikaTest._

class LogikaRcTest extends SireumRcSpec {

  val failPrefix: Predef.String = "zfail$"
  val failDemoSuffix: Predef.String = "-demo-fail.sc"

  lazy val hasAltErgo: B = Os.env("SIREUM_HOME") match {
    case Some(sireumHome) =>
      val m = Smt2Invoke.nameExePathMap(Os.path(sireumHome))
      val r = m.contains("alt-ergo")
      r
    case _ => F
  }

  def shouldIgnore(name: Predef.String): Boolean = name match {
    case "count.sc" | "count2.sc" if !hasAltErgo => true
    case "collection.sc" if Os.isMac && Os.env("GITHUB_WORKSPACE").nonEmpty => true
    case _ => false
  }

  def textResources: scala.collection.Map[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example")) { (p, f) => p.last.endsWith(".sc") && !p.last.startsWith("wip-") }
    for ((k, v) <- m if !shouldIgnore(k.last)) yield (k, v)
  }

  def check(path: scala.Vector[Predef.String], content: Predef.String): scala.Boolean = {
    val reporter = Logika.Reporter.create
    var c = config
    path(path.size - 1) match {
      case "collection.sc" | "strictpure.sc" => c = c(smt2Configs = for (c <- c.smt2Configs if c.name =!= "alt-ergo") yield c, timeoutInMs = 5000)
      case _ =>
    }
    //c = c(logVcDirOpt = Some((Os.home / "Temp" / path.last).string))
    val p = Os.path(path.mkString(Os.fileSep.value))
    Logika.checkScript(Some(p.string), content, c,
      th => Smt2Impl.create(c.smt2Configs, th, c.timeoutInMs, c.fpRoundingMode, c.charBitWidth,
        c.intBitWidth, c.useReal, c.simplifiedQuery, c.smt2Seq, reporter),
      Smt2.NoCache(), reporter, 0, T, Logika.defaultPlugins, 0, ISZ(), ISZ())
    reporter.printMessages()
    val name = p.name.value
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
