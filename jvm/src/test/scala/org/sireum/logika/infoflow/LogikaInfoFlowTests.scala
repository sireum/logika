package org.sireum.logika.infoflow

import org.sireum._
import org.sireum.test._
import org.sireum.logika.LogikaTest._
import org.sireum.logika.{Logika, Smt2, Smt2Impl, Smt2Invoke}


object LogikaInfoFlowTests {
  val failSuffix: Predef.String = "-FAIL"
  val simplifiedPrefix: Predef.String = " (simplified)"
}

import LogikaInfoFlowTests._

class LogikaInfoFlowTests extends SireumRcSpec {

  def shouldIgnore(name: Predef.String): B = {
    false
  }

  val root = Os.path(".") / "logika" / "jvm" / "src" / "test" / "scala" / "org" / "sireum" / "logika" / "infoflow"

  def textResources: scala.collection.Map[scala.Vector[Predef.String], Predef.String] = {
    { // force marcro expansion
      val root = Os.path(".") / "logika" / "jvm" / "src" / "test" / "scala" / "org" / "sireum" / "logika" / "infoflow"
      val p = root / "LogikaInfoFlowTests.scala"
      p.writeOver(s"${p.read} ")
    }
    val m = $internal.RC.text(Vector("example")) { (p, f) => p.last.endsWith(".sc") }
    implicit val ordering: Ordering[Vector[Predef.String]] = m.ordering
    for ((k, v) <- m if !shouldIgnore(k.last);
         pair <- Seq((k, v), (k.dropRight(1) :+ s"${k.last}$simplifiedPrefix", v))) yield pair
  }

  val dontSplitPfq:B = F
  val splitAll:B = F
  val splitContract: B = F
  val splitIf: B = F
  val spiltMatch: B = F

  val logPc: B = F
  val logRawPc: B = F
  val logVc: B = T
  var logVcDirOpt: Option[String] = None()

  def check(path: scala.Vector[Predef.String], content: Predef.String): scala.Boolean = {
    Smt2Invoke.haltOnError = T
    val isSimplified = path.last.endsWith(simplifiedPrefix)
    val p = if (isSimplified) path.dropRight(1) :+ path.last.replace(simplifiedPrefix, "") else path
    val reporter = Logika.Reporter.create
    var c = config(simplifiedQuery = isSimplified)
    val f = Os.path(p.mkString(Os.fileSep.value))

    if(logVc) {
      val d = root / "example" / s"vcs_${(ops.StringOps(p.last).substring(0, p.last.length - 3))}" / path.last
      logVcDirOpt = Some(d.string)
      if (d.exists) {
        d.removeAll()
      }
    }

    c = c(dontSplitPfq = dontSplitPfq, splitAll = splitAll, splitContract = splitContract, splitIf = splitIf,
      logPc = logPc, logRawPc = logRawPc, logVc = logVc, logVcDirOpt = logVcDirOpt)

    Logika.checkScript(Some(f.string), content, c,
      th => Smt2Impl.create(c.smt2Configs, th, c.timeoutInMs, c.fpRoundingMode, c.charBitWidth,
        c.intBitWidth, c.useReal, c.simplifiedQuery, c.smt2Seq, reporter),
      Smt2.NoCache(), reporter, T, Logika.defaultPlugins, 0, ISZ(), ISZ())
    reporter.printMessages()
    val name = f.name.value
    if (name.contains(failSuffix)) {
      reporter.messages.elements.filter(m => !m.isInfo).exists(m => m.text.value.contains("Flow") && m.text.value.contains("violation"))
    } else {
      !reporter.hasIssue
    }
  }
}                                  