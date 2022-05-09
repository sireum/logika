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

object Smt2Invoke {

  val timeoutCodes: Set[Z] = Set.empty[Z] ++ ISZ(-101, -100, 1, 3, 6, 132)

  def query(smt2Configs: Smt2Configs,
            cache: Smt2.Cache,
            isSat: B,
            smt2Seq: B,
            query: String,
            timeoutInMs: Z): Smt2Query.Result = {

    def err(config: Smt2Config, out: String, exitCode: Z): Unit = {
      halt(
        st"""Error encountered when running ${config.exe} query:
            |$query
            |
            |${config.exe} output (exit code $exitCode):
            |$out""".render)
    }

    val fs: ISZ[() => Option[Smt2Query.Result] @pure] = for (config <- smt2Configs.configs) yield () => {
      //println(s"$exe Query:")
      //println(query)
      val args = config.args(isSat, timeoutInMs)
      var proc = Os.proc(config.exe +: args).input(query).redirectErr
      proc = proc.timeout(timeoutInMs * 2)
      val startTime = extension.Time.currentMillis
      val pr = proc.run()
      val pout: String = pr.out
      val isTimeout: B = timeoutCodes.contains(pr.exitCode)
      if (pout.size == 0 && pr.exitCode != 0 && !isTimeout) {
        err(config, pout, pr.exitCode)
      }
      val duration = extension.Time.currentMillis - startTime
      val out = ops.StringOps(pout).split((c: C) => c.isWhitespace)
      val firstLine: String = if (isTimeout) "timeout" else out(0)
      val r: Smt2Query.Result = firstLine match {
        case string"sat" => Smt2Query.Result(Smt2Query.Result.Kind.Sat, config.name, query,
          st"""; Result: ${if (isSat) "Sat" else "Invalid"}
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case string"unsat" => Smt2Query.Result(Smt2Query.Result.Kind.Unsat, config.name, query,
          st"""; Result: ${if (isSat) "Unsat" else "Valid"}
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case string"timeout" => Smt2Query.Result(Smt2Query.Result.Kind.Timeout, config.name, query,
          st"""; Result: Timeout
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case string"unknown" => Smt2Query.Result(Smt2Query.Result.Kind.Unknown, config.name, query,
          st"""; Result: Don't Know
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
        case _ => Smt2Query.Result(Smt2Query.Result.Kind.Error, config.name, query,
          st"""; Result: Error
              |; Solver: ${config.exe}
              |; Arguments: ${(args, " ")}""".render, pout, duration, F)
      }
      //println(s"$exe Result (${r.kind}):")
      //println(r.output)
      if (r.kind == Smt2Query.Result.Kind.Error) {
        err(config, pout, pr.exitCode)
      }
      r.kind match {
        case Smt2Query.Result.Kind.Sat => Some(r)
        case Smt2Query.Result.Kind.Unsat => Some(r)
        case Smt2Query.Result.Kind.Unknown => None()
        case Smt2Query.Result.Kind.Timeout => None()
        case Smt2Query.Result.Kind.Error => Some(r)
      }
    }
    val start = extension.Time.currentMillis
    val r: Smt2Query.Result = ops.ISZOpsUtil.invokeAny(fs, () =>
      Smt2Query.Result(Smt2Query.Result.Kind.Unknown, "all", query,
        st"""; Result: Don't Know or Timeout
            |; Solver and arguments:
            |${(for (config <- smt2Configs.configs) yield st"; * ${config.exe} ${config.args(isSat, timeoutInMs)}", "\n")}""".render,
        "", extension.Time.currentMillis - start, F),
      smt2Seq || fs.size == 1)
    val args: ISZ[String] = if (isSat) smt2Configs.satArgs(timeoutInMs) else smt2Configs.validArgs(timeoutInMs)
    cache.get(isSat, query, args) match {
      case Some(r) => return r
      case _ =>
    }
    cache.set(isSat, query, args, r(cached = T, info = ops.StringOps(r.info).replaceAllLiterally("Result:", "Result (cached):")))
    return r
  }

}
