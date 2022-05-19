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

  @pure def nameExePathMap(sireumHome: Os.Path): HashMap[String, String] = {
    val platform: String = Os.kind match {
      case Os.Kind.Mac => "mac"
      case Os.Kind.Linux => "linux"
      case Os.Kind.Win => "win"
      case _ => halt("Unsupported platform")
    }
    return HashMap.empty[String, String] ++ ISZ[(String, String)](
      "cvc4" ~> (sireumHome / "bin" / platform / "cvc").string,
      "cvc5" ~> (sireumHome / "bin" / platform / "cvc5").string,
      "z3" ~> (sireumHome / "bin" / platform / "z3" / "bin" / "z3").string,
    )
  }

  @pure def queryDefault(sireumHome: Os.Path,
                         cache: Smt2.Cache,
                         isSat: B,
                         smt2Seq: B,
                         queryString: String,
                         timeoutInMs: Z,
                         rlimit: Z): Smt2Query.Result = {
    val smt2Configs: ISZ[Smt2Config] =
      if (isSat) Smt2.parseConfigs(nameExePathMap(sireumHome), T, Smt2.defaultSatOpts, timeoutInMs, rlimit).left
      else Smt2.parseConfigs(nameExePathMap(sireumHome), F, Smt2.defaultValidOpts, timeoutInMs, rlimit).left
    return query(smt2Configs, cache, isSat, smt2Seq, queryString, timeoutInMs)
  }

  @pure def query(smt2Configs: ISZ[Smt2Config],
                  cache: Smt2.Cache,
                  isSat: B,
                  smt2Seq: B,
                  queryString: String,
                  timeoutInMs: Z): Smt2Query.Result = {
    val configs: ISZ[Smt2Config] = for (smt2Config <- smt2Configs if isSat == smt2Config.isSat) yield smt2Config
    val smt2Args: ISZ[String] =
      for (smt2Config <- configs if isSat == smt2Config.isSat; arg <- smt2Config.name +: smt2Config.opts) yield arg
    cache.get(isSat, queryString, smt2Args) match {
      case Some(r) => return r
      case _ =>
    }
    val start = extension.Time.currentMillis
    val fs: ISZ[() => Option[Smt2Query.Result] @pure] = for (config <- configs) yield () => {
      val args = config.opts
      var proc = Os.proc(config.exe +: args).input(queryString).redirectErr
      proc = proc.timeout(timeoutInMs * Os.numOfProcessors * 2)
      val startTime = extension.Time.currentMillis
      val pr = proc.run()
      val pout: String = pr.out
      val isTimeout: B = timeoutCodes.contains(pr.exitCode)
      val rOpt: Option[Smt2Query.Result] = if (pout.size == 0 && pr.exitCode != 0 && !isTimeout) {
        halt(
          st"""Error encountered when running ${config.exe} query:
              |; Result: Error
              |; Solver: ${config.exe}
              |; Arguments: ${(config.opts, " ")}
              |$queryString
              |
              |${config.exe} output (exit code ${pr.exitCode}):
              |${pr.out}""".render)
      } else {
        val duration = extension.Time.currentMillis - startTime
        val out = ops.StringOps(pout).split((c: C) => c.isWhitespace)
        val firstLine: String = if (isTimeout) "timeout" else out(0)
        firstLine match {
          case string"sat" => Some(Smt2Query.Result(Smt2Query.Result.Kind.Sat, config.name, queryString,
            st"""; Result: ${if (isSat) "Sat" else "Invalid"}
                |; Solver: ${config.exe}
                |; Arguments: ${(args, " ")}""".render, pout, duration, F))
          case string"unsat" => Some(Smt2Query.Result(Smt2Query.Result.Kind.Unsat, config.name, queryString,
            st"""; Result: ${if (isSat) "Unsat" else "Valid"}
                |; Solver: ${config.exe}
                |; Arguments: ${(args, " ")}""".render, pout, duration, F))
          case string"timeout" => None()
          case string"unknown" => None()
        }
      }
      rOpt
    }
    val r: Smt2Query.Result = ops.ISZOpsUtil.invokeAny(fs, () =>
      Smt2Query.Result(Smt2Query.Result.Kind.Unknown, "all", queryString,
        st"""; Result: Don't Know or Timeout
            |; Solver and arguments:
            |${(for (config <- configs) yield st"; * ${config.exe} ${(config.opts, " ")}", "\n")}""".render,
        "", extension.Time.currentMillis - start, F),
      smt2Seq || fs.size == 1)
    cache.set(isSat, queryString, smt2Args, r(cached = T, info = ops.StringOps(r.info).replaceAllLiterally("Result:", "Result (cached):")))
    return r
  }

}
