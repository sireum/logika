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

  val timeoutCodes: Set[Z] = Set.empty[Z] ++ ISZ(-101, -100, 3, 6, 132, 134, 142)

  var haltOnError: B = F

  @pure def nameExePathMap(sireumHome: Os.Path): HashMap[String, String] = {
    val platform: String = Os.kind match {
      case Os.Kind.Mac => "mac"
      case Os.Kind.Linux => "linux"
      case Os.Kind.Win => "win"
      case _ => halt("Unsupported platform")
    }
    val platformHome = sireumHome / "bin" / platform
    val altErgoOpen = platformHome / "alt-ergo-open"
    return HashMap.empty[String, String] ++ ISZ[(String, String)](
      "cvc4" ~> (platformHome / "cvc").string,
      "cvc5" ~> (platformHome / "cvc5").string,
      "z3" ~> (platformHome / "z3" / "bin" / "z3").string,
    ) ++ (if (altErgoOpen.exists) ISZ(altErgoOpen.name ~> altErgoOpen.string) else ISZ[(String, String)]()) ++
      (for (p <- (platformHome / ".opam").list if (p / "bin" / "alt-ergo").exists) yield
        "alt-ergo" ~> (p / "bin" / "alt-ergo").string)
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
    val fs: ISZ[() => Either[Smt2Query.Result, (String, ISZ[String], Smt2Query.Result.Kind.Type)] @pure] = for (config <- configs) yield () => {
      val args = config.opts
      var proc = Os.proc(config.exe +: args).input(queryString)
      proc = proc.timeout(timeoutInMs * Os.numOfProcessors * 2)
      val startTime = extension.Time.currentMillis
      val pr = proc.run()
      val pout: String = st"${pr.err}${pr.out}".render
      val isTimeout: B = timeoutCodes.contains(pr.exitCode) ||
        (config.name === "cvc5" && ops.StringOps(pout).contains("cvc5 interrupted by timeout."))
      val isUnknown: B = if (pr.exitCode == 1) {
        config.name match {
          case string"cvc5" =>
            val poutOps = ops.StringOps(pout)
            poutOps.contains("An uninterpreted constant was preregistered to the UF theory") ||
              poutOps.contains("Array theory solver does not yet support write-chains connecting two different constant arrays")
          case string"alt-ergo" => T
          case string"alt-ergo-open" => T
          case _ => F
        }
      } else if (pr.exitCode == 2) {
        val poutOps = ops.StringOps(pout)
        config.name match {
          case string"alt-ergo" if poutOps.contains("exception Psmt2Frontend__Smtlib_parser.MenhirBasics.Error") => T
          case string"alt-ergo-open" if poutOps.contains("exception Psmt2Frontend__Smtlib_parser.MenhirBasics.Error") => T
          case _ => F
        }
      } else {
        F
      }
      val rOpt: Either[Smt2Query.Result, (String, ISZ[String], Smt2Query.Result.Kind.Type)] = {
        val duration = extension.Time.currentMillis - startTime
        val out = ops.StringOps(pout).split((c: C) => c == '\n')
        val firstLine: String = if (isTimeout) {
          "timeout"
        } else if (isUnknown) {
          "unknown"
        } else {
          var l: String = ""
          var i: Z = 0
          while (i < out.size) {
            val lineOps = ops.StringOps(out(i))
            if (!(lineOps.startsWith(";") || lineOps.trim.size === 0)) {
              l = out(i)
              i = out.size
            }
            i = i + 1
          }
          ops.StringOps(l).trim
        }
        firstLine match {
          case string"sat" => Either.Left(Smt2Query.Result(Smt2Query.Result.Kind.Sat, config.name, queryString,
            st"""; Result: ${if (isSat) "Sat" else "Invalid"}
                |; Solver: ${config.exe}
                |; Arguments: ${(args, " ")}""".render, pout, duration, F))
          case string"unsat" => Either.Left(Smt2Query.Result(Smt2Query.Result.Kind.Unsat, config.name, queryString,
            st"""; Result: ${if (isSat) "Unsat" else "Valid"}
                |; Solver: ${config.exe}
                |; Arguments: ${(args, " ")}""".render, pout, duration, F))
          case string"timeout" => Either.Right((config.exe, config.opts, Smt2Query.Result.Kind.Timeout))
          case string"unknown" => Either.Right((config.exe, config.opts, Smt2Query.Result.Kind.Unknown))
          case string"cvc5 interrupted by timeout." => Either.Right((config.exe, config.opts, Smt2Query.Result.Kind.Timeout))
          case _ => Either.Left(Smt2Query.Result(Smt2Query.Result.Kind.Error, config.name, queryString,
            st"""; Result: Error (exit code ${pr.exitCode})
                |; Solver: ${config.exe}
                |; Arguments: ${(config.opts, " ")}
                |; Output:
                |${(for (line <- ops.StringOps(pout).split((c: C) => c === '\n')) yield st"; $line", "\n")}""".render, pout, duration, F))
        }
      }
      rOpt
    }
    val r: Smt2Query.Result = ops.ISZOpsUtil.invokeAnyEither(fs, smt2Seq || fs.size == 1) match {
      case Either.Left(qr) =>
        if (haltOnError && qr.kind == Smt2Query.Result.Kind.Error) {
          halt(
            st"""${qr.info}
                |${qr.query}""".render
          )
        }
        qr
      case Either.Right(ts) =>
        val sortedTs = ops.ISZOps(ts).sortWith((t1: (String, ISZ[String], Smt2Query.Result.Kind.Type), t2: (String, ISZ[String], Smt2Query.Result.Kind.Type)) =>
          Os.path(t1._1).name < Os.path(t2._1).name
        )
        val kinds = Set.empty[String] ++ (for (t <- sortedTs) yield t._3.string)
        Smt2Query.Result(Smt2Query.Result.Kind.Unknown, "all", queryString,
          st"""; Result: ${(ops.ISZOps(kinds.elements).sortWith((s1: String, s2: String) => s1 < s2), " or ")}
              |; Solver and arguments:
              |${(for (t <- sortedTs) yield st"; * ${t._3}: ${t._1} ${(t._2, " ")}", "\n")}""".render,
          "", extension.Time.currentMillis - start, F)
    }
    cache.set(isSat, queryString, smt2Args, r(cached = T, info = ops.StringOps(r.info).replaceAllLiterally("Result:", "Result (cached):")))
    return r
  }

}
