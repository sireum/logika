// #Sireum
/*
 Copyright (c) 2017-2023, Robby, Kansas State University
 ∀ rights reserved.

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
package org.sireum.logika.options

import org.sireum._
import org.sireum.logika.{Config, Logika, Smt2, Smt2Config}

object OptionsUtil {

  def mineConfig(defaultConfig: Config, maxCores: Z, title: String, nameExePathMap: HashMap[String, String],
                 fileContent: String, reporter: message.Reporter): Config = {
    val m = LibUtil.mineOptions(fileContent)
    val options: String = m.get("logika") match {
      case Some(o) => o
      case _ => return defaultConfig
    }
    toConfig(defaultConfig, maxCores, title, nameExePathMap, options) match {
      case Either.Left(c) => return c
      case Either.Right(msgs) =>
        for (msg <- msgs) {
          reporter.error(None(), Logika.kind, msg)
        }
        return defaultConfig
    }
  }

  def toConfig(defaultConfig: Config, maxCores: Z, title: String, nameExePathMap: HashMap[String, String],
               options: String): Either[Config, ISZ[String]] = {
    val opts: ISZ[String] = for (option <- ops.StringOps(options).split((c: C) => c == ' ')) yield
      ops.StringOps(option).replaceAllChars('␣', ' ')
    val cli = OptionsCli(':', message.Reporter.create)

    val o: OptionsCli.LogikaOption = cli.parseLogika(opts, 0) match {
      case Some(option: OptionsCli.LogikaOption) => option
      case _ => return Either.Right(for (m <- cli.reporter.messages) yield m.text)
    }

    if (o.line != 0) {
      return Either.Right(ISZ(s"Option --line is not allowed as a $title option"))
    }

    if (o.logVcDir.nonEmpty) {
      return Either.Right(ISZ(s"Option --log-vc-dir is not allowed as a $title option"))
    }

    if (o.logPc) {
      return Either.Right(ISZ(s"Option --log-pc is not allowed as a $title option"))
    }

    if (o.logPcLines) {
      return Either.Right(ISZ(s"Option --log-pc-lines is not allowed as a $title option"))
    }

    if (o.logPc) {
      return Either.Right(ISZ(s"Option --log-vc is not allowed as a $title option"))
    }

    if (o.logRawPc) {
      return Either.Right(ISZ(s"Option --log-raw-vc is not allowed as a $title option"))
    }

    if (o.infoFlow && (o.splitAll || o.splitContract || o.splitIf || o.splitMatch)) {
      if (o.splitAll) {
        return Either.Right(ISZ("Cannot split all paths when info flow verification is enabled"))
      }
      if (o.splitMatch) {
        return Either.Right(ISZ("Cannot split match-statement when info flow verification is enabled"))
      }
      if (o.splitIf) {
        return Either.Right(ISZ("Cannot split if-statement when info flow verification is enabled"))
      }
      if (o.splitContract) {
        return Either.Right(ISZ("Cannot split compositional contract cases when info flow verification is enabled"))
      }
    }

    o.charBitWidth match {
      case z"8" =>
      case z"16" =>
      case z"32" =>
      case _ =>
        return Either.Right(ISZ(s"C (character) bit-width has to be 8, 16, or 32 (instead of ${o.charBitWidth})"))
    }

    o.intBitWidth match {
      case z"0" =>
      case z"8" =>
      case z"16" =>
      case z"32" =>
      case z"64" =>
      case _ =>
        return Either.Right(ISZ(s"Z (integer) bit-width has to be 0 (arbitrary-precision), 8, 16, 32, or 64 (instead of ${o.intBitWidth})"))
    }

    val smt2Configs: ISZ[Smt2Config] = (Smt2.parseConfigs(nameExePathMap, F, o.smt2ValidConfigs.get, o.timeout * 1000, o.rlimit),
      Smt2.parseConfigs(nameExePathMap, T, o.smt2SatConfigs.get, Smt2.satTimeoutInMs, o.rlimit)) match {
      case (Either.Left(c1), Either.Left(c2)) => c1 ++ c2
      case (Either.Right(msg1), Either.Right(msg2)) => return Either.Right(ISZ(msg1, msg2))
      case (Either.Right(msg), _) => return Either.Right(ISZ(msg))
      case (_, Either.Right(msg)) => return Either.Right(ISZ(msg))
    }

    val fpRoundingMode: String = o.fpRounding match {
      case OptionsCli.LogikaFPRoundingMode.NearestTiesToEven => "RNE"
      case OptionsCli.LogikaFPRoundingMode.NearestTiesToAway => "RNA"
      case OptionsCli.LogikaFPRoundingMode.TowardPositive => "RTP"
      case OptionsCli.LogikaFPRoundingMode.TowardNegative => "RTN"
      case OptionsCli.LogikaFPRoundingMode.TowardZero => "RTZ"
    }
    val parCores = LibUtil.parCoresOpt(maxCores, o.par)
    val branchParCores = LibUtil.parCoresOpt(maxCores, o.branchPar)
    val branchParMode: org.sireum.logika.Config.BranchPar.Type = o.branchParMode match {
      case OptionsCli.LogikaBranchPar.All => org.sireum.logika.Config.BranchPar.All
      case OptionsCli.LogikaBranchPar.Returns => org.sireum.logika.Config.BranchPar.OnlyAllReturns
      case OptionsCli.LogikaBranchPar.Disabled => org.sireum.logika.Config.BranchPar.Disabled
    }

    val config = logika.Config(
      smt2Configs = smt2Configs,
      parCores = parCores,
      sat = o.sat,
      rlimit = o.rlimit,
      timeoutInMs = o.timeout * 1000,
      charBitWidth = o.charBitWidth,
      intBitWidth = o.intBitWidth,
      useReal = o.useReal,
      logPc = F,
      logRawPc = F,
      logVc = F,
      logVcDirOpt = None(),
      dontSplitPfq = o.dontSplitFunQuant,
      splitAll = o.splitAll,
      splitIf = o.splitIf,
      splitMatch = o.splitMatch,
      splitContract = o.splitContract,
      simplifiedQuery = o.simplify,
      checkInfeasiblePatternMatch = defaultConfig.checkInfeasiblePatternMatch,
      fpRoundingMode = fpRoundingMode,
      caching = defaultConfig.caching,
      smt2Seq = o.sequential,
      branchPar = branchParMode,
      branchParCores = branchParCores,
      atLinesFresh = F,
      interp = o.interprocedural,
      loopBound = o.loopBound,
      callBound = o.callBound,
      interpContracts = o.interproceduralContracts,
      elideEncoding = o.elideEncoding,
      rawInscription = o.rawInscription,
      flipStrictPure = o.flipStrictPure,
      transitionCache = defaultConfig.transitionCache,
      patternExhaustive = o.patternExhaustive,
      pureFun = o.pureFun
    )
    return Either.Left(config)
  }

  def fromConfig(config: Config): String = {
    halt("TODO")
  }
}
