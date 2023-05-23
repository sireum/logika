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

  val logika: String = "Logika"

  def mineConfig(defaultConfig: Config, maxCores: Z, title: String, nameExePathMap: HashMap[String, String],
                 fileContent: String, posOpt: Option[message.Position], reporter: message.Reporter): Config = {
    val m = LibUtil.mineOptions(fileContent)
    val options: String = m.get(logika) match {
      case Some(o) => o
      case _ => return defaultConfig
    }
    toConfig(defaultConfig, maxCores, title, nameExePathMap, options) match {
      case Either.Left(c) => return c
      case Either.Right(msgs) =>
        for (msg <- msgs) {
          reporter.error(posOpt, Logika.kind, msg)
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

    if (o.logPc) {
      return Either.Right(ISZ(s"Option --log-pc is not allowed as a $title option"))
    }

    if (o.logRawPc) {
      return Either.Right(ISZ(s"Option --log-raw-pc is not allowed as a $title option"))
    }

    if (o.logVc) {
      return Either.Right(ISZ(s"Option --log-vc is not allowed as a $title option"))
    }

    if (o.logVcDir.nonEmpty) {
      return Either.Right(ISZ(s"Option --log-vc-dir is not allowed as a $title option"))
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

    val smt2Configs: ISZ[Smt2Config] = (Smt2.parseConfigs(nameExePathMap, F, o.smt2ValidConfigs.get),
      Smt2.parseConfigs(nameExePathMap, T, o.smt2SatConfigs.get)) match {
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

    val config = org.sireum.logika.Config(
      smt2Configs = smt2Configs,
      parCores = parCores,
      sat = o.sat,
      rlimit = o.rlimit,
      timeoutInMs = o.timeout * 1000,
      charBitWidth = o.charBitWidth,
      intBitWidth = o.intBitWidth,
      useReal = o.useReal,
      logPc = defaultConfig.logPc,
      logRawPc = defaultConfig.logRawPc,
      logVc = defaultConfig.logVc,
      logVcDirOpt = defaultConfig.logVcDirOpt,
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
      atLinesFresh = o.logPcLines,
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

  def fromConfig(maxCores: Z, nameExePathMap: HashMap[String, String], config: Config): String = {
    val defaultConfig = toConfig(config, maxCores, "default", nameExePathMap, "").left

    var r = ISZ[String]()

    def addSmt2Config(isSat: B): Unit = {
      var ds = ISZ[String]()
      for (c <- defaultConfig.smt2Configs if c.isSat == isSat) {
        ds = ds :+ st"${(c.name +: c.opts, ",")}".render
      }
      var rs = ISZ[String]()
      for (c <- config.smt2Configs if c.isSat == isSat) {
        rs = rs :+ st"${(c.name +: c.opts, ",")}".render
      }
      val dc = st"${(ds, ";")}".render
      val rc = st"${(rs, ";")}".render
      if (dc != rc) {
        r = r :+ (if (isSat) "--solver-sat" else "--solver-valid")
        r = r :+ rc
      }
    }

    @strictpure def max(value1: Z, value2: Z): Z =
      if (value1 > value2) value1 else value2

    if (config.transitionCache != defaultConfig.transitionCache) {
      r = r :+ "--transition-caching"
    }
    if (config.caching != defaultConfig.caching) {
      r = r :+ "--smt2-caching"
    }
    if (config.parCores > 1) {
      val value = config.parCores * 100 / maxCores
      if (value == 100) {
        r = r :+ "--par"
      } else {
        r = r ++ ISZ[String]("--par", value.string)
      }
    }
    if (config.branchParCores > 1) {
      val value = config.branchParCores * 100 / maxCores
      if (value == 100) {
        r = r :+ "--par-branch"
      } else {
        r = r ++ ISZ[String]("--par-branch", value.string)
      }
    }
    if (config.branchPar != defaultConfig.branchPar) {
      val value: String = config.branchPar match {
        case Config.BranchPar.All => "all"
        case Config.BranchPar.OnlyAllReturns => "returns"
        case Config.BranchPar.Disabled => "disabled"
      }
      r = r ++ ISZ[String]("--par-branch-mode", value)
    }
    if (config.sat != defaultConfig.sat) {
      r = r :+ "--sat"
    }
    if (config.rlimit != defaultConfig.rlimit) {
      r = r ++ ISZ[String]("--rlimit", config.rlimit.string)
    }
    if (config.timeoutInMs != defaultConfig.timeoutInMs) {
      r = r ++ ISZ[String]("--timeout", max(config.timeoutInMs / 1000, 1).string)
    }
    if (config.charBitWidth != defaultConfig.charBitWidth) {
      r = r ++ ISZ[String]("--c-bitwidth", config.charBitWidth.string)
    }
    if (config.intBitWidth != defaultConfig.intBitWidth) {
      r = r ++ ISZ[String]("--z-bitwidth", config.intBitWidth.string)
    }
    if (config.useReal != defaultConfig.useReal) {
      r = r :+ "--use-real"
    }
    if (config.logRawPc != defaultConfig.logRawPc) {
      r = r :+ "--log-raw-smt2"
    }
    if (config.dontSplitPfq != defaultConfig.dontSplitPfq) {
      r = r :+ "--dont-split-pfq"
    }
    if (config.splitAll != defaultConfig.splitAll) {
      r = r :+ "--split-all"
    }
    if (config.splitIf != defaultConfig.splitIf) {
      r = r :+ "--split-if"
    }
    if (config.splitMatch != defaultConfig.splitMatch) {
      r = r :+ "--split-match"
    }
    if (config.splitContract != defaultConfig.splitContract) {
      r = r :+ "--split-contract"
    }
    if (config.simplifiedQuery != defaultConfig.simplifiedQuery) {
      r = r :+ "--simplify"
    }
    if (config.fpRoundingMode != defaultConfig.fpRoundingMode) {
      val value: String = config.fpRoundingMode.native match {
        case "RNE" => "NearestTiesToEven"
        case "RNA" => "NearestTiesToAway"
        case "RTP" => "TowardPositive"
        case "RTN" => "TowardNegative"
        case "RTZ" => "TowardZero"
      }
      r = r ++ ISZ[String]("--fp-rounding", value)
    }
    if (config.smt2Seq != defaultConfig.smt2Seq) {
      r = r :+ "--smt2-seq"
    }
    if (config.atLinesFresh != defaultConfig.atLinesFresh) {
      r = r :+ "--log-pc-lines"
    }
    if (config.interp != defaultConfig.interp) {
      r = r :+ "--interprocedural"
    }
    if (config.interpContracts != defaultConfig.interpContracts) {
      r = r :+ "--interprocedural-contracts"
    }
    if (config.flipStrictPure != defaultConfig.flipStrictPure) {
      r = r :+ "--flip-strictpure-mode"
    }
    if (config.loopBound != defaultConfig.loopBound) {
      r = r ++ ISZ[String]("--loop-bound", config.loopBound.string)
    }
    if (config.callBound != defaultConfig.callBound) {
      r = r ++ ISZ[String]("--recursive-bound", config.callBound.string)
    }
    if (config.elideEncoding != defaultConfig.elideEncoding) {
      r = r :+ "--elide-encoding"
    }
    if (config.rawInscription != defaultConfig.rawInscription) {
      r = r :+ "--raw-inscription"
    }
    if (config.patternExhaustive != defaultConfig.patternExhaustive) {
      r = r :+ "--pattern-inexhaustive"
    }
    if (config.pureFun != defaultConfig.pureFun) {
      r = r :+ "--pure-proof-fun"
    }

    addSmt2Config(F)
    addSmt2Config(T)

    return st"${(r, " ")}".render
  }
}
