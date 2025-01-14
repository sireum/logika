// #Sireum
// @formatter:off

/*
 Copyright (c) 2017-2025, Robby, Kansas State University
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

// This file is auto-generated from options.sc

package org.sireum.logika.options

import org.sireum._

object OptionsCli {

  @datatype trait LogikaTopOption

  @datatype class HelpOption extends LogikaTopOption

  @enum object LogikaBackground {
    "Type"
    "Save"
    "Disabled"
  }

  @enum object LogikaFPRoundingMode {
    "NearestTiesToEven"
    "NearestTiesToAway"
    "TowardPositive"
    "TowardNegative"
    "TowardZero"
  }

  @enum object LogikaStrictPureMode {
    "Default"
    "Flip"
    "Uninterpreted"
  }

  @datatype class LogikaOption(
    val help: String,
    val args: ISZ[String],
    val background: LogikaBackground.Type,
    val manual: B,
    val smt2Caching: B,
    val transitionCaching: B,
    val infoFlow: B,
    val charBitWidth: Z,
    val fpRounding: LogikaFPRoundingMode.Type,
    val useReal: B,
    val intBitWidth: Z,
    val interprocedural: B,
    val interproceduralContracts: B,
    val strictPureMode: LogikaStrictPureMode.Type,
    val line: Z,
    val loopBound: Z,
    val callBound: Z,
    val patternExhaustive: B,
    val pureFun: B,
    val sat: B,
    val skipMethods: ISZ[String],
    val skipTypes: ISZ[String],
    val logPc: B,
    val logPcLines: B,
    val logRawPc: B,
    val logVc: B,
    val logVcDir: Option[String],
    val logDetailedInfo: B,
    val logAtRewrite: B,
    val stats: B,
    val par: Option[Z],
    val branchPar: B,
    val branchParReturn: B,
    val branchPredNum: Z,
    val branchPredComplexity: Z,
    val rwPar: B,
    val dontSplitFunQuant: B,
    val splitAll: B,
    val splitContract: B,
    val splitIf: B,
    val splitMatch: B,
    val rwMax: Z,
    val rwTrace: B,
    val rwEvalTrace: B,
    val elideEncoding: B,
    val rawInscription: B,
    val rlimit: Z,
    val sequential: B,
    val simplify: B,
    val smt2SatConfigs: Option[String],
    val smt2ValidConfigs: Option[String],
    val satTimeout: B,
    val timeout: Z,
    val searchPC: B
  ) extends LogikaTopOption
}

import OptionsCli._

@record class OptionsCli(val pathSep: C, reporter: message.Reporter) {

  def parseLogikaBackgroundH(arg: String): Option[LogikaBackground.Type] = {
    arg.native match {
      case "type" => return Some(LogikaBackground.Type)
      case "save" => return Some(LogikaBackground.Save)
      case "disabled" => return Some(LogikaBackground.Disabled)
      case s =>
        reporter.error(None(), "OptionsCli", s"Expecting one of the following: { type, save, disabled }, but found '$s'.")
        return None()
    }
  }

  def parseLogikaBackground(args: ISZ[String], i: Z): Option[LogikaBackground.Type] = {
    if (i >= args.size) {
      reporter.error(None(), "OptionsCli", "Expecting one of the following: { type, save, disabled }, but none found.")
      return None()
    }
    val r = parseLogikaBackgroundH(args(i))
    return r
  }

  def parseLogikaFPRoundingModeH(arg: String): Option[LogikaFPRoundingMode.Type] = {
    arg.native match {
      case "NearestTiesToEven" => return Some(LogikaFPRoundingMode.NearestTiesToEven)
      case "NearestTiesToAway" => return Some(LogikaFPRoundingMode.NearestTiesToAway)
      case "TowardPositive" => return Some(LogikaFPRoundingMode.TowardPositive)
      case "TowardNegative" => return Some(LogikaFPRoundingMode.TowardNegative)
      case "TowardZero" => return Some(LogikaFPRoundingMode.TowardZero)
      case s =>
        reporter.error(None(), "OptionsCli", s"Expecting one of the following: { NearestTiesToEven, NearestTiesToAway, TowardPositive, TowardNegative, TowardZero }, but found '$s'.")
        return None()
    }
  }

  def parseLogikaFPRoundingMode(args: ISZ[String], i: Z): Option[LogikaFPRoundingMode.Type] = {
    if (i >= args.size) {
      reporter.error(None(), "OptionsCli", "Expecting one of the following: { NearestTiesToEven, NearestTiesToAway, TowardPositive, TowardNegative, TowardZero }, but none found.")
      return None()
    }
    val r = parseLogikaFPRoundingModeH(args(i))
    return r
  }

  def parseLogikaStrictPureModeH(arg: String): Option[LogikaStrictPureMode.Type] = {
    arg.native match {
      case "default" => return Some(LogikaStrictPureMode.Default)
      case "flip" => return Some(LogikaStrictPureMode.Flip)
      case "uninterpreted" => return Some(LogikaStrictPureMode.Uninterpreted)
      case s =>
        reporter.error(None(), "OptionsCli", s"Expecting one of the following: { default, flip, uninterpreted }, but found '$s'.")
        return None()
    }
  }

  def parseLogikaStrictPureMode(args: ISZ[String], i: Z): Option[LogikaStrictPureMode.Type] = {
    if (i >= args.size) {
      reporter.error(None(), "OptionsCli", "Expecting one of the following: { default, flip, uninterpreted }, but none found.")
      return None()
    }
    val r = parseLogikaStrictPureModeH(args(i))
    return r
  }

  def parseLogika(args: ISZ[String], i: Z): Option[LogikaTopOption] = {
    val help =
      st"""Logika Verifier Options
          |
          |Usage: <option>*
          |
          |Available Options:
          |    --background         Background verification mode (expects one of { type,
          |                           save, disabled }; default: type)
          |-m, --manual             Set verification mode to manual for Slang scripts
          |    --smt2-caching       Disable SMT2 query caching
          |    --transition-caching Disable transition caching
          |-h, --help               Display this information
          |
          |Additional Verifications Options:
          |    --info-flow          Enable information flow verification
          |
          |Approximation Options:
          |    --c-bitwidth         Bit-width representation for C (character) values
          |                           (expected 8, 16, or 32) (expects an integer; default
          |                           is 32)
          |    --fp-rounding        Rounding mode for floating point numbers (expects one
          |                           of { NearestTiesToEven, NearestTiesToAway,
          |                           TowardPositive, TowardNegative, TowardZero };
          |                           default: NearestTiesToEven)
          |    --use-real           Use reals to approximate floating-point numbers
          |    --z-bitwidth         Bit-width representation for Z (integer) values
          |                           (expected 0, 8, 16, 32, 64) (expects an integer;
          |                           default is 0)
          |
          |Control Options:
          |    --interprocedural    Enable inter-procedural verification on
          |                           non-strict-pure methods
          |    --interprocedural-contracts
          |                          Use contracts in inter-procedural verification
          |    --strictpure-mode    Strict-pure method treatment mode in
          |                           compositional/interprocedural verification (expects
          |                           one of { default, flip, uninterpreted }; default:
          |                           default)
          |    --line               Focus verification to the specified program line
          |                           number (expects an integer; min is 0; default is 0)
          |    --loop-bound         Loop bound for inter-procedural verification (expects
          |                           an integer; min is 1; default is 3)
          |    --recursive-bound    Recursive call-chain bound for inter-procedural
          |                           verification (expects an integer; min is 1; default
          |                           is 3)
          |    --pattern-inexhaustive
          |                          Disable pattern exhaustiveness checking
          |    --pure-proof-fun     Always add proof functions for pure methods
          |    --sat                Enable assumption satisfiability checking
          |    --skip-methods       Skip checking methods with the specified
          |                           fully-qualified names or identifiers (expects a
          |                           string separated by ",")
          |    --skip-types         Skip checking traits, classes, and objects with the
          |                           specified fully-qualified names or identifiers
          |                           (expects a string separated by ",")
          |
          |Logging Options:
          |    --log-pc             Display path conditions before each statement
          |    --log-pc-lines       Display At(...) path condition line numbers and unique
          |                           symbolic value numbering
          |    --log-raw-pc         Display raw path conditions before each statement
          |    --log-vc             Display all verification conditions
          |    --log-vc-dir         Write all verification conditions in a directory
          |                           (expects a path)
          |    --log-detailed-info  Display detailed feedback information
          |    --log-rewrite-at     Disable At(...) rewriting as In(...)/Old(...) in
          |                           symexe mode
          |    --stats              Collect verification statistics
          |
          |Optimizations Options:
          |-p, --par                Enable parallelization (with CPU cores percentage to
          |                           use) (accepts an optional integer; min is 1; max is
          |                           100; default is 100)
          |    --par-branch         Enable branch parallelization
          |    --par-branch-return  Only use branch parallelization if all branches return
          |    --par-branch-pred-num
          |                          Enable branch parallelization (expects an integer;
          |                           min is 2; default is 2)
          |    --par-branch-pred-complexity
          |                          Enable branch parallelization (expects an integer;
          |                           min is 0; default is 10)
          |    --par-rw             Enable rewriting parallelization
          |
          |Path Splitting Options:
          |    --dont-split-pfq     Do not force splitting in quantifiers and proof
          |                           functions derived from @strictpure methods
          |    --split-all          Split all
          |    --split-contract     Split on contract cases
          |    --split-if           Split on if-conditional expressions and statements
          |    --split-match        Split on match expressions and statements
          |
          |Rewriting Options:
          |    --rw-max             Maximum number of rewriting (expects an integer; min
          |                           is 1; default is 100)
          |    --rw-trace           Disable rewriting trace
          |    --rw-eval-trace      Disable evaluation rewriting trace
          |
          |SMT2 Options:
          |    --elide-encoding     Strip out SMT2 encoding in feedback
          |    --raw-inscription    Use raw sequent/sat preamble inscription
          |    --rlimit             SMT2 solver resource limit (expects an integer; min is
          |                           0; default is 2000000)
          |    --smt2-seq           Disable SMT2 solvers parallelization
          |    --simplify           Simplify SMT2 query (experimental)
          |    --solver-sat         SMT2 configurations for satisfiability queries
          |                           (expects a string; default is "z3")
          |    --solver-valid       SMT2 configurations for validity queries (expects a
          |                           string; default is "cvc4,--full-saturate-quant; z3;
          |                           cvc5,--full-saturate-quant")
          |    --sat-timeout        Use validity checking timeout for satisfiability
          |                           checking (otherwise: 500ms)
          |-t, --timeout            Timeout (seconds) for validity checking (expects an
          |                           integer; min is 1; default is 2)
          |    --search-pc          Search path conditions first before employing SMT2
          |                           solvers when discharging VCs""".render

    var background: LogikaBackground.Type = LogikaBackground.Type
    var manual: B = false
    var smt2Caching: B = true
    var transitionCaching: B = true
    var infoFlow: B = false
    var charBitWidth: Z = 32
    var fpRounding: LogikaFPRoundingMode.Type = LogikaFPRoundingMode.NearestTiesToEven
    var useReal: B = false
    var intBitWidth: Z = 0
    var interprocedural: B = false
    var interproceduralContracts: B = false
    var strictPureMode: LogikaStrictPureMode.Type = LogikaStrictPureMode.Default
    var line: Z = 0
    var loopBound: Z = 3
    var callBound: Z = 3
    var patternExhaustive: B = true
    var pureFun: B = false
    var sat: B = false
    var skipMethods: ISZ[String] = ISZ[String]()
    var skipTypes: ISZ[String] = ISZ[String]()
    var logPc: B = false
    var logPcLines: B = false
    var logRawPc: B = false
    var logVc: B = false
    var logVcDir: Option[String] = None[String]()
    var logDetailedInfo: B = false
    var logAtRewrite: B = true
    var stats: B = false
    var par: Option[Z] = None()
    var branchPar: B = false
    var branchParReturn: B = false
    var branchPredNum: Z = 2
    var branchPredComplexity: Z = 10
    var rwPar: B = true
    var dontSplitFunQuant: B = false
    var splitAll: B = false
    var splitContract: B = false
    var splitIf: B = false
    var splitMatch: B = false
    var rwMax: Z = 100
    var rwTrace: B = true
    var rwEvalTrace: B = true
    var elideEncoding: B = false
    var rawInscription: B = false
    var rlimit: Z = 2000000
    var sequential: B = false
    var simplify: B = false
    var smt2SatConfigs: Option[String] = Some("z3")
    var smt2ValidConfigs: Option[String] = Some("cvc4,--full-saturate-quant; z3; cvc5,--full-saturate-quant")
    var satTimeout: B = false
    var timeout: Z = 2
    var searchPC: B = false
    var j = i
    var isOption = T
    while (j < args.size && isOption) {
      val arg = args(j)
      if (ops.StringOps(arg).first == '-') {
        if (args(j) == "-h" || args(j) == "--help") {
          println(help)
          return Some(HelpOption())
        } else if (arg == "--background") {
           val o: Option[LogikaBackground.Type] = parseLogikaBackground(args, j + 1)
           o match {
             case Some(v) => background = v
             case _ => return None()
           }
         } else if (arg == "-m" || arg == "--manual") {
           val o: Option[B] = { j = j - 1; Some(!manual) }
           o match {
             case Some(v) => manual = v
             case _ => return None()
           }
         } else if (arg == "--smt2-caching") {
           val o: Option[B] = { j = j - 1; Some(!smt2Caching) }
           o match {
             case Some(v) => smt2Caching = v
             case _ => return None()
           }
         } else if (arg == "--transition-caching") {
           val o: Option[B] = { j = j - 1; Some(!transitionCaching) }
           o match {
             case Some(v) => transitionCaching = v
             case _ => return None()
           }
         } else if (arg == "--info-flow") {
           val o: Option[B] = { j = j - 1; Some(!infoFlow) }
           o match {
             case Some(v) => infoFlow = v
             case _ => return None()
           }
         } else if (arg == "--c-bitwidth") {
           val o: Option[Z] = parseNum(args, j + 1, None(), None())
           o match {
             case Some(v) => charBitWidth = v
             case _ => return None()
           }
         } else if (arg == "--fp-rounding") {
           val o: Option[LogikaFPRoundingMode.Type] = parseLogikaFPRoundingMode(args, j + 1)
           o match {
             case Some(v) => fpRounding = v
             case _ => return None()
           }
         } else if (arg == "--use-real") {
           val o: Option[B] = { j = j - 1; Some(!useReal) }
           o match {
             case Some(v) => useReal = v
             case _ => return None()
           }
         } else if (arg == "--z-bitwidth") {
           val o: Option[Z] = parseNum(args, j + 1, None(), None())
           o match {
             case Some(v) => intBitWidth = v
             case _ => return None()
           }
         } else if (arg == "--interprocedural") {
           val o: Option[B] = { j = j - 1; Some(!interprocedural) }
           o match {
             case Some(v) => interprocedural = v
             case _ => return None()
           }
         } else if (arg == "--interprocedural-contracts") {
           val o: Option[B] = { j = j - 1; Some(!interproceduralContracts) }
           o match {
             case Some(v) => interproceduralContracts = v
             case _ => return None()
           }
         } else if (arg == "--strictpure-mode") {
           val o: Option[LogikaStrictPureMode.Type] = parseLogikaStrictPureMode(args, j + 1)
           o match {
             case Some(v) => strictPureMode = v
             case _ => return None()
           }
         } else if (arg == "--line") {
           val o: Option[Z] = parseNum(args, j + 1, Some(0), None())
           o match {
             case Some(v) => line = v
             case _ => return None()
           }
         } else if (arg == "--loop-bound") {
           val o: Option[Z] = parseNum(args, j + 1, Some(1), None())
           o match {
             case Some(v) => loopBound = v
             case _ => return None()
           }
         } else if (arg == "--recursive-bound") {
           val o: Option[Z] = parseNum(args, j + 1, Some(1), None())
           o match {
             case Some(v) => callBound = v
             case _ => return None()
           }
         } else if (arg == "--pattern-inexhaustive") {
           val o: Option[B] = { j = j - 1; Some(!patternExhaustive) }
           o match {
             case Some(v) => patternExhaustive = v
             case _ => return None()
           }
         } else if (arg == "--pure-proof-fun") {
           val o: Option[B] = { j = j - 1; Some(!pureFun) }
           o match {
             case Some(v) => pureFun = v
             case _ => return None()
           }
         } else if (arg == "--sat") {
           val o: Option[B] = { j = j - 1; Some(!sat) }
           o match {
             case Some(v) => sat = v
             case _ => return None()
           }
         } else if (arg == "--skip-methods") {
           val o: Option[ISZ[String]] = parseStrings(args, j + 1, ',')
           o match {
             case Some(v) => skipMethods = v
             case _ => return None()
           }
         } else if (arg == "--skip-types") {
           val o: Option[ISZ[String]] = parseStrings(args, j + 1, ',')
           o match {
             case Some(v) => skipTypes = v
             case _ => return None()
           }
         } else if (arg == "--log-pc") {
           val o: Option[B] = { j = j - 1; Some(!logPc) }
           o match {
             case Some(v) => logPc = v
             case _ => return None()
           }
         } else if (arg == "--log-pc-lines") {
           val o: Option[B] = { j = j - 1; Some(!logPcLines) }
           o match {
             case Some(v) => logPcLines = v
             case _ => return None()
           }
         } else if (arg == "--log-raw-pc") {
           val o: Option[B] = { j = j - 1; Some(!logRawPc) }
           o match {
             case Some(v) => logRawPc = v
             case _ => return None()
           }
         } else if (arg == "--log-vc") {
           val o: Option[B] = { j = j - 1; Some(!logVc) }
           o match {
             case Some(v) => logVc = v
             case _ => return None()
           }
         } else if (arg == "--log-vc-dir") {
           val o: Option[Option[String]] = parsePath(args, j + 1)
           o match {
             case Some(v) => logVcDir = v
             case _ => return None()
           }
         } else if (arg == "--log-detailed-info") {
           val o: Option[B] = { j = j - 1; Some(!logDetailedInfo) }
           o match {
             case Some(v) => logDetailedInfo = v
             case _ => return None()
           }
         } else if (arg == "--log-rewrite-at") {
           val o: Option[B] = { j = j - 1; Some(!logAtRewrite) }
           o match {
             case Some(v) => logAtRewrite = v
             case _ => return None()
           }
         } else if (arg == "--stats") {
           val o: Option[B] = { j = j - 1; Some(!stats) }
           o match {
             case Some(v) => stats = v
             case _ => return None()
           }
         } else if (arg == "-p" || arg == "--par") {
           val o: Option[Option[Z]] = parseNumFlag(args, j + 1, Some(1), Some(100)) match {
             case o@Some(None()) => j = j - 1; Some(Some(100))
             case o => o
           }
           o match {
             case Some(v) => par = v
             case _ => return None()
           }
         } else if (arg == "--par-branch") {
           val o: Option[B] = { j = j - 1; Some(!branchPar) }
           o match {
             case Some(v) => branchPar = v
             case _ => return None()
           }
         } else if (arg == "--par-branch-return") {
           val o: Option[B] = { j = j - 1; Some(!branchParReturn) }
           o match {
             case Some(v) => branchParReturn = v
             case _ => return None()
           }
         } else if (arg == "--par-branch-pred-num") {
           val o: Option[Z] = parseNum(args, j + 1, Some(2), None())
           o match {
             case Some(v) => branchPredNum = v
             case _ => return None()
           }
         } else if (arg == "--par-branch-pred-complexity") {
           val o: Option[Z] = parseNum(args, j + 1, Some(0), None())
           o match {
             case Some(v) => branchPredComplexity = v
             case _ => return None()
           }
         } else if (arg == "--par-rw") {
           val o: Option[B] = { j = j - 1; Some(!rwPar) }
           o match {
             case Some(v) => rwPar = v
             case _ => return None()
           }
         } else if (arg == "--dont-split-pfq") {
           val o: Option[B] = { j = j - 1; Some(!dontSplitFunQuant) }
           o match {
             case Some(v) => dontSplitFunQuant = v
             case _ => return None()
           }
         } else if (arg == "--split-all") {
           val o: Option[B] = { j = j - 1; Some(!splitAll) }
           o match {
             case Some(v) => splitAll = v
             case _ => return None()
           }
         } else if (arg == "--split-contract") {
           val o: Option[B] = { j = j - 1; Some(!splitContract) }
           o match {
             case Some(v) => splitContract = v
             case _ => return None()
           }
         } else if (arg == "--split-if") {
           val o: Option[B] = { j = j - 1; Some(!splitIf) }
           o match {
             case Some(v) => splitIf = v
             case _ => return None()
           }
         } else if (arg == "--split-match") {
           val o: Option[B] = { j = j - 1; Some(!splitMatch) }
           o match {
             case Some(v) => splitMatch = v
             case _ => return None()
           }
         } else if (arg == "--rw-max") {
           val o: Option[Z] = parseNum(args, j + 1, Some(1), None())
           o match {
             case Some(v) => rwMax = v
             case _ => return None()
           }
         } else if (arg == "--rw-trace") {
           val o: Option[B] = { j = j - 1; Some(!rwTrace) }
           o match {
             case Some(v) => rwTrace = v
             case _ => return None()
           }
         } else if (arg == "--rw-eval-trace") {
           val o: Option[B] = { j = j - 1; Some(!rwEvalTrace) }
           o match {
             case Some(v) => rwEvalTrace = v
             case _ => return None()
           }
         } else if (arg == "--elide-encoding") {
           val o: Option[B] = { j = j - 1; Some(!elideEncoding) }
           o match {
             case Some(v) => elideEncoding = v
             case _ => return None()
           }
         } else if (arg == "--raw-inscription") {
           val o: Option[B] = { j = j - 1; Some(!rawInscription) }
           o match {
             case Some(v) => rawInscription = v
             case _ => return None()
           }
         } else if (arg == "--rlimit") {
           val o: Option[Z] = parseNum(args, j + 1, Some(0), None())
           o match {
             case Some(v) => rlimit = v
             case _ => return None()
           }
         } else if (arg == "--smt2-seq") {
           val o: Option[B] = { j = j - 1; Some(!sequential) }
           o match {
             case Some(v) => sequential = v
             case _ => return None()
           }
         } else if (arg == "--simplify") {
           val o: Option[B] = { j = j - 1; Some(!simplify) }
           o match {
             case Some(v) => simplify = v
             case _ => return None()
           }
         } else if (arg == "--solver-sat") {
           val o: Option[Option[String]] = parseString(args, j + 1)
           o match {
             case Some(v) => smt2SatConfigs = v
             case _ => return None()
           }
         } else if (arg == "--solver-valid") {
           val o: Option[Option[String]] = parseString(args, j + 1)
           o match {
             case Some(v) => smt2ValidConfigs = v
             case _ => return None()
           }
         } else if (arg == "--sat-timeout") {
           val o: Option[B] = { j = j - 1; Some(!satTimeout) }
           o match {
             case Some(v) => satTimeout = v
             case _ => return None()
           }
         } else if (arg == "-t" || arg == "--timeout") {
           val o: Option[Z] = parseNum(args, j + 1, Some(1), None())
           o match {
             case Some(v) => timeout = v
             case _ => return None()
           }
         } else if (arg == "--search-pc") {
           val o: Option[B] = { j = j - 1; Some(!searchPC) }
           o match {
             case Some(v) => searchPC = v
             case _ => return None()
           }
         } else {
          reporter.error(None(), "OptionsCli", s"Unrecognized option '$arg'.")
          return None()
        }
        j = j + 2
      } else {
        isOption = F
      }
    }
    return Some(LogikaOption(help, parseArguments(args, j), background, manual, smt2Caching, transitionCaching, infoFlow, charBitWidth, fpRounding, useReal, intBitWidth, interprocedural, interproceduralContracts, strictPureMode, line, loopBound, callBound, patternExhaustive, pureFun, sat, skipMethods, skipTypes, logPc, logPcLines, logRawPc, logVc, logVcDir, logDetailedInfo, logAtRewrite, stats, par, branchPar, branchParReturn, branchPredNum, branchPredComplexity, rwPar, dontSplitFunQuant, splitAll, splitContract, splitIf, splitMatch, rwMax, rwTrace, rwEvalTrace, elideEncoding, rawInscription, rlimit, sequential, simplify, smt2SatConfigs, smt2ValidConfigs, satTimeout, timeout, searchPC))
  }

  def parseArguments(args: ISZ[String], i: Z): ISZ[String] = {
    var r = ISZ[String]()
    var j = i
    while (j < args.size) {
      r = r :+ args(j)
      j = j + 1
    }
    return r
  }

  def parsePaths(args: ISZ[String], i: Z): Option[ISZ[String]] = {
    return tokenize(args, i, "path", pathSep, F)
  }

  def parsePath(args: ISZ[String], i: Z): Option[Option[String]] = {
    if (i >= args.size) {
      reporter.error(None(), "OptionsCli", "Expecting a path, but none found.")
    }
    return Some(Some(args(i)))
  }

  def parseStrings(args: ISZ[String], i: Z, sep: C): Option[ISZ[String]] = {
    tokenize(args, i, "string", sep, F) match {
      case r@Some(_) => return r
      case _ => return None()
    }
  }

  def parseString(args: ISZ[String], i: Z): Option[Option[String]] = {
    if (i >= args.size) {
      reporter.error(None(), "OptionsCli", "Expecting a string, but none found.")
      return None()
    }
    return Some(Some(args(i)))
  }

  def parseNums(args: ISZ[String], i: Z, sep: C, minOpt: Option[Z], maxOpt: Option[Z]): Option[ISZ[Z]] = {
    tokenize(args, i, "integer", sep, T) match {
      case Some(sargs) =>
        var r = ISZ[Z]()
        for (arg <- sargs) {
          parseNumH(F, arg, minOpt, maxOpt)._2 match {
            case Some(n) => r = r :+ n
            case _ => return None()
          }
        }
        return Some(r)
      case _ => return None()
    }
  }

  def tokenize(args: ISZ[String], i: Z, tpe: String, sep: C, removeWhitespace: B): Option[ISZ[String]] = {
    if (i >= args.size) {
      reporter.error(None(), "OptionsCli", s"Expecting a sequence of $tpe separated by '$sep', but none found.")
      return None()
    }
    val arg = args(i)
    return Some(tokenizeH(arg, sep, removeWhitespace))
  }

  def tokenizeH(arg: String, sep: C, removeWhitespace: B): ISZ[String] = {
    val argCis = conversions.String.toCis(arg)
    var r = ISZ[String]()
    var cis = ISZ[C]()
    var j = 0
    while (j < argCis.size) {
      val c = argCis(j)
      if (c == sep) {
        r = r :+ conversions.String.fromCis(cis)
        cis = ISZ[C]()
      } else {
        val allowed: B = c match {
          case c"\n" => !removeWhitespace
          case c" " => !removeWhitespace
          case c"\r" => !removeWhitespace
          case c"\t" => !removeWhitespace
          case _ => T
        }
        if (allowed) {
          cis = cis :+ c
        }
      }
      j = j + 1
    }
    if (cis.size > 0) {
      r = r :+ conversions.String.fromCis(cis)
    }
    return r
  }

  def parseNumChoice(args: ISZ[String], i: Z, choices: ISZ[Z]): Option[Z] = {
    val set = HashSet.empty[Z] ++ choices
    parseNum(args, i, None(), None()) match {
      case r@Some(n) =>
        if (set.contains(n)) {
          return r
        } else {
          reporter.error(None(), "OptionsCli", s"Expecting one of the following: $set, but found $n.")
          return None()
        }
      case r => return r
    }
  }

  def parseNum(args: ISZ[String], i: Z, minOpt: Option[Z], maxOpt: Option[Z]): Option[Z] = {
    if (i >= args.size) {
      reporter.error(None(), "OptionsCli", s"Expecting an integer, but none found.")
      return None()
    }
    return parseNumH(F, args(i), minOpt, maxOpt)._2
  }

  def parseNumFlag(args: ISZ[String], i: Z, minOpt: Option[Z], maxOpt: Option[Z]): Option[Option[Z]] = {
    if (i >= args.size) {
      return Some(None())
    }
    parseNumH(T, args(i), minOpt, maxOpt) match {
      case (T, vOpt) => return Some(vOpt)
      case _ => return None()
    }
  }

  def parseNumH(optArg: B, arg: String, minOpt: Option[Z], maxOpt: Option[Z]): (B, Option[Z]) = {
    Z(arg) match {
      case Some(n) =>
        minOpt match {
          case Some(min) =>
            if (n < min) {
              reporter.error(None(), "OptionsCli", s"Expecting an integer at least $min, but found $n.")
              return (F, None())
            }
          case _ =>
        }
        maxOpt match {
          case Some(max) =>
            if (n > max) {
              reporter.error(None(), "OptionsCli", s"Expecting an integer at most $max, but found $n.")
              return (F, None())
            }
          case _ =>
        }
        return (T, Some(n))
      case _ =>
        if (!optArg) {
          reporter.error(None(), "OptionsCli", s"Expecting an integer, but found '$arg'.")
          return (F, None())
        } else {
          return (T, None())
       }
    }
  }

  def select(mode: String, args: ISZ[String], i: Z, choices: ISZ[String]): Option[String] = {
    val arg = args(i)
    var cs = ISZ[String]()
    for (c <- choices) {
      if (ops.StringOps(c).startsWith(arg)) {
        cs = cs :+ c
      }
    }
    cs.size match {
      case z"0" =>
        reporter.error(None(), "OptionsCli", s"$arg is not a mode of $mode.")
        return None()
      case z"1" => return Some(cs(0))
      case _ =>
        reporter.error(None(), "OptionsCli", 
          st"""Which one of the following modes did you mean by '$arg'?
              |${(cs, "\n")}""".render)
        return None()
    }
  }
}
// @formatter:on

// BEGIN USER CODE

// END USER CODE
