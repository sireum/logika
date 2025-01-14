// #Sireum
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

package org.sireum.logika

import org.sireum._
import org.sireum.cli.CliOpt._

object cli {

  val modeOpt: Opt = Opt(name = "manual", longKey = "manual", shortKey = Some('m'),
    tpe = Type.Flag(F),
    description = "Set verification mode to manual for Slang scripts")

  val parOpt: Opt = Opt(name = "par", longKey = "par", shortKey = Some('p'),
    tpe = Type.NumFlag(100, Some(1), Some(100)),
    description = "Enable parallelization (with CPU cores percentage to use)")

  val logikaVerifier: Tool = Tool(
    name = "logikaVerifier",
    command = "verifier",
    description = "Logika verifier",
    header = "Logika Verifier for Slang",
    usage = "<option>* <slang-file>+",
    usageDescOpt = None(),
    opts = ISZ(
      Opt(name = "feedback", longKey = "feedback", shortKey = None(),
        tpe = Type.Path(multiple = F, default = None()),
        description = "Feedback output directory"),
      modeOpt,
      Opt(name = "noRuntime", longKey = "no-runtime", shortKey = Some('r'),
        tpe = Type.Flag(F), description = "Do not use built-in runtime (use runtime in sourcepath)"),
      Opt(name = "parseableMessages", longKey = "parseable-messages", shortKey = None(),
        tpe = Type.Flag(F),
        description = "Print parseable file messages"),
      Opt(name = "sourcepath", longKey = "sourcepath", shortKey = Some('s'),
        tpe = Type.Path(T, None()),
        description = "Sourcepath of Slang .scala files")
    ),
    groups = ISZ(
      OptGroup(name = "Additional Verifications", opts = ISZ(
        Opt(name = "infoFlow", longKey = "info-flow", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Enable information flow verification")
      )),
      OptGroup(name = "Approximation", opts = ISZ(
        Opt(name = "charBitWidth", longKey = "c-bitwidth", shortKey = None(),
          tpe = Type.Num(sep = None(), default = 32, min = None(), max = None()),
          description = "Bit-width representation for C (character) values (expected 8, 16, or 32)"),
        Opt(name = "fpRounding", longKey = "fp-rounding", shortKey = None(),
          tpe = Type.Choice(name = "FPRoundingMode", sep = None(), elements = ISZ(
            "NearestTiesToEven", "NearestTiesToAway", "TowardPositive", "TowardNegative", "TowardZero")),
          description = "Rounding mode for floating point numbers"),
        Opt(name = "useReal", longKey = "use-real", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Use reals to approximate floating-point numbers"),
        Opt(name = "intBitWidth", longKey = "z-bitwidth", shortKey = None(),
          tpe = Type.Num(sep = None(), default = 0, min = None(), max = None()),
          description = "Bit-width representation for Z (integer) values (expected 0, 8, 16, 32, 64)")
      )),
      OptGroup(name = "Control", opts = ISZ(
        Opt(name = "interprocedural", longKey = "interprocedural", shortKey = None(),
          tpe = Type.Flag(F), description = "Enable inter-procedural verification on non-strict-pure methods"),
        Opt(name = "interproceduralContracts", longKey = "interprocedural-contracts", shortKey = None(),
          tpe = Type.Flag(F), description = "Use contracts in inter-procedural verification"),
        Opt(name = "strictPureMode", longKey = "strictpure-mode", shortKey = None(),
          tpe = Type.Choice("StrictPureMode", None(), ISZ("default", "flip", "uninterpreted")),
          description = "Strict-pure method treatment mode in compositional/interprocedural verification"),
        Opt(name = "line", longKey = "line", shortKey = None(),
          tpe = Type.Num(None(), 0, Some(0), None()),
          description = "Focus verification to the specified program line number"),
        Opt(name = "loopBound", longKey = "loop-bound", shortKey = None(),
          tpe = Type.Num(None(), 3, Some(1), None()),
          description = "Loop bound for inter-procedural verification"),
        Opt(name = "callBound", longKey = "recursive-bound", shortKey = None(),
          tpe = Type.Num(None(), 3, Some(1), None()),
          description = "Recursive call-chain bound for inter-procedural verification"),
        Opt(name = "patternExhaustive", longKey = "pattern-inexhaustive", shortKey = None(),
          tpe = Type.Flag(T),
          description = "Disable pattern exhaustiveness checking"),
        Opt(name = "pureFun", longKey = "pure-proof-fun", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Always add proof functions for pure methods"),
        Opt(name = "sat", longKey = "sat", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Enable assumption satisfiability checking"),
        Opt(name = "skipMethods", longKey = "skip-methods", shortKey = None(),
          tpe = Type.Str(Some(','), None()),
          description = "Skip checking methods with the specified fully-qualified names or identifiers"),
        Opt(name = "skipTypes", longKey = "skip-types", shortKey = None(),
          tpe = Type.Str(Some(','), None()),
          description = "Skip checking traits, classes, and objects with the specified fully-qualified names or identifiers")
      )),
      OptGroup(name = "Logging", opts = ISZ(
        Opt(name = "logPc", longKey = "log-pc", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display path conditions before each statement"),
        Opt(name = "logPcLines", longKey = "log-pc-lines", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display At(...) path condition line numbers and unique symbolic value numbering"),
        Opt(name = "logRawPc", longKey = "log-raw-pc", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display raw path conditions before each statement"),
        Opt(name = "logVc", longKey = "log-vc", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display all verification conditions"),
        Opt(name = "logVcDir", longKey = "log-vc-dir", shortKey = None(),
          tpe = Type.Path(F, None()),
          description = "Write all verification conditions in a directory"),
        Opt(name = "logDetailedInfo", longKey = "log-detailed-info", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display detailed feedback information"),
        Opt(name = "logAtRewrite", longKey = "log-rewrite-at", shortKey = None(),
          tpe = Type.Flag(T),
          description = "Disable At(...) rewriting as In(...)/Old(...) in symexe mode"),
        Opt(name = "stats", longKey = "stats", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Collect verification statistics")
      )),
      OptGroup(name = "Optimizations", opts = ISZ(
        parOpt,
        Opt(name = "branchPar", longKey = "par-branch", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Enable branch parallelization"),
        Opt(name = "branchParReturn", longKey = "par-branch-return", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Only use branch parallelization if all branches return"),
        Opt(name = "branchPredNum", longKey = "par-branch-pred-num", shortKey = None(),
          tpe = Type.Num(sep = None(), default = 2, min = Some(2), max = None()),
          description = "Branch parallelization prediction minimum number of branches"),
        Opt(name = "branchPredComplexity", longKey = "par-branch-pred-complexity", shortKey = None(),
          tpe = Type.Num(sep = None(), default = 10, min = Some(0), max = None()),
          description = "Branch parallelization prediction statement complexity"),
        Opt(name = "rwPar", longKey = "par-rw", shortKey = None(),
          tpe = Type.Flag(T),
          description = "Enable rewriting parallelization")
      )),
      OptGroup(name = "Path Splitting", opts = ISZ(
        Opt(name = "dontSplitFunQuant", longKey = "dont-split-pfq", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Do not force splitting in quantifiers and proof functions derived from @strictpure methods"),
        Opt(name = "splitAll", longKey = "split-all", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Split all"),
        Opt(name = "splitContract", longKey = "split-contract", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Split on contract cases"),
        Opt(name = "splitIf", longKey = "split-if", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Split on if-conditional expressions and statements"),
        Opt(name = "splitMatch", longKey = "split-match", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Split on match expressions and statements")
      )),
      OptGroup(name = "Rewriting", opts = ISZ(
        Opt(name = "rwMax", longKey = "rw-max", shortKey = None(),
          tpe = Type.Num(None(), 100, Some(1), None()),
          description = "Maximum number of rewriting"),
        Opt(name = "rwTrace", longKey = "rw-trace", shortKey = None(),
          tpe = Type.Flag(T),
          description = "Disable rewriting trace"),
        Opt(name = "rwEvalTrace", longKey = "rw-eval-trace", shortKey = None(),
          tpe = Type.Flag(T),
          description = "Disable evaluation rewriting trace")
      )),
      OptGroup(name = "SMT2", opts = ISZ(
        Opt(name = "elideEncoding", longKey = "elide-encoding", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Strip out SMT2 encoding in feedback"),
        Opt(name = "rawInscription", longKey = "raw-inscription", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Use raw sequent/sat preamble inscription"),
        Opt(name = "rlimit", longKey = "rlimit", shortKey = None(),
          tpe = Type.Num(None(), Smt2.rlimit, Some(0), None()),
          description = "SMT2 solver resource limit"
        ),
        Opt(name = "sequential", longKey = "smt2-seq", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Disable SMT2 solvers parallelization"
        ),
        Opt(name = "simplify", longKey = "simplify", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Simplify SMT2 query (experimental)"
        ),
        Opt(name = "smt2SatConfigs", longKey = "solver-sat", shortKey = None(),
          tpe = Type.Str(None(), Some(logika.Smt2.defaultSatOpts)),
          description = "SMT2 configurations for satisfiability queries"
        ),
        Opt(name = "smt2ValidConfigs", longKey = "solver-valid", shortKey = None(),
          tpe = Type.Str(None(), Some(logika.Smt2.defaultValidOpts)),
          description = "SMT2 configurations for validity queries"
        ),
        Opt(name = "satTimeout", longKey = "sat-timeout", shortKey = None(),
          tpe = Type.Flag(F),
          description = s"Use validity checking timeout for satisfiability checking (otherwise: ${Smt2.satTimeoutInMs}ms)"
        ),
        Opt(name = "timeout", longKey = "timeout", shortKey = Some('t'),
          tpe = Type.Num(sep = None(), default = 2, min = Some(1), max = None()),
          description = "Timeout (seconds) for validity checking"
        ),
        Opt(name = "searchPC", longKey = "search-pc", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Search path conditions first before employing SMT2 solvers when discharging VCs")
      ))
    )
  )

  val logikaConfig: Tool = Tool(
    name = "logikaConfig",
    command = "config",
    description = "Logika Config",
    header = "Sireum Logika Config",
    usage = "<option>* <file.sc>",
    usageDescOpt = None(),
    opts = ISZ(
      Opt(name = "theme", longKey = "theme", shortKey = Some('t'),
        tpe = Type.Choice(name = "Theme", sep = None(), elements = ISZ("dark", "light")),
        description = "Form color theme")
    ),
    groups = ISZ()
  )


  val group: Group = Group(
    name = "logika",
    description = "Logika tools",
    header = "Logika Tools for Slang",
    unlisted = F,
    subs = ISZ(logikaConfig, logikaVerifier)
  )

}
