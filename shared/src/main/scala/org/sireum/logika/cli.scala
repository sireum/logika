// #Sireum
/*
 Copyright (c) 2017-2021, Robby, Kansas State University
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
      Opt(name = "noRuntime", longKey = "no-runtime", shortKey = Some('r'),
        tpe = Type.Flag(F), description = "Do not use built-in runtime (use runtime in sourcepath)"),
      Opt(name = "sourcepath", longKey = "sourcepath", shortKey = Some('s'),
        tpe = Type.Path(T, None()),
        description = "Sourcepath of Slang .scala files"),
    ),
    groups = ISZ(
      OptGroup(name = "Bit-width", opts = ISZ(
        Opt(name = "charBitWidth", longKey = "c-bitwidth", shortKey = None(),
          tpe = Type.Num(sep = None(), default = 32, min = None(), max = None()),
          description = "Bit-width representation for C (character) values (expected 8, 16, or 32)"),
        Opt(name = "intBitWidth", longKey = "z-bitwidth", shortKey = None(),
          tpe = Type.Num(sep = None(), default = 0, min = None(), max = None()),
          description = "Bit-width representation for Z (integer) values (expected 0, 8, 16, 32, 64)")
      )),
      OptGroup(name = "Control", opts = ISZ(
        Opt(name = "line", longKey = "line", shortKey = None(),
          tpe = Type.Num(None(), 0, Some(0), None()),
          description = "Focus verification to the specified program line number"),
        Opt(name = "sat", longKey = "sat", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Enable assumption satisfiability checking"),
        Opt(name = "skipMethods", longKey = "skip-methods", shortKey = None(),
          tpe = Type.Str(Some(','), None()),
          description = "Skip checking methods with the specified fully-qualified names or identifiers"),
        Opt(name = "skipTypes", longKey = "skip-types", shortKey = None(),
          tpe = Type.Str(Some(','), None()),
          description = "Skip checking traits, classes, and objects with the specified fully-qualified names or identifiers"),
        Opt(name = "unroll", longKey = "unroll", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Enable loop unrolling when loop modifies clause is unspecified"),
      )),
      OptGroup(name = "Logging", opts = ISZ(
        Opt(name = "logPc", longKey = "log-pc", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display path conditions before each statement"),
        Opt(name = "logRawPc", longKey = "log-raw-pc", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display raw path conditions before each statement"),
        Opt(name = "logVc", longKey = "log-vc", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Display all verification conditions"),
        Opt(name = "logVcDir", longKey = "log-vc-dir", shortKey = None(),
          tpe = Type.Path(F, None()),
          description = "Write all verification conditions in a directory"),
      )),
      OptGroup(name = "Optimizations", opts = ISZ(
        Opt(name = "par", longKey = "par", shortKey = Some('p'),
          tpe = Type.NumFlag(100, Some(1), Some(100)),
          description = "Enable parallelization (with CPU cores percentage to use)"),
        Opt(name = "ramFolder", longKey = "ram-folder", shortKey = None(),
          tpe = Type.Path(F, None()),
          description = "RAM folder to temporarily store various artifacts (e.g., SMT2 solvers)"),
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
          description = "Split on match expressions and statements"),
      )),
      OptGroup(name = "SMT2", opts = ISZ(
        Opt(name = "cvc4RLimit", longKey = "cvc4-rlimit", shortKey = None(),
          tpe = Type.Num(None(), 1000000, None(), None()),
          description = "CVC4 rlimit"
        ),
        Opt(name = "cvc4VOpts", longKey = "cvc4-vopts", shortKey = None(),
          tpe = Type.Str(Some(','), Some("--full-saturate-quant")),
          description = "Additional options for CVC4 validity checks"
        ),
        Opt(name = "cvc4SOpts", longKey = "cvc4-sopts", shortKey = None(),
          tpe = Type.Str(Some(','), None() /*Some("--finite-model-find")*/),
          description = "Additional options for CVC4 satisfiability checks"
        ),
        Opt(name = "simplify", longKey = "simplify", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Simplify SMT2 query"
        ),
        Opt(name = "solver", longKey = "solver", shortKey = Some('m'),
          tpe = Type.Choice(name = "LogikaSolver", sep = None(), elements = ISZ("all", "cvc4", "z3")),
          description = "SMT2 solver"
        ),
        Opt(name = "timeout", longKey = "timeout", shortKey = Some('t'),
          tpe = Type.Num(sep = None(), default = 2, min = Some(1), max = None()),
          description = "Timeout (seconds) for SMT2 solver"
        ),
        Opt(name = "z3VOpts", longKey = "z3-vopts", shortKey = None(),
          tpe = Type.Str(Some(','), None()),
          description = "Additional options for Z3 validity checks"
        ),
        Opt(name = "z3SOpts", longKey = "z3-sopts", shortKey = None(),
          tpe = Type.Str(Some(','), None()),
          description = "Additional options for Z3 satisfiability checks"
        ),
      )),
    )
  )

  val group: Group = Group(
    name = "logika",
    description = "Logika tools",
    header = "Logika Tools for Slang",
    unlisted = F,
    subs = ISZ(logikaVerifier)
  )

}
