// #Sireum
/*
 Copyright (c) 2019, Robby, Kansas State University
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

  val logikaVerifier: Tool = Tool(
    name = "logikaVerifier",
    command = "verifier",
    description = "Logika verifier",
    header = "Logika Verifier for Slang",
    usage = "<option>* [<slang-file>]",
    opts = ISZ(
      Opt(name = "sat", longKey = "sat", shortKey = None(),
        tpe = Type.Flag(F),
        description = "Enable assumption satisfiability checking"),
      Opt(name = "sourcepath", longKey = "sourcepath", shortKey = Some('s'),
        tpe = Type.Path(T, None()),
        description = "Sourcepath of Slang .scala files"),
      Opt(name = "unroll", longKey = "unroll", shortKey = None(),
        tpe = Type.Flag(F),
        description = "Enable loop unrolling when loop modifies clause is unspecified"),
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
      OptGroup(name = "SMT2", opts = ISZ(
        Opt(name = "simplify", longKey = "simplify", shortKey = None(),
          tpe = Type.Flag(F),
          description = "Simplify SMT2 query"
        ),
        Opt(name = "solver", longKey = "solver", shortKey = Some('m'),
          tpe = Type.Choice(name = "LogikaSolver", sep = None(), elements = ISZ("all", "cvc4", "z3")),
          description = "Smt2 solver"
        ),
        Opt(name = "timeout", longKey = "timeout", shortKey = Some('t'),
          tpe = Type.Num(sep = None(), default = 2, min = Some(1), max = None()),
          description = "Timeout (seconds) for SMT2 solver"),
      )),
      OptGroup(name = "Optimizations", opts = ISZ(
        Opt(name = "par", longKey = "par", shortKey = Some('p'),
          tpe = Type.Flag(F),
          description = "Enable parallelization"),
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
      ))
    )
  )

  val group: Group = Group(
    name = "logika",
    description = "Logika toolset",
    header = "Logika Toolset for Slang",
    unlisted = T,
    subs = ISZ(logikaVerifier)
  )

}
