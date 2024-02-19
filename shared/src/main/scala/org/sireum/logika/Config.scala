// #Sireum
/*
 Copyright (c) 2017-2024, Robby, Kansas State University
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

@datatype class Config(val smt2Configs: ISZ[Smt2Config],
                       val parCores: Z,
                       val sat: B,
                       val rlimit: Z,
                       val timeoutInMs: Z,
                       val charBitWidth: Z,
                       val intBitWidth: Z,
                       val useReal: B,
                       val logPc: B,
                       val logRawPc: B,
                       val logVc: B,
                       val logVcDirOpt: Option[String],
                       val dontSplitPfq: B,
                       val splitAll: B,
                       val splitIf: B,
                       val splitMatch: B,
                       val splitContract: B,
                       val simplifiedQuery: B,
                       val checkInfeasiblePatternMatch: B,
                       val fpRoundingMode: String,
                       val smt2Caching: B,
                       val smt2Seq: B,
                       val branchPar: Config.BranchPar.Type,
                       val atLinesFresh: B,
                       val interp: B,
                       val loopBound: Z,
                       val callBound: Z,
                       val interpContracts: B,
                       val elideEncoding: B,
                       val rawInscription: B,
                       val strictPureMode: Config.StrictPureMode.Type,
                       val transitionCache: B,
                       val patternExhaustive: B,
                       val pureFun: B,
                       val detailedInfo: B,
                       val satTimeout: B,
                       val isAuto: B,
                       val background: Config.BackgroundMode.Type,
                       val atRewrite: B,
                       val searchPc: B,
                       val rwTrace: B,
                       val rwMax: Z,
                       val rwPar: B,
                       val rwEvalTrace: B) {

  @memoize def fingerprint: U64 = {
    return ops.StringOps(string).sha3U64(T, T)
  }
}

object Config {
  @enum object BranchPar {
    "Disabled"
    "OnlyAllReturns"
    "All"
  }

  @enum object StrictPureMode {
    "Default"
    "Flip"
    "Uninterpreted"
  }

  @enum object BackgroundMode {
    "Type"
    "Save"
    "Disabled"
  }
}

@datatype class Smt2Config(val isSat: B, val name: String, val exe: String, val opts: ISZ[String])

@datatype class LoopId(val ids: ISZ[String])