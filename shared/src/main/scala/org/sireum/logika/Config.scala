// #Sireum
/*
 Copyright (c) 2017-2023, Robby, Kansas State University
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
                       val caching: B,
                       val smt2Seq: B,
                       val branchPar: Config.BranchPar.Type,
                       val branchParCores: Z,
                       val atLinesFresh: B,
                       val interp: B,
                       val loopBound: Z,
                       val callBound: Z,
                       val interpContracts: B,
                       val elideEncoding: B,
                       val rawInscription: B,
                       val flipStrictPure: B,
                       val transitionCache: B) {

  @memoize def fingerprint: U64 = {
    val digest = ops.StringOps(string).sha3(T, T)
    return (conversions.U8.toU64(digest(0)) & U64.fromZ(0xFF)) << U64.fromZ(56) |
      (conversions.U8.toU64(digest(1)) & U64.fromZ(0xFF)) << U64.fromZ(48) |
      (conversions.U8.toU64(digest(2)) & U64.fromZ(0xFF)) << U64.fromZ(40) |
      (conversions.U8.toU64(digest(3)) & U64.fromZ(0xFF)) << U64.fromZ(32) |
      (conversions.U8.toU64(digest(4)) & U64.fromZ(0xFF)) << U64.fromZ(24) |
      (conversions.U8.toU64(digest(5)) & U64.fromZ(0xFF)) << U64.fromZ(16) |
      (conversions.U8.toU64(digest(6)) & U64.fromZ(0xFF)) << U64.fromZ(8) |
      (conversions.U8.toU64(digest(7)) & U64.fromZ(0xFF))
  }
}

object Config {
  @enum object BranchPar {
    "Disabled"
    "OnlyAllReturns"
    "All"
  }
}

@datatype class Smt2Config(val isSat: B, val name: String, val exe: String, val rlimit: Z, val opts: ISZ[String])

@datatype class LoopId(val ids: ISZ[String])