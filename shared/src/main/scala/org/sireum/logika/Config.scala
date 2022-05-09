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

@datatype class Config(val smt2Configs: ISZ[Smt2Config],
                       val sat: B,
                       val timeoutInMs: Z,
                       val defaultLoopBound: Z,
                       val loopBounds: HashMap[LoopId, Z],
                       val unroll: B,
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
                       val cvcRLimit: Z,
                       val fpRoundingMode: String,
                       val caching: B,
                       val smt2Seq: B)

@datatype trait Smt2Config {
  def name: String
  def exe: String
  def validOpts: ISZ[String]
  def satOpts: ISZ[String]
  @pure def args(isSat: B, timeoutInMs: Z): ISZ[String]
  @pure def updateOtherOpts(solverName: String, isSat: B, opts: ISZ[String]): Smt2Config
}

@datatype class Smt2Configs(val configs: ISZ[Smt2Config]) {
  @memoize def satArgs(timeoutInMs: Z): ISZ[String] = {
    var r = ISZ[String]()
    for (config <- configs) {
      r = (r :+ config.exe) ++ config.args(T, timeoutInMs)
    }
    return r
  }

  @memoize def validArgs(timeoutInMs: Z): ISZ[String] = {
    var r = ISZ[String]()
    for (config <- configs) {
      r = (r :+ config.exe) ++ config.args(F, timeoutInMs)
    }
    return r
  }
}

@datatype class Z3Config(val exe: String, val validOpts: ISZ[String], val satOpts: ISZ[String]) extends Smt2Config {
  val name: String = "z3"

  @pure def args(isSat: B, timeoutInMs: Z): ISZ[String] = {
    return ISZ[String]("-smt2", "-in", s"-t:$timeoutInMs") ++ (if (isSat) satOpts else validOpts)
  }

  @strictpure def updateOtherOpts(solverName: String, isSat: B, newOpts: ISZ[String]): Z3Config =
    if (name == solverName) Z3Config(exe, if (isSat) validOpts else newOpts, if (isSat) newOpts else satOpts) else this
}

@datatype class CvcConfig(val exe: String, val validOpts: ISZ[String], val satOpts: ISZ[String], val rlimit: Z) extends Smt2Config {
  val name: String = "cvc"

  @pure def args(isSat: B, timeoutInMs: Z): ISZ[String] = {
    return ISZ[String]("--lang=smt2.6", s"--tlimit=$timeoutInMs", s"--rlimit=$rlimit") ++ (if (isSat) satOpts else validOpts)
  }

  @strictpure def updateOtherOpts(solverName: String, isSat: B, newOpts: ISZ[String]): CvcConfig =
    if (name == solverName) CvcConfig(exe, if (isSat) validOpts else newOpts, if (isSat) newOpts else satOpts, rlimit) else this
}


@datatype class LoopId(val ids: ISZ[String])