// #Sireum
/*
 Copyright (c) 2020, Robby, Kansas State University
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

@datatype class Config(smt2Configs: ISZ[Smt2Config],
                       sat: B,
                       timeoutInMs: Z,
                       defaultLoopBound: Z,
                       loopBounds: HashMap[LoopId, Z],
                       unroll: B,
                       charBitWidth: Z,
                       intBitWidth: Z,
                       logPc: B,
                       logRawPc: B,
                       logVc: B,
                       logVcDirOpt: Option[String],
                       dontSplitPfq: B,
                       splitAll: B,
                       splitIf: B,
                       splitMatch: B,
                       splitContract: B,
                       simplifiedQuery: B)

@datatype trait Smt2Config {
  def name: String
  def exe: String
  @pure def args(timeoutInMs: Z): ISZ[String]
}

@datatype class Z3Config(val exe: String) extends Smt2Config {
  val name: String = "z3"

  @pure def args(timeoutInMs: Z): ISZ[String] = {
    return ISZ("-smt2", s"-t:$timeoutInMs", "-in")
  }
}

@datatype class Cvc4Config(val exe: String) extends Smt2Config {
  val name: String = "cvc4"

  @pure def args(timeoutInMs: Z): ISZ[String] = {
    return ISZ(s"--tlimit=$timeoutInMs", "--lang=smt2.6")
  }
}


@datatype class LoopId(ids: ISZ[String])