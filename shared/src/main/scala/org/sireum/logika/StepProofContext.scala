// #Sireum
/*
 Copyright (c) 2021, Robby, Kansas State University
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
import org.sireum.lang.{ast => AST}

@datatype trait StepProofContext {
  @pure def stepNo: Z
}

object StepProofContext {

  @datatype class Regular(val stepNo: Z,
                          val exp: AST.Exp,
                          val claims: ISZ[State.Claim]) extends StepProofContext

  @datatype class SubProof(val stepNo: Z,
                           val subProof: AST.ProofAst.Step.SubProof) extends StepProofContext

  @datatype class FreshSubProof(val stepNo: Z,
                                val params: ISZ[AST.ProofAst.Step.Let.Param],
                                val steps: ISZ[AST.ProofAst.Step]) extends StepProofContext

  @datatype class FreshPredSubProof(val stepNo: Z,
                                    val params: ISZ[AST.ProofAst.Step.Let.Param],
                                    val exp: AST.Exp,
                                    val steps: ISZ[AST.ProofAst.Step]) extends StepProofContext

}
