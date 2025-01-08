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
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}

@datatype trait StepProofContext {
  @pure def stepNo: AST.ProofAst.StepId
  @strictpure def prettyST: ST
  override def string: String = {
    return prettyST.render
  }
}

object StepProofContext {

  @datatype class Regular(val th: TypeHierarchy,
                          val stepNo: AST.ProofAst.StepId,
                          val exp: AST.Exp) extends StepProofContext {
    @strictpure override def prettyST: ST = st"(${stepNo.prettyST}, ${exp.prettyST})"
    @memoize def coreExpClaim: AST.CoreExp.Base = {
      return th.translateToBaseCoreExp(exp, F)
    }
  }

  @datatype class SubProof(val stepNo: AST.ProofAst.StepId,
                           val assumption: AST.Exp,
                           val claims: ISZ[AST.Exp],
                           val spcs: ISZ[StepProofContext]) extends StepProofContext {
    @strictpure override def prettyST: ST = st"(${stepNo.prettyST}, ${assumption.prettyST}, ${(for (claim <- claims) yield claim.prettyST, ", ")})"
  }

  @datatype class FreshSubProof(val stepNo: AST.ProofAst.StepId,
                                val context: ISZ[String],
                                val params: ISZ[AST.ProofAst.Step.Let.Param],
                                val claims: ISZ[AST.Exp],
                                val spcs: ISZ[StepProofContext]) extends StepProofContext {
    @strictpure override def prettyST: ST = st"(${stepNo.prettyST}, ${(for (param <- params) yield param.prettyST, ", ")}, ${(for (claim <- claims) yield claim.prettyST, ", ")})"
  }

  @datatype class FreshAssumeSubProof(val stepNo: AST.ProofAst.StepId,
                                      val context: ISZ[String],
                                      val params: ISZ[AST.ProofAst.Step.Let.Param],
                                      val assumption: AST.Exp,
                                      val claims: ISZ[AST.Exp],
                                      val spcs: ISZ[StepProofContext]) extends StepProofContext {
    @strictpure override def prettyST: ST = st"(${stepNo.prettyST}, ${(for (param <- params) yield param.prettyST, ", ")}, ${assumption.prettyST}, ${(for (claim <- claims) yield claim.prettyST, ", ")})"
  }

}
