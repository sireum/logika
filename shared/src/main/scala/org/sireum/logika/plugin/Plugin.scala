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
package org.sireum.logika.plugin

import org.sireum._
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}
import org.sireum.logika.{Context, Logika, Smt2, State, StepProofContext}
import org.sireum.logika.Logika.Reporter

object Plugin {
  @datatype class Result(val status: B,
                         val nextFresh: Z,
                         val claims: ISZ[State.Claim])

  @strictpure def stepNoDesc(cap: B, stepId: AST.ProofAst.StepId): ST =
    stepId match {
      case stepId: AST.ProofAst.StepId.Num =>
        if (cap) if (stepId.no < 0) st"The method's premise #${-stepId.no}" else st"Proof step $stepId"
        else if (stepId.no < 0) st"the method's premise #${-stepId.no}" else st"proof step $stepId"
      case _ => if (cap) st"Proof step $stepId" else st"proof step $stepId"
    }

  @strictpure def claimPlugins(plugins: ISZ[Plugin]): ISZ[ClaimPlugin] =
    for (p <- plugins if p.isInstanceOf[ClaimPlugin]) yield p.asInstanceOf[ClaimPlugin]
}

@sig trait Plugin {
  @pure def name: String
}

@sig trait JustificationPlugin extends Plugin {

  @pure def canHandle(logika: Logika, just: AST.ProofAst.Step.Justification): B

  def handle(logika: Logika,
             smt2: Smt2,
             cache: Logika.Cache,
             spcMap: HashSMap[AST.ProofAst.StepId, StepProofContext],
             state: State,
             step: AST.ProofAst.Step.Regular,
             reporter: Reporter): Plugin.Result
}

@sig trait ExpPlugin extends Plugin {

  @pure def canHandle(logika: Logika, exp: AST.Exp): B

  def handle(logika: Logika,
             split: Logika.Split.Type,
             smt2: Smt2,
             cache: Logika.Cache,
             rtCheck: B,
             state: State,
             exp: AST.Exp,
             reporter: Reporter): ISZ[(State, State.Value)]

}

@sig trait StmtPlugin extends Plugin {

  @pure def canHandle(logika: Logika, stmt: AST.Stmt): B

  def handle(logika: Logika,
             split: Logika.Split.Type,
             smt2: Smt2,
             cache: Logika.Cache,
             rtCheck: B,
             state: State,
             stmt: AST.Stmt,
             reporter: Reporter): ISZ[State]
}

@sig trait MethodPlugin extends Plugin {

  @pure def canHandle(th: TypeHierarchy, stmt: AST.Stmt.Method): B

  def handle(th: TypeHierarchy,
             plugins: ISZ[Plugin],
             stmt: AST.Stmt.Method,
             caseIndex: Z,
             config: logika.Config,
             smt2: Smt2,
             cache: Logika.Cache,
             reporter: Reporter): B

  @pure def canHandleCompositional(th: TypeHierarchy, info: Context.InvokeMethodInfo): B

  def handleCompositional(logika: Logika, smt2: Smt2, cache: Logika.Cache, rtCheck: B, split: Logika.Split.Type,
                          posOpt: Option[message.Position], info: Context.InvokeMethodInfo,
                          state: State, typeSubstMap: HashMap[String, AST.Typed], retType: AST.Typed,
                          invokeReceiverOpt: Option[AST.Exp], receiverOpt: Option[State.Value.Sym],
                          paramArgs: ISZ[(AST.ResolvedInfo.LocalVar, AST.Typed, AST.Exp, State.Value)],
                          reporter: Reporter): ISZ[(State, State.Value)]
}


@sig trait StmtsPlugin extends Plugin {

  @pure def canHandle(th: TypeHierarchy, stmts: ISZ[AST.Stmt.Method]): B

  def handle(th: TypeHierarchy,
             plugins: ISZ[Plugin],
             stmts: ISZ[AST.Stmt],
             config: logika.Config,
             smt2: Smt2,
             cache: Logika.Cache,
             reporter: Reporter): (B, ISZ[State])

}

@sig trait ClaimPlugin extends Plugin {

  @pure def canHandleExp(claim: State.Claim): B

  @pure def handleExp(cs2es: logika.Util.ClaimsToExps, claim: State.Claim): Option[AST.Exp]

  @pure def canHandleDeclSmt2(claim: State.Claim): B

  @pure def canHandleSmt2(rhs: B, claim: State.Claim): B

  @pure def handleDeclSmt2(smt2: Smt2, claim: State.Claim): ISZ[(String, ST)]

  @pure def handleSmt2(smt2: Smt2,
                       claim: State.Claim, v2st: (State.Value, Reporter) => ST,
                       lets: HashMap[Z, ISZ[State.Claim.Let]],
                       declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
                       reporter: Reporter): Option[ST]

  @pure def canHandleSymRewrite(data: State.Claim.Data): B

  @pure def handleSymRewrite(rw: logika.Util.SymAddRewriter, data: State.Claim.Data): MOption[State.Claim.Data]
}