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

object Z3 {
  object Result {
    @enum object Kind {
      'Sat
      'Unsat
      'Unknown
      'Timeout
      'Error
    }
  }

  @datatype class Result(kind: Result.Kind.Type, output: String)

}

@record class Z3 extends Smt2 {

  def checkSat(query: String, timeoutInSeconds: Z): B = {
    return checkQuery(query, timeoutInSeconds).kind == Z3.Result.Kind.Sat
  }

  def checkUnsat(query: String, timeoutInSeconds: Z): B = {
    return checkQuery(query, timeoutInSeconds).kind == Z3.Result.Kind.Unsat
  }

  def checkQuery(query: String, timeoutInSeconds: Z): Z3.Result = {
    //println(s"Z3 Query:")
    //println(query)
    val pr = Os.proc(ISZ("z3", "-smt2", s"-T:$timeoutInSeconds", "-in")).input(query).redirectErr.run()
    val firstLine = ops.StringOps(pr.out).split(c => c == '\n' || c == '\r')(0)
    val r: Z3.Result = firstLine match {
      case string"sat" => Z3.Result(Z3.Result.Kind.Sat, pr.out)
      case string"unsat" => Z3.Result(Z3.Result.Kind.Unsat, pr.out)
      case string"timeout" => Z3.Result(Z3.Result.Kind.Timeout, pr.out)
      case string"unknown" => Z3.Result(Z3.Result.Kind.Unknown, pr.out)
      case _ => Z3.Result(Z3.Result.Kind.Error, pr.out)
    }
    //println(s"Z3 Result (${r.kind}):")
    //println(r.output)
    if (r.kind == Z3.Result.Kind.Error) {
      halt(
        st"""Error encountered when running Z3 query:
                |$query
                |
                |Z3 output:
                |${r.output}""".render)
    }

    return r
  }
}
