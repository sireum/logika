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

@msig trait Smt2 {

  def timeoutInSeconds: Z

  def checkSat(query: String): B

  def checkUnsat(query: String): B

  def sat(title: String, claims: ISZ[State.Claim]): B = {
    val headers = st"Satisfiability Check for $title:" +: (for (c <- claims) yield c.toST)
    checkSat(satQuery(headers, claims).render)
  }

  @pure def satQuery(headers: ISZ[ST], claims: ISZ[State.Claim]): ST = {
    val decls: ISZ[ST] = (HashSMap.empty[String, ST] ++ (for (c <- claims; p <- c.toSmt2DeclMem.entries) yield p)).values
    return query(headers, decls, for (c <- claims) yield c.toSmt2Mem)
  }

  def valid(title: String, premises: ISZ[State.Claim], conclusion: State.Claim): B = {
    val headers = st"Validity Check for $title:" +: (for (c <- premises) yield c.toST) :+ st"  ⊢" :+ conclusion.toST
    checkUnsat(satQuery(headers, premises :+ State.Claim.Neg(conclusion)).render)
  }

  @pure def query(headers: ISZ[ST], decls: ISZ[ST], claims: ISZ[ST]): ST = {
    return st"""${(for (header <- headers; line <- ops.StringOps(header.render).split(c => c == '\n')) yield st"; $line", "\n")}
               |;
               |(define-sort   B            ()           Bool)
               |(define-sort   C            ()           String)
               |(define-sort   Z            ()           Int)
               |(define-sort   Z8           ()           Int)
               |(define-sort   Z16          ()           Int)
               |(define-sort   Z32          ()           Int)
               |(define-sort   Z64          ()           Int)
               |(define-sort   N            ()           Int)
               |(define-sort   N8           ()           Int)
               |(define-sort   N16          ()           Int)
               |(define-sort   N32          ()           Int)
               |(define-sort   N64          ()           Int)
               |(define-sort   S8           ()           (_ BitVec 8))
               |(define-sort   S16          ()           (_ BitVec 16))
               |(define-sort   S32          ()           (_ BitVec 32))
               |(define-sort   S64          ()           (_ BitVec 64))
               |(define-sort   U8           ()           (_ BitVec 8))
               |(define-sort   U16          ()           (_ BitVec 16))
               |(define-sort   U32          ()           (_ BitVec 32))
               |(define-sort   U64          ()           (_ BitVec 64))
               |(define-sort   R            ()           Real)
               |(define-sort   F32          ()           Float32)
               |(define-sort   F64          ()           Float64)
               |(define-const  F32_PInf     (F32)        (_ +oo 8 24))
               |(define-const  F32_NInf     (F32)        (_ -oo 8 24))
               |(define-const  F32_NaN      (F32)        (_ NaN 8 24))
               |(define-const  F64_PInf     (F64)        (_ +oo 11 53))
               |(define-const  F64_NInf     (F64)        (_ -oo 11 53))
               |(define-const  F64_NaN      (F64)        (_ NaN 11 53))
               |
               |(define-sort   IS           (I T)        (Array I T))
               |(define-sort   MS           (I T)        (Array I T))
               |(define-sort   ISInt        (T)          (Seq T))
               |(define-sort   MSInt        (T)          (Seq T))
               |
               |(declare-sort  Type)
               |(declare-fun   sub-type     (Type Type)  Bool)
               |(define-fun    leaf-type    ((x Type))   Bool
               |                  (forall ((y Type)) (=> (sub-type y x) (= y x))))
               |(assert        (forall ((x Type))
               |                  (sub-type x x)))
               |(assert        (forall ((x Type) (y Type) (z Type))
               |                  (=> (and (sub-type x y) (sub-type y z)) (sub-type x z))))
               |(assert        (forall ((x Type) (y Type))
               |                  (=> (and (sub-type x y) (sub-type y x)) (= x y))))
               |
               |(define-sort   Address      ()           Int)
               |(declare-fun   type-of      (Address)    Type)
               |
               |${(decls, "\n")}
               |
               |${(for (a <- claims) yield st"(assert $a)", "\n")}
               |
               |(check-sat)
               |(exit)"""
  }
}
