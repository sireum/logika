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
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.Logika.Reporter
import Util._

object Smt2 {
  @msig trait Cache {
    def get(isSat: B, query: String, args: ISZ[String]): Option[Smt2Query.Result]
    def set(isSat: B, query: String, args: ISZ[String], result: Smt2Query.Result): Unit
  }

  @record class NoCache extends Cache {
    def get(isSat: B, query: String, args: ISZ[String]): Option[Smt2Query.Result] = {
      return None()
    }
    def set(isSat: B, query: String, args: ISZ[String], result: Smt2Query.Result): Unit = {}
  }

  @datatype class SeqLit(val t: AST.Typed.Name, val size: Z)

  @datatype class AdtFieldInfo(val isParam: B,
                               val isSpec: B,
                               val fieldId: String,
                               val fieldLookupId: ST,
                               val fieldStoreId: ST,
                               val fieldTypeId: ST,
                               val fieldType: AST.Typed)

  @datatype class MemPrinter(val defs: HashMap[Z, ISZ[State.Claim.Let]]) {
  }

  val builtInCurrentNames: HashSet[ISZ[String]] = HashSet.empty[ISZ[String]] ++ ISZ[ISZ[String]](
    AST.Typed.f32Name :+ "NaN", AST.Typed.f32Name :+ "PInf", AST.Typed.f32Name :+ "NInf",
    AST.Typed.f64Name :+ "NaN", AST.Typed.f64Name :+ "PInf", AST.Typed.f64Name :+ "NInf",
  )

  val basicTypes: HashSet[AST.Typed] = HashSet ++ ISZ[AST.Typed](
    AST.Typed.b,
    AST.Typed.z,
    AST.Typed.c,
    AST.Typed.f32,
    AST.Typed.f64,
    AST.Typed.r,
    AST.Typed.string,
  )

  val imsOps: HashSet[String] =
    HashSet.empty[String] ++
      ISZ(
        AST.Exp.BinaryOp.Append,
        AST.Exp.BinaryOp.AppendAll,
        AST.Exp.BinaryOp.Prepend,
        AST.Exp.BinaryOp.RemoveAll,
      )

  val stTrue: ST = st"true"
  val stFalse: ST = st"false"
  val symPrefix: String = "cx!"

  @strictpure def cST(charBitWidth: Z): ST =
    st"""(define-sort C () (_ BitVec $charBitWidth))
        |(define-fun |C.unary_-| ((x C)) C (bvneg x))
        |(define-fun |C.unary_~| ((x C)) C (bvnot x))
        |(define-fun |C.<=| ((x C) (y C)) B (bvule x y))
        |(define-fun |C.<| ((x C) (y C)) B (bvult x y))
        |(define-fun |C.>| ((x C) (y C)) B (bvugt x y))
        |(define-fun |C.>=| ((x C) (y C)) B (bvuge x y))
        |(define-fun |C.==| ((x C) (y C)) B (= x y))
        |(define-fun |C.!=| ((x C) (y C)) B (not (= x y)))
        |(define-fun |C.+| ((x C) (y C)) C (bvadd x y))
        |(define-fun |C.-| ((x C) (y C)) C (bvsub x y))
        |(define-fun |C.*| ((x C) (y C)) C (bvmul x y))
        |(define-fun |C./| ((x C) (y C)) C (bvudiv x y))
        |(define-fun |C.%| ((x C) (y C)) C (bvurem x y))
        |(define-fun |C.<<| ((x C) (y C)) C (bvshl x y))
        |(define-fun |C.>>| ((x C) (y C)) C (bvlshr x y))
        |(define-fun |C.>>>| ((x C) (y C)) C (bvlshr x y))"""

  @strictpure def zST(intBitWidth: Z): ST =
    if (intBitWidth == 0)
      st"""(define-sort Z () Int)
          |(define-fun |Z.unary_-| ((x Z)) Z (- x))
          |(define-fun |Z.<=| ((x Z) (y Z)) B (<= x y))
          |(define-fun |Z.<| ((x Z) (y Z)) B (< x y))
          |(define-fun |Z.>| ((x Z) (y Z)) B (> x y))
          |(define-fun |Z.>=| ((x Z) (y Z)) B (>= x y))
          |(define-fun |Z.==| ((x Z) (y Z)) B (= x y))
          |(define-fun |Z.!=| ((x Z) (y Z)) B (not (= x y)))
          |(define-fun |Z.+| ((x Z) (y Z)) Z (+ x y))
          |(define-fun |Z.-| ((x Z) (y Z)) Z (- x y))
          |(define-fun |Z.*| ((x Z) (y Z)) Z (* x y))
          |(define-fun |Z./| ((x Z) (y Z)) Z (div x y))
          |(define-fun |Z.%| ((x Z) (y Z)) Z (mod x y))"""
    else
      st"""(define-sort Z () (_ BitVec $intBitWidth))
          |(define-fun |Z.unary_-| ((x Z)) Z (bvneg x))
          |(define-fun |Z.<=| ((x Z) (y Z)) B (bvsle x y))
          |(define-fun |Z.<| ((x Z) (y Z)) B (bvslt x y))
          |(define-fun |Z.>| ((x Z) (y Z)) B (bvsgt x y))
          |(define-fun |Z.>=| ((x Z) (y Z)) B (bvsge x y))
          |(define-fun |Z.==| ((x Z) (y Z)) B (= x y))
          |(define-fun |Z.!=| ((x Z) (y Z)) B (not (= x y)))
          |(define-fun |Z.+| ((x Z) (y Z)) Z (bvadd x y))
          |(define-fun |Z.-| ((x Z) (y Z)) Z (bvsub x y))
          |(define-fun |Z.*| ((x Z) (y Z)) Z (bvmul x y))
          |(define-fun |Z./| ((x Z) (y Z)) Z (bvsdiv x y))
          |(define-fun |Z.%| ((x Z) (y Z)) Z (bvsrem x y))"""

  val rST: ST =
    st"""(define-sort R () Real)
        |(define-fun |R.unary_-| ((x R)) R (- x))
        |(define-fun |R.<=| ((x R) (y R)) B (<= x y))
        |(define-fun |R.<| ((x R) (y R)) B (< x y))
        |(define-fun |R.>| ((x R) (y R)) B (> x y))
        |(define-fun |R.>=| ((x R) (y R)) B (>= x y))
        |(define-fun |R.==| ((x R) (y R)) B (= x y))
        |(define-fun |R.!=| ((x R) (y R)) B (not (= x y)))
        |(define-fun |R.+| ((x R) (y R)) R (+ x y))
        |(define-fun |R.-| ((x R) (y R)) R (- x y))
        |(define-fun |R.*| ((x R) (y R)) R (* x y))
        |(define-fun |R./| ((x R) (y R)) R (/ x y))"""

  @strictpure def quotedEscape(s: String): String = ops.StringOps(s).replaceAllChars('|', '│')

  val topPrefix: String = "_"

  val z3DefaultValidOpts: String = "z3"

  val z3DefaultSatOpts: String = "z3"

  val cvc4DefaultValidOpts: String = "cvc4,--full-saturate-quant"

  val cvc4DefaultSatOpts: String = "cvc4"

  val cvc5DefaultValidOpts: String = "cvc5,--full-saturate-quant"

  val cvc5DefaultSatOpts: String = "cvc5,--finite-model-find"

  val altErgoDefaultValidOpts: String = "alt-ergo"

  val altErgoDefaultSatOpts: String = "alt-ergo"

  val altErgoOpenDefaultValidOpts: String = "alt-ergo-open"

  val altErgoOpenDefaultSatOpts: String = "alt-ergo-open"

  val defaultValidOpts: String = s"$cvc4DefaultValidOpts; $z3DefaultValidOpts; $cvc5DefaultValidOpts"

  val defaultSatOpts: String = s"$cvc4DefaultSatOpts; $z3DefaultSatOpts; $cvc5DefaultSatOpts"

  val validTimeoutInMs: Z = 2000

  val satTimeoutInMs: Z = 500

  val rlimit: Z = 1000000

  def solverArgs(name: String, timeoutInMs: Z, rlimit: Z): Option[ISZ[String]] = {
    name match {
      case string"alt-ergo" =>
        var timeoutInS: Z = timeoutInMs / 1000
        if (timeoutInMs % 1000 != 0) {
          timeoutInS = timeoutInS + 1
        }
        return Some(ISZ("-default-lang", "smt2", "-use-fpa", "-steps-bound", rlimit.string, "-timelimit", timeoutInS.string))
      case string"alt-ergo-open" =>
        var timeoutInS: Z = timeoutInMs / 1000
        if (timeoutInMs % 1000 != 0) {
          timeoutInS = timeoutInS + 1
        }
        return Some(ISZ("-default-lang", "smt2", "-use-fpa", "-steps-bound", rlimit.string, "-timelimit", timeoutInS.string))
      case string"cvc4" => return Some(ISZ("--lang=smt2.6", s"--rlimit=$rlimit", s"--tlimit=$timeoutInMs"))
      case string"cvc5" => return Some(ISZ("--lang=smt2.6", s"--rlimit=$rlimit", s"--tlimit=$timeoutInMs"))
      case string"z3" => return Some(ISZ("-smt2", "-in", s"rlimit=$rlimit", s"-t:$timeoutInMs"))
      case _ => return None()
    }
  }

  def parseConfigs(nameExePathMap: HashMap[String, String],
                   isSat: B,
                   options: String,
                   timeoutInMs: Z,
                   rlimit: Z): Either[ISZ[Smt2Config], String] = {
    var r = ISZ[Smt2Config]()
    for (option <- ops.StringOps(options).split((c: C) => c === ';')) {
      val opts: ISZ[String] =
        for (e <- ops.StringOps(ops.StringOps(option).trim).split((c: C) => c === ',')) yield ops.StringOps(e).trim
      opts match {
        case ISZ(name, _*) =>
          solverArgs(name, timeoutInMs, rlimit) match {
            case Some(prefix) =>
              nameExePathMap.get(name) match {
                case Some(exe) => r = r :+ Smt2Config(isSat, name, exe, prefix ++ ops.ISZOps(opts).drop(1))
                case _ =>
              }
            case _ => return Either.Right(s"Unsupported SMT2 solver name: $name")
          }
        case _ => return Either.Right(s"Invalid SMT2 configuration: $option")
      }
    }
    return Either.Left(r)
  }

  @pure def isSimpsOp(l: State.Claim.Let.Binary): B = {
    if (!imsOps.contains(l.op)) {
      return F
    }
    l.tipe match {
      case t: AST.Typed.Name => return t.ids == AST.Typed.isName || t.ids == AST.Typed.msName
      case _ => return F
    }
  }

  @strictpure def eqProp(eq: ST, tid: ST): ST =
    st"""; eqprop
        |(assert (forall ((o $tid)) ($eq o o)))
        |(assert (forall ((o1 $tid) (o2 $tid)) (= ($eq o1 o2) ($eq o2 o1))))
        |(assert(forall ((o1 $tid) (o2 $tid) (o3 $tid)) (=> ($eq o1 o2) ($eq o2 o3) ($eq o1 o3))))"""

  @strictpure def eqTypeOfThProp(eq: ST, tid: ST, trel: String, typeofName: ST, thid: ST): ST =
    st"""; eqprop
        |(assert (forall ((o $tid)) (=> ($trel ($typeofName o) $thid) ($eq o o))))
        |(assert (forall ((o1 $tid) (o2 $tid)) (=> ($trel ($typeofName o1) $thid) ($trel ($typeofName o2) $thid) (= ($eq o1 o2) ($eq o2 o1)))))
        |(assert(forall ((o1 $tid) (o2 $tid) (o3 $tid)) (=> ($trel ($typeofName o1) $thid) ($trel ($typeofName o2) $thid) ($trel ($typeofName o3) $thid) ($eq o1 o2) ($eq o2 o3) ($eq o1 o3))))"""

  @strictpure def eqThProp(eq: ST, tid: ST, trel: String, thid: ST): ST = eqTypeOfThProp(eq, tid, trel, st"type-of", thid)
}

@msig trait Smt2 {

  @pure def fpRoundingMode: String

  @strictpure def f32ST: ST = if (useReal) {
    st"""(define-sort F32 () Real)
        |(declare-const |F32.PInf| F32)
        |(declare-const |F32.NInf| F32)
        |(declare-const |F32.NaN| F32)
        |(define-fun |F32.isNaN| ((x F32)) B (= x |F32.NaN|))
        |(define-fun |F32.isInfinite| ((x F32)) B (or (= x |F32.PInf|) (= x |F32.NInf|)))
        |(define-fun |F32.unary_-| ((x F32)) F32 (- x))
        |(define-fun |F32.<=| ((x F32) (y F32)) B (<= x y))
        |(define-fun |F32.<| ((x F32) (y F32)) B (< x y))
        |(define-fun |F32.>| ((x F32) (y F32)) B (> x y))
        |(define-fun |F32.>=| ((x F32) (y F32)) B (>= x y))
        |(define-fun |F32.==| ((x F32) (y F32)) B (= x y))
        |(define-fun |F32.!=| ((x F32) (y F32)) B (not (= x y)))
        |(define-fun |F32.+| ((x F32) (y F32)) F32 (+ x y))
        |(define-fun |F32.-| ((x F32) (y F32)) F32 (- x y))
        |(define-fun |F32.*| ((x F32) (y F32)) F32 (* x y))
        |(define-fun |F32./| ((x F32) (y F32)) F32 (/ x y))
        |(declare-fun |F32.%| (F32 F32) F32)"""
  } else {
    st"""(define-sort F32 () Float32)
        |(define-const |F32.PInf| F32 (_ +oo 8 24))
        |(define-const |F32.NInf| F32 (_ -oo 8 24))
        |(define-const |F32.NaN| F32 (_ NaN 8 24))
        |(define-fun |F32.isNaN| ((x F32)) B (fp.isNaN x))
        |(define-fun |F32.isInfinite| ((x F32)) B (fp.isInfinite x))
        |(define-fun |F32.unary_-| ((x F32)) F32 (fp.neg x))
        |(define-fun |F32.<=| ((x F32) (y F32)) B (fp.leq x y))
        |(define-fun |F32.<| ((x F32) (y F32)) B (fp.lt x y))
        |(define-fun |F32.>| ((x F32) (y F32)) B (fp.gt x y))
        |(define-fun |F32.>=| ((x F32) (y F32)) B (fp.geq x y))
        |(define-fun |F32.==| ((x F32) (y F32)) B (fp.eq x y))
        |(define-fun |F32.!=| ((x F32) (y F32)) B (not (fp.eq x y)))
        |(define-fun |F32.+| ((x F32) (y F32)) F32 (fp.add $fpRoundingMode x y))
        |(define-fun |F32.-| ((x F32) (y F32)) F32 (fp.sub $fpRoundingMode x y))
        |(define-fun |F32.*| ((x F32) (y F32)) F32 (fp.mul $fpRoundingMode x y))
        |(define-fun |F32./| ((x F32) (y F32)) F32 (fp.div $fpRoundingMode x y))
        |(define-fun |F32.%| ((x F32) (y F32)) F32 (fp.rem x y))"""
  }

  @strictpure def f64ST: ST = if (useReal) {
    st"""(define-sort F64 () Real)
        |(declare-const |F64.PInf| F64)
        |(declare-const |F64.NInf| F64)
        |(declare-const |F64.NaN| F64)
        |(define-fun |F64.isNaN| ((x F64)) B (= x |F64.NaN|))
        |(define-fun |F64.isInfinite| ((x F64)) B (or (= x |F64.PInf|) (= x |F64.NInf|)))
        |(define-fun |F64.unary_-| ((x F64)) F64 (- x))
        |(define-fun |F64.<=| ((x F64) (y F64)) B (<= x y))
        |(define-fun |F64.<| ((x F64) (y F64)) B (< x y))
        |(define-fun |F64.>| ((x F64) (y F64)) B (> x y))
        |(define-fun |F64.>=| ((x F64) (y F64)) B (>= x y))
        |(define-fun |F64.==| ((x F64) (y F64)) B (= x y))
        |(define-fun |F64.!=| ((x F64) (y F64)) B (not (= x y)))
        |(define-fun |F64.+| ((x F64) (y F64)) F64 (+ x y))
        |(define-fun |F64.-| ((x F64) (y F64)) F64 (- x y))
        |(define-fun |F64.*| ((x F64) (y F64)) F64 (* x y))
        |(define-fun |F64./| ((x F64) (y F64)) F64 (/ x y))
        |(declare-fun |F64.%| (F64 F64) F64)"""
  } else {
    st"""(define-sort F64 () Float64)
        |(define-const |F64.PInf| F64 (_ +oo 11 53))
        |(define-const |F64.NInf| F64 (_ -oo 11 53))
        |(define-const |F64.NaN| F64 (_ NaN 11 53))
        |(define-fun |F64.isNaN| ((x F64)) B (fp.isNaN x))
        |(define-fun |F64.isInfinite| ((x F64)) B (fp.isInfinite x))
        |(define-fun |F64.unary_-| ((x F64)) F64 (fp.neg x))
        |(define-fun |F64.<=| ((x F64) (y F64)) B (fp.leq x y))
        |(define-fun |F64.<| ((x F64) (y F64)) B (fp.lt x y))
        |(define-fun |F64.>| ((x F64) (y F64)) B (fp.gt x y))
        |(define-fun |F64.>=| ((x F64) (y F64)) B (fp.geq x y))
        |(define-fun |F64.==| ((x F64) (y F64)) B (fp.eq x y))
        |(define-fun |F64.!=| ((x F64) (y F64)) B (not (fp.eq x y)))
        |(define-fun |F64.+| ((x F64) (y F64)) F64 (fp.add $fpRoundingMode x y))
        |(define-fun |F64.-| ((x F64) (y F64)) F64 (fp.sub $fpRoundingMode x y))
        |(define-fun |F64.*| ((x F64) (y F64)) F64 (fp.mul $fpRoundingMode x y))
        |(define-fun |F64./| ((x F64) (y F64)) F64 (fp.div $fpRoundingMode x y))
        |(define-fun |F64.%| ((x F64) (y F64)) F64 (fp.rem x y))"""
  }

  @pure def timeoutInMs: Z

  @pure def simplifiedQuery: B

  @pure def charBitWidth: Z

  @pure def intBitWidth: Z

  @pure def useReal: B

  def configs: ISZ[Smt2Config]

  def types: HashSet[AST.Typed]

  def typesUp(newTypes: HashSet[AST.Typed]): Unit

  def poset: Poset[AST.Typed.Name]

  def posetUp(newPoset: Poset[AST.Typed.Name]): Unit

  def sorts: ISZ[ST]

  def sortsUp(newSorts: ISZ[ST]): Unit

  def seqLits: HashSSet[Smt2.SeqLit]

  def seqLitsUp(newSeqLits: HashSSet[Smt2.SeqLit]): Unit

  def addSort(sort: ST): Unit = {
    sortsUp(sorts :+ sort)
  }

  def adtDecls: ISZ[ST]

  def adtDeclsUp(newAdtDecls: ISZ[ST]): Unit

  def typeDecls: ISZ[ST]

  def typeDeclsUp(newTypeDecls: ISZ[ST]): Unit

  def sTypeDecls: ISZ[ST]

  def sTypeDeclsUp(newTypeDecls: ISZ[ST]): Unit

  def strictPureMethods: HashSMap[State.ProofFun, (ST, ST)]

  def strictPureMethodsUp(newProofFuns: HashSMap[State.ProofFun, (ST, ST)]): Unit

  def constraints: ISZ[ST]

  def constraintsUp(newConstraints: ISZ[ST]): Unit

  def writeFile(dir: String, filename: String, content: String): Unit

  def typeOfSeqSet: HashSet[(String, AST.Typed)]

  def typeOfSeqSetUp(newTypeOfSeqSet: HashSet[(String, AST.Typed)]): Unit

  @strictpure def proofFunId(pf: State.ProofFun): ST = {
    val targs: ST = pf.receiverTypeOpt match {
      case Some(receiverType: AST.Typed.Name) =>
        if (receiverType.args.isEmpty) st"#"
        else st"[${(for (arg <- receiverType.args) yield typeIdRaw(arg), ", ")}]#"
      case _ => st"."
    }
    val pTypes: ST = st"(${(for (pt <- pf.paramTypes) yield typeIdRaw(pt), ", ")})"
    if (pf.context.isEmpty) st"|${pf.id}$pTypes|"
    else st"|${(pf.context, ".")}$targs${pf.id}$pTypes|"
  }

  def injectAdditionalClaims(v: State.Value.Sym, claims: ISZ[State.Claim],
                             additionalClaims: ISZ[State.Claim]): Option[ISZ[State.Claim]] = {
    if (claims.size == 0) {
      return None()
    }
    var newClaims = ISZ[State.Claim]()
    var changed = F
    for (c <- claims) {
      c match {
        case c: State.Claim.And =>
          injectAdditionalClaims(v, c.claims, additionalClaims) match {
            case Some(cs) =>
              newClaims = newClaims :+ State.Claim.And(cs)
              changed = T
            case _ => newClaims = newClaims :+ c
          }
        case c: State.Claim.Imply =>
          injectAdditionalClaims(v, c.claims, additionalClaims) match {
            case Some(cs) =>
              newClaims = newClaims :+ State.Claim.Imply(cs)
              changed = T
            case _ => newClaims = newClaims :+ c
          }
        case c: State.Claim.Or =>
          injectAdditionalClaims(v, c.claims, additionalClaims) match {
            case Some(cs) =>
              newClaims = newClaims :+ State.Claim.Or(cs)
              changed = T
            case _ => newClaims = newClaims :+ c
          }
        case c: State.Claim.If =>
          val newTClaimsOpt = injectAdditionalClaims(v, c.tClaims, additionalClaims)
          val newFClaimsOpt = injectAdditionalClaims(v, c.fClaims, additionalClaims)
          if (newTClaimsOpt.isEmpty && newFClaimsOpt.isEmpty) {
            newClaims = newClaims :+ c
          } else {
            newClaims = newClaims :+ c(tClaims = newTClaimsOpt.getOrElse(c.tClaims), fClaims = newFClaimsOpt.getOrElse(c.fClaims))
            changed = T
          }
        case c: State.Claim.Prop => newClaims = newClaims :+ c
        case c: State.Claim.Let =>
          if (c.sym.num == v.num) {
            newClaims = newClaims :+ State.Claim.And(c +: additionalClaims)
            changed = T
          } else {
            newClaims = newClaims :+ c
          }
        case c: State.Claim.Label => newClaims = newClaims :+ c
      }
    }
    return if (changed) Some(newClaims) else None()
  }

  def addStrictPureMethodDecl(pf: State.ProofFun, sym: State.Value.Sym, invClaims: ISZ[State.Claim], reporter: Reporter): Unit = {
    pf.receiverTypeOpt match {
      case Some(rt) => addType(rt, reporter)
      case _ =>
    }
    for (pt <- pf.paramTypes) {
      addType(pt, reporter)
    }
    addType(pf.returnType, reporter)

    val id = proofFunId(pf)
    val context = pf.context :+ pf.id
    val thisId = currentLocalIdString(context, "this")
    var paramIdTypes: ISZ[(ST, AST.Typed)] = ISZ[(ST, AST.Typed)]()
    pf.receiverTypeOpt match {
      case Some(receiverType) => paramIdTypes = paramIdTypes :+ ((thisId, receiverType))
      case _ =>
    }
    for (p <- ops.ISZOps(pf.paramIds).zip(pf.paramTypes)) {
      paramIdTypes = paramIdTypes :+ ((currentLocalIdString(context, p._1), p._2))
    }
    val app: ST = if (paramIdTypes.isEmpty) id else st"($id ${(for (p <- paramIdTypes) yield p._1, " ")})"
    val (decls, claim) = addTypeConstraints(T, paramIdTypes :+ ((v2ST(sym), pf.returnType)),
      st"""(=>
          |    (= ${v2ST(sym)} $app)
          |    ${embeddedClaims(F, invClaims, ISZ(), None(), HashSMap.empty)})"""
    )
    val declClaim: ST = if (invClaims.size == 0) st"" else
      st"""(assert (forall (${(decls, " ")})
          |  $claim
          |))"""
    val decl = st"(declare-fun $id (${(for (p <- paramIdTypes) yield adtId(p._2), " ")}) ${adtId(pf.returnType)})"
    strictPureMethodsUp(strictPureMethods + pf ~> ((decl, declClaim)))
  }

  def addStrictPureMethod(pos: message.Position, pf: State.ProofFun, svs: ISZ[(State, State.Value.Sym)],
                          statePrefix: Z, reporter: Reporter): Unit = {
    val context = pf.context :+ pf.id
    val thisId = currentLocalIdString(context, "this")
    var paramIdTypes: ISZ[(String, ST, AST.Typed)] = ISZ[(String, ST, AST.Typed)]()
    pf.receiverTypeOpt match {
      case Some(receiverType) => paramIdTypes = paramIdTypes :+ (("this", thisId, receiverType))
      case _ =>
    }
    for (p <- ops.ISZOps(pf.paramIds).zip(pf.paramTypes)) {
      paramIdTypes = paramIdTypes :+ ((p._1, currentLocalIdString(context, p._1), p._2))
    }
    val (decl, declClaim) = strictPureMethods.get(pf).get

    var ecs = ISZ[ST]()
    for (sv <- svs if sv._1.status) {
      val (s0, v) = sv
      var s1 = s0
      var args = ISZ[State.Value]()
      for (ptid <- paramIdTypes) {
        val (pid, _, pt) = ptid
        val (s2, v2) = idIntro(pos, s1, context, pid, pt, None())
        args = args :+ v2
        s1 = s2
      }
      val (s3, v3) = s1.freshSym(pf.returnType, pos)
      s1 = s3.addClaim(State.Claim.Let.ProofFunApply(v3, pf, args))
      val claims = State.Claim.Imply(ISZ(
        State.Claim.And(ops.ISZOps(s1.claims).slice(statePrefix, s1.claims.size)),
        State.Claim.Let.Eq(v, v3)
      ))
      ecs = ecs :+ embeddedClaims(T, ISZ(claims), ISZ(), None(), HashSMap.empty)
    }
    val ec: ST = if (ecs.isEmpty) {
      val ignore = reporter.ignore
      reporter.setIgnore(F)
      reporter.warn(Some(pos), Logika.kind, "Could not derive SMT2 function; try refactoring to a @strictpure method")
      reporter.setIgnore(ignore)
      st"true"
    } else if (ecs.size == 1) {
      ecs(0)
    } else {
      st"""(and
          |  ${(ecs, "\n")})"""
    }
    val claim: ST = if (paramIdTypes.nonEmpty) {
      val (decls, ec2) = addTypeConstraints(T, for (t <- paramIdTypes) yield (t._2, t._3), ec)
      st"""$declClaim
          |(assert (forall (${(decls, " ")})
          |  $ec2))"""
    } else {
      st"""$declClaim
          |(assert $ec)"""
    }
    strictPureMethodsUp(strictPureMethods + pf ~> ((decl, claim)))
  }

  def addAdtDecl(adtDecl: ST): Unit = {
    adtDeclsUp(adtDecls :+ adtDecl)
  }

  def addAdtDecls(adtDecls: ISZ[ST]): Unit = {
    adtDeclsUp(this.adtDecls ++ adtDecls)
  }

  def addSTypeDecl(sTypeDecl: ST): Unit = {
    sTypeDeclsUp(sTypeDecls :+ sTypeDecl)
  }

  def addSTypeDecls(sTypeDecls: ISZ[ST]): Unit = {
    sTypeDeclsUp(this.sTypeDecls ++ sTypeDecls)
  }

  def addTypeDecl(typeDecl: ST): Unit = {
    typeDeclsUp(typeDecls :+ typeDecl)
  }

  def addTypeDecls(typeDecls: ISZ[ST]): Unit = {
    typeDeclsUp(this.typeDecls ++ typeDecls)
  }

  def addConstraint(constraint: ST): Unit = {
    constraintsUp(constraints :+ constraint)
  }

  def typeHierarchyIds: ISZ[ST]

  def typeHierarchyIdsUp(newTypeHierarchyIds: ISZ[ST]): Unit

  def addTypeHiearchyId(tId: ST): Unit = {
    typeHierarchyIdsUp(typeHierarchyIds :+ tId)
  }

  def shortIds: HashMap[ISZ[String], ISZ[String]]

  def shortIdsUp(newShortIds: HashMap[ISZ[String], ISZ[String]]): Unit

  def addShortIds(ids: ISZ[String], shortenedIds: ISZ[String]): Unit = {
    shortIdsUp(shortIds + ids ~> shortenedIds)
  }

  def addSeqLit(t: AST.Typed.Name, n: Z, reporter: Reporter): Unit = {
    addType(t, reporter)
    seqLitsUp(seqLits + Smt2.SeqLit(t, n))
  }

  def typeHierarchy: TypeHierarchy

  def checkSat(cache: Smt2.Cache, query: String): (B, Smt2Query.Result)

  def checkUnsat(cache: Smt2.Cache, query: String): (B, Smt2Query.Result)

  def formatVal(width: Z, n: Z): ST

  def formatF32(value: F32): ST

  def formatF64(value: F64): ST

  def formatR(value: R): ST

  @memoize def adtId(tipe: AST.Typed): ST = {
    tipe match {
      case tipe: AST.Typed.Name if isAdt(tipe) => return st"ADT"
      case _ => typeId(tipe)
    }
  }

  @memoize def typeOpId(tipe: AST.Typed, op: String): ST = {
    return st"|${typeIdRaw(tipe)}.${Smt2.quotedEscape(op)}|"
  }

  @memoize def adtTypeOpId(t: AST.Typed, op: String): ST = {
    return if (isAdtType(t)) st"|ADT.${Smt2.quotedEscape(op)}|" else typeOpId(t, op)
  }

  def satResult(cache: Smt2.Cache, reportQuery: B, log: B, logDirOpt: Option[String], title: String, pos: message.Position,
                claims: ISZ[State.Claim], reporter: Reporter): (B, Smt2Query.Result) = {
    val startTime = extension.Time.currentMillis
    val (r, smt2res) = checkSat(cache, satQuery(claims, None(), reporter).render)
    val header =
      st"""; Satisfiability check for $title
          |${smt2res.info}"""
    val res = smt2res(info = header.render, query =
      st"""$header
          |;
          |; Claims:
          |;
          |${(toSTs(claims, ClaimDefs.empty), "\n")}
          |;
          |${smt2res.query}""".render
    )
    if (reportQuery) {
      reporter.query(pos, title, extension.Time.currentMillis - startTime, res)
    }
    if (log) {
      reporter.info(None(), Logika.kind, res.query)
    }
    logDirOpt match {
      case Some(logDir) =>
        val filename: String =
          if (ops.StringOps(title).contains("[")) s"sat-$title"
          else s"sat-$title-at-${pos.beginLine}-${pos.beginColumn}"
        writeFile(logDir, filename, res.query)
      case _ =>
    }
    return (r, smt2res)
  }

  def sat(cache: Smt2.Cache, reportQuery: B, log: B, logDirOpt: Option[String], title: String, pos: message.Position,
          claims: ISZ[State.Claim], reporter: Reporter): B = {
    return satResult(cache, reportQuery, log, logDirOpt, title, pos, claims, reporter)._1
  }

  def toVal(t: AST.Typed.Name, n: Z): ST = {
    val bw: Z = if (t == AST.Typed.z) {
      intBitWidth
    } else {
      val ast = typeHierarchy.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.SubZ].ast
      if (!ast.isBitVector) intBitWidth else ast.bitWidth
    }
    return formatVal(bw, n)
  }

  def addTypeVarIndex(t: AST.Typed.TypeVar): Unit = {
    if (types.contains(t)) {
      return
    }
    val tid = typeId(t)
    addSort(st"(define-sort $tid () Z)")
    val t2zId = typeOpId(t, "toZ")
    val oneId = typeOpId(t, "1")
    val minId = typeOpId(t, "Min")
    val leId = typeOpId(t, "<=")
    val eqId = typeOpId(t, "==")
    val neId = typeOpId(t, "!=")
    val addId = typeOpId(t, "+")
    val subId = typeOpId(t, "-")
    addSort(
      st"""(define-fun $eqId ((n1 $tid) (n2 $tid)) B (= n1 n2))
          |(define-fun $neId ((n1 $tid) (n2 $tid)) B (not (= n1 n2)))
          |(define-fun $leId ((n1 $tid) (n2 $tid)) B (<= n1 n2))
          |(define-fun $addId ((n1 $tid) (n2 $tid)) $tid (+ n1 n2))
          |(define-fun $subId ((n1 $tid) (n2 $tid)) $tid (- n1 n2))
          |(define-fun $t2zId ((n $tid)) Z n)
          |(define-const $oneId $tid 1)
          |(define-const $minId $tid 0)"""
    )
    typesUp(types + t)
  }

  @strictpure def sTypeOfName(t: AST.Typed.Name): ST = st"|type-of-${t.ids(t.ids.size - 1)}-${typeIdRaw(t.args(0))}|"

  def addType(tipe: AST.Typed, reporter: Reporter): Unit = {
    def addS(t: AST.Typed.Name): Unit = {
      val it = t.args(0)
      addType(it, reporter)
      val et = t.args(1)
      addType(et, reporter)
      val tId = typeId(t)
      val thId = typeHierarchyId(t)
      val itId = typeId(it)
      val etId = adtId(et)
      val atId = typeOpId(t, "at")
      val atZId = typeOpId(t, "atZ")
      val sizeId = typeOpId(t, "size")
      val appendId = typeOpId(t, ":+")
      val appendsId = typeOpId(t, "++")
      val prependId = typeOpId(t, "+:")
      val upId = typeOpId(t, "up")
      val eqId = typeOpId(t, "==")
      val neId = typeOpId(t, "!=")
      val isInBoundId = typeOpId(t, "isInBound")
      val itLeId = typeOpId(it, "<=")
      val itEqId = typeOpId(it, "==")
      val itAddId = typeOpId(it, "+")
      val itSubId = typeOpId(it, "-")
      val it2zId = typeOpId(it, "toZ")
      val firstIndexId = typeOpId(t, "firstIndex")
      val lastIndexId = typeOpId(t, "lastIndex")
      val zZero = toVal(AST.Typed.z, 0)
      val zOne = toVal(AST.Typed.z, 1)
      val zAddId = typeOpId(AST.Typed.z, "+")
      val zSubId = typeOpId(AST.Typed.z, "-")
      val zGeId = typeOpId(AST.Typed.z, ">=")
      val zEqId = typeOpId(AST.Typed.z, "==")
      val etThid = typeHierarchyId(et)
      val etAdt: B = isAdtType(et)
      val sname = t.ids(t.ids.size - 1)
      val typeofName = sTypeOfName(t)
      if (etAdt) {
        addTypeHiearchyId(thId)
        if (!typeOfSeqSet.contains((sname, it))) {
          typeOfSeqSetUp(typeOfSeqSet + ((sname, it)))
          addSTypeDecl(st"""(declare-fun $typeofName ($tId) Type)""")
        }
        addSort(st"""(declare-const $thId Type)""")
      }
      @strictpure def etThidSubtypeOpt(x: String): Option[ST] = if (etAdt) Some(st"(sub-type (type-of $x) $etThid)") else None()
      @strictpure def thidTypeOpt(x: String): Option[ST] = if (etAdt) Some(st"(= ($typeofName $x) $thId)") else None()
      addSort(st"(define-sort $tId () (Array $itId $etId))")
      addSTypeDecl(st"(declare-fun $sizeId ($tId) Z)")
      addSTypeDecl(st"(assert (forall ((x $tId)) ($zGeId ($sizeId x) $zZero)))")
      addSTypeDecl(st"(declare-fun $firstIndexId ($tId) $itId)")
      addSTypeDecl(st"(declare-fun $lastIndexId ($tId) $itId)")
      val (_, itOne): (ST, ST) = it match {
        case it: AST.Typed.Name =>
          if (it == AST.Typed.z) {
            val min = toVal(it, 0)
            addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($firstIndexId x) $min))))")
            addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($lastIndexId x) ($zSubId ($sizeId x) $zOne)))))")
            addSTypeDecl(st"(define-fun $atZId ((x $tId) (y $itId)) $etId (select x y))")
            (min, toVal(it, 1))
          } else {
            val ti = typeHierarchy.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.SubZ]
            val min: ST = if (ti.ast.isZeroIndex) toVal(it, 0) else typeOpId(it, "Min")
            addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($firstIndexId x) $min))))")
            addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($it2zId ($lastIndexId x)) ($zSubId ($sizeId x) $zOne)))))")
            addSTypeDecl(st"(declare-fun $atZId ($tId $itId) $etId)")
            (min, toVal(it, 1))
          }
        case it: AST.Typed.TypeVar =>
          val min = typeOpId(it, "Min")
          addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($firstIndexId x) $min))))")
          addSTypeDecl(st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($it2zId ($lastIndexId x)) ($zSubId ($sizeId x) $zOne)))))")
          addSTypeDecl(st"(declare-fun $atZId ($tId $itId) $etId)")
          (min, typeOpId(it, "1"))
        case _ => halt(s"Infeasible: $it")
      }
      addSTypeDecl(st"(define-fun $isInBoundId ((x $tId) (y $itId)) B (and (not ($zEqId ($sizeId x) 0)) ($itLeId ($firstIndexId x) y) ($itLeId y ($lastIndexId x))))")
      addSTypeDecl(st"(define-fun $atId ((x $tId) (y $itId)) $etId (select x y))")
      if (etAdt) {
        addSTypeDecl(st"(assert (forall ((o $tId) (i $itId)) (=> ${thidTypeOpt("o")} ($isInBoundId o i) (sub-type (type-of ($atId o i)) $etThid))))")
      }
      addSTypeDecl(
        st"""(define-fun $appendId ((x $tId) (y $etId) (z $tId)) B
            |  (and
            |    ${thidTypeOpt("z")}
            |    ($itEqId ($sizeId z) ($zAddId ($sizeId x) $zOne))
            |    (forall ((i $itId)) (=> ($isInBoundId x i)
            |                        (= ($atId z i) ($atId x i))))
            |    (= ($atId z ($lastIndexId z)) y)))""")
      addSTypeDecl(
        st"""(define-fun $appendsId ((x $tId) (y $tId) (z $tId)) B
            |  (and
            |    ${thidTypeOpt("z")}
            |    (= ($sizeId z) ($zAddId ($sizeId x) ($sizeId y)))
            |    (forall ((i $itId)) (=> ($isInBoundId x i)
            |                            (= ($atId z i) ($atId x i))))
            |    (forall ((i $itId)) (=> ($isInBoundId y i)
            |                            (= ($atId z ($itAddId ($itAddId ($lastIndexId x) ($itSubId i ($firstIndexId y))) $itOne)) ($atId y i))))))""")
      addSTypeDecl(
        st"""(define-fun $prependId ((x $etId) (y $tId) (z $tId)) B
            |  (and
            |    ${thidTypeOpt("z")}
            |    (= ($sizeId z) ($zAddId ($sizeId y) 1))
            |    (forall ((i $itId)) (=> ($isInBoundId y i)
            |                            (= ($atId z ($itAddId i $itOne)) ($atId y i))))
            |    (= ($atId z ($firstIndexId z)) x)))""")
      addSTypeDecl(
        st"""(declare-fun $upId ($tId $itId $etId) $tId)
            |(assert (forall ((x $tId) (y $itId) (z $etId) (x2 $tId))
            |  (=>
            |    ${thidTypeOpt("x")}
            |    ${etThidSubtypeOpt("z")}
            |    (= x2 ($upId x y z))
            |    (and
            |      ${thidTypeOpt("x2")}
            |      (= ($sizeId x2) ($sizeId x))
            |      ($itEqId ($lastIndexId x2) ($lastIndexId x))
            |      (=> ($isInBoundId x y) (= x2 (store x y z))))
            |  )
            |))""")
      addSTypeDecl(
        st"""(define-fun $eqId ((x $tId) (y $tId)) B
            |  (and
            |    (= ($sizeId x) ($sizeId y))
            |    (=> (not (= 0 ($sizeId x))) ($itEqId ($lastIndexId x) ($lastIndexId y)))
            |    (forall ((i $itId)) (=> ($isInBoundId x i) (= (select x i) (select y i))))))""")
      addSTypeDecl(st"""(define-fun $neId ((x $tId) (y $tId)) B (not ($eqId x y)))""")
      if (typeHierarchy.isSubstitutable(et)) {
        addSTypeDecl(
          st"""(assert (forall ((x $tId) (y $tId))
              |  (=>
              |    ${thidTypeOpt("x")}
              |    ${thidTypeOpt("y")}
              |    ($eqId x y)
              |    (= x y))))""")
      }
      if (etAdt) {
        addSTypeDecl(
          st"""(assert (forall ((x $tId) (i $itId) (v $etId))
              |  (=> ${thidTypeOpt("x")}
              |      ($isInBoundId x i)
              |      (= ($atId x i) v)
              |      ${etThidSubtypeOpt("v")})))""")
      }
    }

    def addSub(posOpt: Option[message.Position],
               isRoot: B,
               t: AST.Typed.Name,
               tId: ST,
               parents: ISZ[AST.Typed.Name],
               tsm: HashMap[String, AST.Typed]): Unit = {
      @pure def sortName(names: ISZ[ISZ[String]]): ISZ[ISZ[String]] = {
        return ops.ISZOps(names).sortWith((n1, n2) => st"${(n1, ".")}".render <= st"${(n2, ".")}".render)
      }

      var ps = ISZ[AST.Typed.Name]()
      for (parent <- parents) {
        val p = parent.subst(tsm)
        ps = ps :+ p
      }
      if (ps.nonEmpty) {
        posetUp(poset.addParents(t, ps))
        for (p <- ps) {
          addType(p, reporter)
        }
      }
      if (isRoot) {
        var children = ISZ[AST.Typed.Name]()
        var hasChild = F
        for (sub <- sortName(typeHierarchy.poset.childrenOf(t.ids).elements)) {
          val (parents, tpSize, tipe): (ISZ[AST.Typed.Name], Z, AST.Typed.Name) = typeHierarchy.typeMap.get(sub).get match {
            case childTi: TypeInfo.Adt => (childTi.parents, childTi.ast.typeParams.size, childTi.tpe)
            case childTi: TypeInfo.Sig => (childTi.parents, childTi.ast.typeParams.size, childTi.tpe)
            case _ => halt(s"Infeasible: $sub")
          }
          for (parent <- parents if parent.ids == t.ids) {
            if (tpSize > 0) {
              val sm = TypeChecker.unify(typeHierarchy, None(), TypeChecker.TypeRelation.Equal, t, parent, reporter).get
              assert(sm.size == tpSize)
              val childT = tipe.subst(sm)
              children = children :+ childT
              addType(childT, reporter)
              val childThId = typeHierarchyId(childT)
              addConstraint(
                st"""(assert (forall ((o1 ADT) (o2 ADT))
                    |  (=> (sub-type (type-of o1) $childThId)
                    |      (sub-type (type-of o2) $childThId)
                    |      (= (${typeOpId(t, "==")} o1 o2) (${typeOpId(childT, "==")} o1 o2)))
                    |))"""
              )
              addConstraint(
                st"""(assert (forall ((o1 ADT) (o2 ADT))
                    |  (=> (sub-type (type-of o1) $childThId)
                    |      (not (sub-type (type-of o2) $childThId))
                    |      (= (${typeOpId(t, "==")} o1 o2) false))
                    |))"""
              )
            } else {
              hasChild = T
              addType(tipe, reporter)
            }
          }
        }
        if (!hasChild && children.isEmpty && t != AST.Typed.nothing && t != AST.Typed.string && t != AST.Typed.st) {
          reporter.warn(posOpt, Logika.kind, s"$t does not have any concrete implementation")
        }
        posetUp(poset.addChildren(t, children))
        addTypeDecls(for (child <- children) yield st"(assert (sub-type ${typeHierarchyId(child)} $tId))")
      }
    }

    def addAdt(t: AST.Typed.Name, ti: TypeInfo.Adt): Unit = {
      val sm = TypeChecker.buildTypeSubstMap(t.ids, None(), ti.ast.typeParams, t.args, reporter).get
      for (arg <- t.args) {
        addType(arg.subst(sm), reporter)
      }
      for (v <- ti.vars.values) {
        addType(v.typedOpt.get.subst(sm), reporter)
      }
      for (v <- ti.specVars.values) {
        addType(v.typedOpt.get.subst(sm), reporter)
      }
      posetUp(poset.addNode(t))
      val tId = typeId(t)
      addAdtDecl(st"(define-sort $tId () ADT)")
      val thId = typeHierarchyId(t)
      addTypeHiearchyId(thId)
      addSort(st"(declare-const $thId Type)")
      if (!ti.ast.isRoot) {
        addAdtDecl(st"(assert (forall ((x ${typeId(t)})) (= (sub-type (type-of x) $thId) (= (type-of x) $thId))))")
      }
      addSub(ti.posOpt, ti.ast.isRoot, t, thId, ti.parents, sm)

      @pure def fieldInfo(isParam: B, f: Info.Var): Smt2.AdtFieldInfo = {
        val ft = f.typedOpt.get.subst(sm)
        val id = f.ast.id.value
        return Smt2.AdtFieldInfo(isParam, F, id, typeOpId(t, id), typeOpId(t, s"${id}_="), typeId(ft), ft)
      }

      @pure def specFieldInfo(f: Info.SpecVar): Smt2.AdtFieldInfo = {
        val ft = f.typedOpt.get.subst(sm)
        val id = f.ast.id.value
        return Smt2.AdtFieldInfo(F, T, id, typeOpId(t, id), typeOpId(t, s"${id}_="), typeId(ft), ft)
      }


      val eqId = typeOpId(t, "==")
      val neId = typeOpId(t, "!=")
      val parents = poset.parentsOf(t).elements
      if (ti.ast.isRoot) {
        addAdtDecl(st"""(declare-fun $eqId ($tId $tId) B)""")
        if (typeHierarchy.isSubstitutable(t)) {
          addAdtDecl(
            st"""(assert (forall ((x $tId) (y $tId))
                |  (=>
                |    (sub-type (type-of x) $thId)
                |    (sub-type (type-of y) $thId)
                |    ($eqId x y)
                |    (= x y))))"""
          )
        }
        addAdtDecl(st"(define-fun $neId ((o1 $tId) (o2 $tId)) B (not ($eqId o1 o2)))")
        var leaves: ISZ[ST] = ISZ()
        for (child <- poset.childrenOf(t).elements) {
          typeHierarchy.typeMap.get(child.ids) match {
            case Some(info: TypeInfo.Adt) if !info.ast.isRoot => leaves = leaves :+ typeHierarchyId(child)
            case _ =>
          }
        }
        if (leaves.nonEmpty) {
          addAdtDecl(
            st"""(assert (forall ((x $tId))
                |  (let ((t (type-of x)))
                |  (=> (sub-type t $thId)
                |      (or
                |        ${(for (leaf <- leaves) yield st"(sub-type t $leaf)", "\n")})))))"""
          )
        }
      } else {
        if (parents.nonEmpty) {
          addAdtDecl(
            st"""(assert (and
                |  ${(for (p <- poset.parentsOf(t).elements) yield st"(sub-type $thId ${typeHierarchyId(p)})", "\n")}))"""
          )
        }
        val newId = typeOpId(t, "new")
        val params = HashSet.empty[String] ++ (for (p <- ti.ast.params) yield p.id.value)
        val fieldInfos: ISZ[Smt2.AdtFieldInfo] =
          (for (f <- ti.vars.values) yield fieldInfo(params.contains(f.ast.id.value), f)) ++ (for (f <- ti.specVars.values) yield specFieldInfo(f))
        for (q <- fieldInfos) {
          addTypeDecl(st"(declare-fun ${q.fieldLookupId} ($tId) ${q.fieldTypeId})")
          if (isAdtType(q.fieldType)) {
            addTypeDecl(
              st"""(assert (forall ((o $tId))
                  |  (=> (= (type-of o) $thId)
                  |      (sub-type (type-of (${q.fieldLookupId} o)) ${typeHierarchyId(q.fieldType)}))))""")
          }
        }
        var hasParam = F
        for (q <- fieldInfos) {
          if (q.isParam) {
            hasParam = T
          }
          val upOp = typeOpId(t, s"${q.fieldId}_=")
          val feqs: ISZ[ST] = for (q2 <- fieldInfos) yield
            if (q2.fieldId == q.fieldId) st"(= (${q2.fieldLookupId} x!2) x!1)"
            else st"(= (${q2.fieldLookupId} x!2) (${q2.fieldLookupId} x!0))"
          addTypeDecl(
            st"""(declare-fun $upOp ($tId ${q.fieldTypeId}) $tId)
                |(assert (forall ((x!0 $tId) (x!1 ${q.fieldTypeId}) (x!2 $tId))
                |  (=>
                |    (= (type-of x!2) $thId)
                |    (= x!2 ($upOp x!0 x!1))
                |    (and
                |      (= (type-of x!2) (type-of x!0))
                |      ${(feqs, "\n")}
                |    )
                |  )
                |))"""
          )
        }
        addTypeDecl(
          st"""(declare-fun $newId (${(for (q <- fieldInfos if q.isParam) yield q.fieldTypeId, " ")}) $tId)
              |(assert (forall (${(for (q <- fieldInfos if q.isParam) yield st"(${q.fieldId} ${q.fieldTypeId})", " ")} (x!0 $tId))
              |  (=>
              |    ${(for (q <- fieldInfos if q.isParam && isAdtType(q.fieldType)) yield st"(sub-type (type-of ${q.fieldId}) ${typeHierarchyId(q.fieldType)})", "\n")}
              |    (= x!0 ${if (hasParam) st"($newId ${(for (q <- fieldInfos if q.isParam) yield q.fieldId, " ")})" else newId})
              |    (and
              |      (= (type-of x!0) $thId)
              |      ${(for (q <- fieldInfos if q.isParam) yield st"(= (${q.fieldLookupId} x!0) ${q.fieldId})", "\n")})
              |  )
              |))""")
        addTypeDecl(
          st"""(define-fun $eqId ((x!0 $tId) (x!1 $tId)) B
              |  (and
              |    (= (type-of x!0) (type-of x!1) $thId)
              |    ${(for (q <- fieldInfos if q.isParam) yield st"(${if (isAdtType(q.fieldType)) st"${typeOpId(q.fieldType, "==")}" else typeOpId(q.fieldType, "==")} (${q.fieldLookupId} x!0) (${q.fieldLookupId} x!1))", "\n")}))"""
        )
        if (typeHierarchy.isSubstitutable(t)) {
          addTypeDecl(
            st"""(assert (forall ((x!0 $tId) (x!1 $tId))
                |  (=>
                |    (= (type-of x!0) $thId)
                |    (= (type-of x!0) $thId)
                |    ($eqId x!0 x!1)
                |    (= x!0 x!1))))""")
        }
        addTypeDecl(st"""(define-fun $neId ((x $tId) (y $tId)) B (not ($eqId x y)))""")
      }
      for (parent <- parents) {
        addTypeDecl(
          st"""(assert (forall ((o1 $tId) (o2 $tId))
              |  (=>
              |    (sub-type (type-of o1) $thId)
              |    (sub-type (type-of o2) $thId)
              |    ($eqId o1 o2)
              |    (${typeOpId(parent, "==")} o1 o2))))"""
        )
      }
    }

    def addSig(t: AST.Typed.Name, ti: TypeInfo.Sig): Unit = {
      val sm = TypeChecker.buildTypeSubstMap(t.ids, None(), ti.ast.typeParams, t.args, reporter).get
      for (arg <- t.args) {
        addType(arg.subst(sm), reporter)
      }
      posetUp(poset.addNode(t))
      val tid = typeId(t)
      val isString = t.ids === AST.Typed.stringName
      if (!isString) {
        addAdtDecl(st"(define-sort $tid () ADT)")
      }
      val thId = typeHierarchyId(t)
      addTypeHiearchyId(thId)
      addSort(st"(declare-const $thId Type)")
      val eqId = typeOpId(t, "==")
      val neId = typeOpId(t, "!=")
      if (isString) {
        addAdtDecl(st"(define-fun $eqId ((x $tid) (y $tid)) B (= x y))")
      } else {
        addAdtDecl(st"(declare-fun $eqId ($tid $tid) B)")
      }
      addAdtDecl(st"(define-fun $neId ((o1 $tid) (o2 $tid)) B (not ($eqId o1 o2)))")
      addSub(ti.posOpt, T, t, thId, ti.parents, sm)
      var ops = ISZ[(String, ST)]()
      for (info <- ti.specVars.values) {
        val opId = info.ast.id.value
        val op = typeOpId(t, opId)
        val opT = info.typedOpt.get.subst(sm)
        addType(opT, reporter)
        val opTid = typeId(opT)
        addAdtDecl(st"(declare-fun $op ($tid) $opTid)")
        ops = ops :+ ((opId, opTid))
      }
      for (p <- ops) {
        val (opId, opTid) = p
        val opAssignId = s"${opId}_="
        val op = typeOpId(t, opId)
        val opAssign = typeOpId(t, opAssignId)
        addTypeDecl(
          st"""(define-fun $opAssign ((o $tid) ($opId $opTid) (o2 $tid)) B
              |  (and
              |    ($eqId o2 o)
              |    ${(for (p2 <- ops if p2._1 != opId) yield st"(= (${typeOpId(t, p2._1)} o2) (${typeOpId(t, p2._1)} o))", "\n")}
              |    (= $opId ($op o2) ($op o))))""")
      }
      if (!isString) {
        for (parent <- poset.parentsOf(t).elements) {
          addTypeDecl(
            st"""(assert (forall ((o1 $tid) (o2 $tid))
                |  (=>
                |    (sub-type (type-of o1) $thId)
                |    (sub-type (type-of o2) $thId)
                |    ($eqId o1 o2)
                |    (${typeOpId(parent, "==")} o1 o2))))"""
          )
        }
      }
    }

    def addSubZ(t: AST.Typed.Name, ti: TypeInfo.SubZ): Unit = {
      val tId = typeId(t)
      val tNegId = typeOpId(t, "unary_-")
      val tCompId = typeOpId(t, "unary_~")
      val tLeId = typeOpId(t, "<=")
      val tLtId = typeOpId(t, "<")
      val tGeId = typeOpId(t, ">=")
      val tGtId = typeOpId(t, ">")
      val tEqId = typeOpId(t, "==")
      val tNeId = typeOpId(t, "!=")
      val tAddId = typeOpId(t, "+")
      val tSubId = typeOpId(t, "-")
      val tMulId = typeOpId(t, "*")
      val tDivId = typeOpId(t, "/")
      val tRemId = typeOpId(t, "%")
      val tShlId = typeOpId(t, "<<")
      val tShrId = typeOpId(t, ">>")
      val tUshrId = typeOpId(t, ">>>")
      val t2ZId = typeOpId(t, "toZ")
      val tMaxOpt: Option[ST] =
        if (ti.ast.hasMax) Some(st"(define-const ${typeOpId(t, "MAX")} $tId ${toVal(t, ti.ast.max)})")
        else None()
      val tMinOpt: Option[ST] =
        if (ti.ast.hasMax) Some(st"(define-const ${typeOpId(t, "MIN")}  $tId ${toVal(t, ti.ast.min)})")
        else None()
      (ti.ast.isSigned, ti.ast.isBitVector) match {
        case (T, T) =>
          addSort(
            st"""(define-sort $tId () (_ BitVec ${ti.ast.bitWidth}))
                |(declare-fun $t2ZId ($tId) Z)
                |(define-fun $tNegId ((x $tId)) $tId (bvneg x))
                |(define-fun $tCompId ((x $tId)) $tId (bvnot x))
                |(define-fun $tLeId ((x $tId) (y $tId)) B (bvsle x y))
                |(define-fun $tLtId ((x $tId) (y $tId)) B (bvslt x y))
                |(define-fun $tGtId ((x $tId) (y $tId)) B (bvsgt x y))
                |(define-fun $tGeId ((x $tId) (y $tId)) B (bvsge x y))
                |(define-fun $tEqId ((x $tId) (y $tId)) B (= x y))
                |(define-fun $tNeId ((x $tId) (y $tId)) B (not (= x y)))
                |(define-fun $tAddId ((x $tId) (y $tId)) $tId (bvadd x y))
                |(define-fun $tSubId ((x $tId) (y $tId)) $tId (bvsub x y))
                |(define-fun $tMulId ((x $tId) (y $tId)) $tId (bvmul x y))
                |(define-fun $tDivId ((x $tId) (y $tId)) $tId (bvsdiv x y))
                |(define-fun $tRemId ((x $tId) (y $tId)) $tId (bvsrem x y))
                |(define-fun $tShlId ((x $tId) (y $tId)) $tId (bvshl x y))
                |(define-fun $tShrId ((x $tId) (y $tId)) $tId (bvashr x y))
                |(define-fun $tUshrId ((x $tId) (y $tId)) $tId (bvlshr x y))
                |$tMaxOpt
                |$tMinOpt""")
        case (F, T) =>
          addSort(
            st"""(define-sort $tId () (_ BitVec ${ti.ast.bitWidth}))
                |(declare-fun $t2ZId ($tId) Z)
                |(define-fun $tNegId ((x $tId)) $tId (bvneg x))
                |(define-fun $tCompId ((x $tId)) $tId (bvnot x))
                |(define-fun $tLeId ((x $tId) (y $tId)) B (bvule x y))
                |(define-fun $tLtId ((x $tId) (y $tId)) B (bvult x y))
                |(define-fun $tGtId ((x $tId) (y $tId)) B (bvugt x y))
                |(define-fun $tGeId ((x $tId) (y $tId)) B (bvuge x y))
                |(define-fun $tEqId ((x $tId) (y $tId)) B (= x y))
                |(define-fun $tNeId ((x $tId) (y $tId)) B (not (= x y)))
                |(define-fun $tAddId ((x $tId) (y $tId)) $tId (bvadd x y))
                |(define-fun $tSubId ((x $tId) (y $tId)) $tId (bvsub x y))
                |(define-fun $tMulId ((x $tId) (y $tId)) $tId (bvmul x y))
                |(define-fun $tDivId ((x $tId) (y $tId)) $tId (bvudiv x y))
                |(define-fun $tRemId ((x $tId) (y $tId)) $tId (bvurem x y))
                |(define-fun $tShlId ((x $tId) (y $tId)) $tId (bvshl x y))
                |(define-fun $tShrId ((x $tId) (y $tId)) $tId (bvlshr x y))
                |(define-fun $tUshrId ((x $tId) (y $tId)) $tId (bvlshr x y))
                |$tMaxOpt
                |$tMinOpt""")
        case (_, _) =>
          addSort(
            st"""(define-sort $tId () Int)
                |(define-fun $t2ZId ((n $tId)) Z n)
                |(define-fun $tNegId ((x $tId)) $tId (- x))
                |(define-fun $tLeId ((x $tId) (y $tId)) B (<= x y))
                |(define-fun $tLtId ((x $tId) (y $tId)) B (< x y))
                |(define-fun $tGtId ((x $tId) (y $tId)) B (> x y))
                |(define-fun $tGeId ((x $tId) (y $tId)) B (>= x y))
                |(define-fun $tEqId ((x $tId) (y $tId)) B (= x y))
                |(define-fun $tNeId ((x $tId) (y $tId)) B (not (= x y)))
                |(define-fun $tAddId ((x $tId) (y $tId)) $tId (+ x y))
                |(define-fun $tSubId ((x $tId) (y $tId)) $tId (- x y))
                |(define-fun $tMulId ((x $tId) (y $tId)) $tId (* x y))
                |(define-fun $tDivId ((x $tId) (y $tId)) $tId (div x y))
                |(define-fun $tRemId ((x $tId) (y $tId)) $tId (mod x y))
                |$tMaxOpt
                |$tMinOpt""")
      }
    }

    def addEnum(t: AST.Typed.Name, ti: TypeInfo.Enum): Unit = {
      val tid = typeId(t)
      val owner = ops.ISZOps(ti.name).dropRight(1)
      val eqOp = typeOpId(t, "==")
      val neOp = typeOpId(t, "!=")
      val ordinalOp = typeOpId(t, "ordinal")
      addSort(
        st"""(declare-datatypes (($tid 0)) ((
            |  ${(for (element <- ti.elements.keys) yield st"(${typeHierarchyId(AST.Typed.Name(t.ids :+ element, ISZ()))})", " ")})))
            |(declare-fun $ordinalOp ($tid) Int)
            |(define-fun $eqOp ((x $tid) (y $tid)) B (= x y))
            |(define-fun $neOp ((x $tid) (y $tid)) B (not (= x y)))""")
      val elements: ISZ[ST] = for (element <- ti.elements.keys) yield enumId(owner, element)
      var ordinal = 0
      for (element <- elements) {
        addSort(st"(declare-const $element $tid)")
        addSort(st"(assert (= ($ordinalOp $element) $ordinal))")
        ordinal = ordinal + 1
      }
      if (elements.size > 1) {
        addSort(st"(assert (distinct ${(elements, " ")}))")
      }
    }

    def addTypeVar(t: AST.Typed.TypeVar): Unit = {
      val tid = typeId(t)
      addSort(st"(declare-sort $tid 0)")
      val eqId = typeOpId(t, "==")
      val neId = typeOpId(t, "!=")
      addSort(
        st"""(declare-fun $eqId ($tid $tid) B)
            |${Smt2.eqProp(eqId, tid)}
            |(define-fun $neId ((x $tid) (y $tid)) B (not ($eqId x y)))"""
      )
    }

    def addTuple(t: AST.Typed.Tuple): Unit = {
      for (arg <- t.args) {
        addType(arg, reporter)
      }
      val tId = typeId(t)
      val eqId = typeOpId(t, "==")
      val neId = typeOpId(t, "!=")
      addSort(st"""(declare-datatypes (($tId 0)) (((${typeOpId(t, "new")} ${(for (i <- 1 to t.args.size) yield st"(${typeOpId(t, s"_$i")} ${adtId(t.args(i - 1))})", " ")}))))""")
      addTypeDecl(
        st"""(define-fun $eqId ((x $tId) (y $tId)) B
            |  (and
            |    ${(for (i <- 1 to t.args.size) yield st"(${typeOpId(t.args(i - 1), "==")} (${typeOpId(t, s"_$i")} x) (${typeOpId(t, s"_$i")} y))", "\n")}
            |  )
            |)
            |(define-fun $neId ((x $tId) (y $tId)) B (not ($eqId x y)))""")
    }

    val t = Util.normType(tipe)
    if (types.contains(t)) {
      return
    }
    typesUp(types + t)
    t match {
      case AST.Typed.z => sortsUp(sorts :+ Smt2.zST(intBitWidth))
      case AST.Typed.c => sortsUp(sorts :+ Smt2.cST(charBitWidth))
      case AST.Typed.f32 => sortsUp(sorts :+ f32ST)
      case AST.Typed.f64 => sortsUp(sorts :+ f64ST)
      case AST.Typed.r => sortsUp(sorts :+ Smt2.rST)
      case t: AST.Typed.Name =>
        if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
          addS(t)
        } else {
          typeHierarchy.typeMap.get(t.ids).get match {
            case ti: TypeInfo.Adt => addAdt(t, ti)
            case ti: TypeInfo.Sig => addSig(t, ti)
            case ti: TypeInfo.SubZ => addSubZ(t, ti)
            case ti: TypeInfo.Enum => addEnum(t, ti)
            case _ => halt(s"Infeasible: $t")
          }
        }
      case t: AST.Typed.TypeVar => addTypeVar(t)
      case t: AST.Typed.Tuple => addTuple(t)
      case t: AST.Typed.Fun if t.isPureFun =>
        if (t.args.size > 1) {
          addType(AST.Typed.Tuple(t.args), reporter)
        } else {
          addType(t.args(0), reporter)
        }
        addType(t.ret, reporter)
      case _ => halt(s"TODO: $tipe") // TODO
    }
  }

  @memoize def seqLit2SmtDeclST(seqLit: Smt2.SeqLit): ST = {
    val t = seqLit.t
    val size = seqLit.size
    val it = t.args(0).asInstanceOf[AST.Typed.Name]
    val et = t.args(1)
    val tId = typeId(t)
    val itId = typeId(it)
    val etId = adtId(et)
    val seqLitId = typeOpId(t, s"new.$size")
    val atId = typeOpId(t, "at")
    val sizeId = typeOpId(t, "size")
    val itEqId = typeOpId(it, "==")
    val inBoundId = typeOpId(t, "isInBound")
    val lastIndexOpt: Option[ST] =
      if (size != 0) Some(st"($itEqId (${typeOpId(t, "lastIndex")} x) ${toVal(it, size - 1)})") else None()
    val distinctOpt: Option[ST] =
      if (size > 1) Some(st"(distinct ${(for (i <- 0 until size) yield st"i$i", " ")})")
      else None()
    val typeOfOpt: Option[ST] = if (isAdtType(et)) Some(st"(= (${sTypeOfName(t)} x) ${typeHierarchyId(t)})") else None()
    val r =
      st"""(declare-fun $seqLitId (${(for (_ <- 0 until size) yield st"$itId $etId", " ")}) $tId)
          |(assert (forall (${(for (i <- 0 until size) yield st"(i$i $itId) (v$i $etId)", " ")} (x $tId))
          |  (=>
          |    $distinctOpt
          |    (= x ${if (size == 0) seqLitId else st"($seqLitId ${(for (i <- 0 until size) yield st"i$i v$i", " ")})"})
          |    (and
          |      $typeOfOpt
          |      (= ($sizeId x) $size)
          |      $lastIndexOpt
          |      ${(for (i <- 0 until size) yield st"(=> ($inBoundId x i$i) (= ($atId x i$i) v$i))", "\n")})
          |  )
          |))"""
    return r
  }

  def collectLids(claims: ISZ[State.Claim]): HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id] = {
    var r = HashSMap.empty[(ISZ[String], String, Z), State.Claim.Let.Id]
    def collectLidsRec(cs: ISZ[State.Claim]): Unit = {
      for (c <- cs) {
        c match {
          case c: State.Claim.Let.Id => r = r + (c.context, c.id, c.num) ~> c
          case c: State.Claim.If => collectLidsRec(c.tClaims); collectLidsRec(c.fClaims)
          case c: State.Claim.And => collectLidsRec(c.claims)
          case c: State.Claim.Or => collectLidsRec(c.claims)
          case c: State.Claim.Imply => collectLidsRec(c.claims)
          case _: State.Claim.Let =>
          case _: State.Claim.Label =>
          case _: State.Claim.Prop =>
        }
      }
    }
    collectLidsRec(claims)
    return r
  }

  def satQuery(claims: ISZ[State.Claim], negClaimOpt: Option[State.Claim], reporter: Reporter): ST = {
    for (c <- claims; t <- c.types) {
      addType(t, reporter)
    }
    var decls: HashSMap[String, ST] = HashSMap.empty[String, ST] ++ (for (c <- claims; p <- c2DeclST(c)) yield p)
    val (lets, lsyms) = Util.collectLetClaims(simplifiedQuery, claims)
    val lids = collectLids(claims)
    val sv2ST = Util.value2ST(this, lets, lids)
    var claimSmts = ISZ[ST]()
    for (c <- claims) {
      c2ST(c, sv2ST, lets, lids) match {
        case Some(st) => claimSmts = claimSmts :+ st
        case _ =>
      }
    }
    negClaimOpt match {
      case Some(negClaim) =>
        claimSmts = claimSmts :+ st"(not ${c2ST(negClaim, sv2ST, lets, lids)})"
        decls = decls ++ c2DeclST(negClaim)
      case _ =>
    }
    val seqLitDecls: ISZ[ST] = for (seqLit <- seqLits.elements) yield seqLit2SmtDeclST(seqLit)
    if (lets.nonEmpty) {
      val uscdid = UsedSymsCurrentDeclIdCollector(HashSet.empty, ISZ())
      for (c <- claims) {
        uscdid.transformStateClaim(c)
      }
      val usedSyms = uscdid.syms
      val symNums = HashSet ++ (for (sym <- lsyms.elements) yield v2ST(sym).render) ++
        (for (ds <- lets.values if ds.size > 1 && usedSyms.contains(ds(0).sym)) yield v2ST(ds(0).sym).render)
      decls = HashSMap.empty[String, ST] ++
        (for (d <- decls.entries if !ops.StringOps(d._1).startsWith(Smt2.symPrefix) || symNums.contains(d._1)) yield d)
    }
    return query(seqLitDecls, decls.values, claimSmts)
  }

  @strictpure def toSTs(claims: ISZ[State.Claim], defs: ClaimDefs): ISZ[ST] =
    for (cST <- State.Claim.claimsSTs(claims, defs)) yield
      st"${(for (line <- ops.StringOps(cST.render).split(c => c == '\n')) yield st"; $line", "\n")}"

  def valid(cache: Smt2.Cache, reportQuery: B, log: B, logDirOpt: Option[String], title: String, pos: message.Position,
            premises: ISZ[State.Claim], conclusion: State.Claim, reporter: Reporter): Smt2Query.Result = {
    val startTime = extension.Time.currentMillis
    val (_, smt2res) = checkUnsat(cache, satQuery(premises, Some(conclusion), reporter).render)
    val defs = ClaimDefs.empty
    val header =
      st"""; Validity Check for $title
          |${smt2res.info}"""
    val res = smt2res(info = header.render, query =
      st"""$header
          |;
          |; Sequent:
          |;
          |${(toSTs(premises, defs), ",\n")}
          |; ⊢
          |${(toSTs(ISZ(conclusion), defs), ",\n")}
          |;
          |${smt2res.query}""".render
    )
    if (reportQuery) {
      reporter.query(pos, title, extension.Time.currentMillis - startTime, res)
    }
    if (log) {
      reporter.info(None(), Logika.kind, res.query)
    }
    logDirOpt match {
      case Some(logDir) =>
        val filename: String =
          if (ops.StringOps(title).contains("[")) s"vc-$title"
          else s"vc-$title-at-${pos.beginLine}-${pos.beginColumn}"
        writeFile(logDir, filename, res.query)
      case _ =>
    }
    return res
  }

  @memoize def isAdt(t: AST.Typed.Name): B = {
    typeHierarchy.typeMap.get(t.ids).get match {
      case _: TypeInfo.Adt => return T
      case _: TypeInfo.Sig =>
        if (Smt2.basicTypes.contains(t)) {
          return F
        } else if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
          return F
        }
        return T
      case _ => return F
    }
  }

  @pure def isAdtType(t: AST.Typed): B = {
    t match {
      case t: AST.Typed.Name => return isAdt(t)
      case _ => return F
    }
  }

  def query(funDecls: ISZ[ST], decls: ISZ[ST], claims: ISZ[ST]): ST = {
    var ss: ISZ[ST] = sorts
    if (typeHierarchyIds.size > 1) {
      ss = ss :+
        st"""(assert (distinct
            |  ${(typeHierarchyIds, "\n")}))"""
    }

    val r =
      st"""(set-logic ALL)
          |
          |(define-sort B () Bool)
          |(define-fun |B.unary_!| ((x B)) B (not x))
          |(define-fun |B.unary_~| ((x B)) B (not x))
          |(define-fun |B.==| ((x B) (y B)) B (= x y))
          |(define-fun |B.!=| ((x B) (y B)) B (not (= x y)))
          |(define-fun |B.&| ((x B) (y B)) B (and x y))
          |(define-fun |B.│| ((x B) (y B)) B (or x y))
          |(define-fun |B.│^| ((x B) (y B)) B (xor x y))
          |(define-fun |B.imply_:| ((x B) (y B)) B (=> x y))
          |(define-fun |B.->:| ((x B) (y B)) B (=> x y))
          |
          |(declare-sort ADT 0)
          |(declare-sort Type 0)
          |(declare-fun type-of (ADT) Type)
          |(declare-fun sub-type (Type Type) Bool)
          |
          |(assert (forall ((x Type)) (sub-type x x)))
          |(assert (forall ((x Type) (y Type) (z Type)) (=> (and (sub-type x y) (sub-type y z)) (sub-type x z))))
          |(assert (forall ((x Type) (y Type)) (=> (and (sub-type x y) (sub-type y x)) (= x y))))
          |
          |${(ss, "\n\n")}
          |
          |${(adtDecls, "\n")}
          |
          |${(sTypeDecls, "\n")}
          |
          |${(typeDecls, "\n")}
          |
          |${(constraints, "\n")}
          |
          |${(funDecls, "\n")}
          |
          |${(for (p <- strictPureMethods.values) yield p._1, "\n")}
          |
          |${(for (p <- strictPureMethods.values) yield p._2, "\n")}
          |
          |${(decls, "\n")}
          |
          |${(for (a <- claims) yield st"(assert $a)", "\n")}
          |
          |(check-sat)
          |(exit)"""
    return r
  }

  @pure def v2ST(v: State.Value): ST = {
    v match {
      case v: State.Value.B => return if (v.value) Smt2.stTrue else Smt2.stFalse
      case v: State.Value.Z => return if (v.value < 0) st"(- ${v.value * -1})" else st"${v.value}"
      case v: State.Value.Sym => return st"${Smt2.symPrefix}${v.num}"
      case v: State.Value.Range => return if (v.value < 0) st"(- ${v.value * -1})" else st"${v.value}"
      case v: State.Value.Enum => return enumId(v.owner, v.id)
      case v: State.Value.S8 => return toVal(v.tipe, conversions.S8.toZ(v.value))
      case v: State.Value.S16 => return toVal(v.tipe, conversions.S16.toZ(v.value))
      case v: State.Value.S32 => return toVal(v.tipe, conversions.S32.toZ(v.value))
      case v: State.Value.S64 => return toVal(v.tipe, conversions.S64.toZ(v.value))
      case v: State.Value.U8 => return toVal(v.tipe, conversions.U8.toZ(v.value))
      case v: State.Value.U16 => return toVal(v.tipe, conversions.U16.toZ(v.value))
      case v: State.Value.U32 => return toVal(v.tipe, conversions.U32.toZ(v.value))
      case v: State.Value.U64 => return toVal(v.tipe, conversions.U64.toZ(v.value))
      case v: State.Value.F32 => return formatF32(v.value)
      case v: State.Value.F64 => return formatF64(v.value)
      case v: State.Value.C =>
        val t: AST.Typed.Name = charBitWidth match {
          case 8 => AST.Typed.u8
          case 16 => AST.Typed.u16
          case 32 => AST.Typed.u32
          case _ => halt("Infeasible")
        }
        return toVal(t, conversions.U32.toZ(conversions.C.toU32(v.value)))
      case v: State.Value.R => return formatR(v.value)
      case v: State.Value.String =>
        val cs: ISZ[String] = for (c <- conversions.String.toCis(v.value)) yield smt2c(c)
        return st""""${(cs, "")}""""
      case _ =>
        halt(s"TODO: $v") // TODO
    }
  }

  @pure def smt2c(c: C): String = {
    c match {
      case '\t' =>
      case '\r' => return "\\r"
      case '\n' => return "\\n"
      case ' ' =>
      case '"' => return "\"\""
      case _ if ('\u0020' <= c && c <= '\u007E') || (c >= '\u0080') =>
      case _ =>
        halt(s"Unsupported character $c in string literal")
    }
    return c.string
  }

  @pure def escapeIdC(c: C): String = {
    c match {
      case '\\' => return "$backslash"
      case _ => return c.string
    }
  }

  @strictpure def escapeId(id: String): String = st"${(for (c <- conversions.String.toCis(id)) yield escapeIdC(c), "")}".render

  @memoize def ids2ST(ids: ISZ[String]): ST = {
    return st"${(for (id <- ids) yield escapeId(id), ".")}"
  }

  def shorten(ids: ISZ[String]): ST = {
    def rec(suffix: ISZ[String]): ST = {
      shortIds.get(suffix) match {
        case Some(other) =>
          if (other != ids) {
            if (suffix.size == ids.size) {
              shortIdsUp(shortIds + ids ~> ids)
              return ids2ST(ids)
            } else {
              return rec(ops.ISZOps(ids).takeRight(suffix.size + 1))
            }
          } else {
            return ids2ST(suffix)
          }
        case _ =>
          if (suffix == ISZ("Type") && ids.size != 1) {
            return rec(ops.ISZOps(ids).takeRight(suffix.size + 1))
          } else {
            shortIdsUp(shortIds + suffix ~> ids)
            return ids2ST(suffix)
          }
      }
    }
    return if (ids(0) === Smt2.topPrefix) ids2ST(ids) else rec(ISZ(ids(ids.size - 1)))
  }

  @pure def currentNameId(c: State.Claim.Let.CurrentName): ST = {
    return currentNameIdString(c.ids)
  }

  @pure def currentNameIdString(name: ISZ[String]): ST = {
    return if (Smt2.builtInCurrentNames.contains(name)) st"|${name(name.size - 2)}.${name(name.size - 1)}|"
    else st"|g:${(shorten(name), ".")}|"
  }

  @pure def currentLocalId(c: State.Claim.Let.CurrentId): ST = {
    return currentLocalIdString(c.context, c.id)
  }

  @pure def currentLocalIdString(context: ISZ[String], id: String): ST = {
    return if (context.isEmpty) st"|l:${escapeId(id)}|" else st"|l:${escapeId(id)}:${ids2ST(context)}|"
  }

  def localId(c: State.Claim.Let.Id): ST = {
    return if (c.context.isEmpty) st"|l:${escapeId(c.id)}@${State.Claim.possLines(c.poss)}#${c.num}|"
    else st"|l:${escapeId(c.id)}:${ids2ST(c.context)}@${State.Claim.possLines(c.poss)}#${c.num}|"
  }

  def nameId(c: State.Claim.Let.Name): ST = {
    return st"|g:${(shorten(c.ids), ".")}@${State.Claim.possLines(c.poss)}#${c.num}|"
  }

  def qvar2ST(x: State.Claim.Let.Quant.Var): ST = {
    x match {
      case x: State.Claim.Let.Quant.Var.Id => return st"${currentLocalIdString(x.context, x.id)}"
      case x: State.Claim.Let.Quant.Var.Sym => return st"${v2ST(x.sym)}"
    }
  }

  def enumId(owner: ISZ[String], id: String): ST = {
    return st"|e:${(shorten(owner), ".")}.${escapeId(id)}|"
  }

  def l2DeclST(c: State.Claim.Let,
               declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): ST = {
    c match {
      case c: State.Claim.Let.CurrentId if c.declId => return st"(${l2RhsST(c, v2ST _, HashMap.empty, declIds)} ${v2ST(c.sym)})"
      case _ => return st"(${v2ST(c.sym)} ${l2RhsST(c, v2ST _, HashMap.empty, declIds)})"
    }
  }

  def embeddedClaims(isImply: B,
                     claims: ISZ[State.Claim],
                     initSyms: ISZ[State.Value.Sym],
                     letsOpt: Option[HashMap[Z, ISZ[State.Claim.Let]]],
                     declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): ST = {
    def collectSyms(c: State.Claim, acc: ISZ[State.Value.Sym]): ISZ[State.Value.Sym] = {
      c match {
        case c: State.Claim.Let => return acc :+ c.sym
        case c: State.Claim.And =>
          var r = acc
          for (ca <- c.claims) {
            r = collectSyms(ca, r)
          }
          return r
        case c: State.Claim.Or =>
          var r = acc
          for (ca <- c.claims) {
            r = collectSyms(ca, r)
          }
          return r
        case c: State.Claim.Imply =>
          var r = acc
          for (ca <- c.claims) {
            r = collectSyms(ca, r)
          }
          return r
        case c: State.Claim.If =>
          var r = acc
          for (ca <- c.tClaims ++ c.fClaims) {
            r = collectSyms(ca, r)
          }
          return r
        case _: State.Claim.Label => return acc
        case _: State.Claim.Prop => return acc
      }
    }
    val lids = collectLids(claims) -- declIds.keys
    def raw: ST = {
      var lets = ISZ[State.Claim.Let]()
      var lsyms = ISZ[State.Value.Sym]()
      var syms = initSyms
      var rest = ISZ[State.Claim]()

      for (i <- 0 until claims.size) {
        claims(i) match {
          case claim: State.Claim.Let.Binary if Smt2.isSimpsOp(claim) => syms = syms :+ claim.sym; rest = rest :+ claim
          case claim: State.Claim.Let if i != claims.size - 1 => lsyms = lsyms :+ claim.sym; lets = lets :+ claim
          case claim: State.Claim.Let => syms = syms :+ claim.sym; rest = rest :+ claim
          case claim: State.Claim.If => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.And => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.Or => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.Imply => syms = collectSyms(claim, syms); rest = rest :+ claim
          case claim: State.Claim.Label => rest = rest :+ claim
          case claim: State.Claim.Prop => rest = rest :+ claim
        }
      }
      var body: ST =
        if (isImply) implyST(rest, v2ST _, HashMap.empty, declIds)
        else andST(rest, v2ST _, HashMap.empty, declIds)
      if (lets.nonEmpty) {
        val newDeclIds = lids ++ declIds.entries
        body =
          st"""(let (${l2DeclST(lets(lets.size - 1), newDeclIds)})
              |  $body)"""
        for (i <- (lets.size - 2) to 0 by -1) {
          val let = lets(i)
          body =
            st"""(let (${l2DeclST(let, newDeclIds)})
                |$body)"""
        }
      }
      val s = HashSSet.empty[State.Value.Sym] ++ syms -- lsyms
      if (s.nonEmpty) {
          val (decls, body2) = addTypeConstraints(isImply,
            (for (id <- lids.values) yield (localId(id), id.sym.tipe)) ++
              (for (sym <- s.elements) yield (v2ST(sym), sym.tipe)),
            body)
        body =
          st"""(${if (isImply) "forall" else "exists"} (${(decls, " ")})
              |  $body2)"""
      }
      return body
    }

    def simplified: ST = {
      var (lets, lsyms) = Util.collectLetClaims(simplifiedQuery, claims)
      letsOpt match {
        case Some(ls) =>
          for (p <- ls.entries) {
            val (k, s) = p
            lets = lets + k ~> (HashSet.empty[State.Claim.Let] ++ lets.get(k).getOrElse(ISZ()) ++ s).elements
          }
        case _ =>
      }
      val sv2ST = Util.value2ST(this, lets, HashSMap.empty)
      var simplifiedClaimSTs = ISZ[ST]()
      for (i <- 0 until (if (isImply) claims.size - 1 else claims.size)) {
        c2ST(claims(i), sv2ST, lets, declIds) match {
          case Some(st) => simplifiedClaimSTs = simplifiedClaimSTs :+ st
          case _ =>
        }
      }
      var r: ST =
        if (isImply) implySTH(simplifiedClaimSTs, c2ST(claims(claims.size - 1), sv2ST, lets, declIds))
        else andSTH(simplifiedClaimSTs)
      val uscdid = UsedSymsCurrentDeclIdCollector(HashSet.empty, ISZ())
      for (c <- claims) {
        uscdid.transformStateClaim(c)
      }
      val usedSyms = uscdid.syms
      val syms = lsyms.elements ++ (for (ds <- lets.values if ds.size > 1 && usedSyms.contains(ds(0).sym)) yield ds(0).sym)
      var decls: ISZ[ST] =
        (for (id <- lids.values) yield st"(${localId(id)} ${typeId(id.sym.tipe)})") ++
          (for (sym <- syms) yield st"(${v2ST(sym)} ${typeId(sym.tipe)})")
      for (cid <- uscdid.currentDeclIds) {
        decls = decls :+ st"(${currentLocalId(cid)} ${typeId(cid.sym.tipe)})"
      }
      if (decls.nonEmpty) {
        r =
          st"""(${if (isImply) "forall" else "exists"} (${(decls, " ")})
              |  $r)"""
      }
      return r
    }

    return if (simplifiedQuery) simplified else raw
  }

  @pure def addTypeConstraints(isImply: B, ps: ISZ[(ST, AST.Typed)], claim: ST): (ISZ[ST], ST) = {
    var varDecls = ISZ[ST]()
    var typeConstraints = ISZ[ST]()
    for (p <- ps) {
      val (x, tipe) = p
      val t = typeId(tipe)
      varDecls = varDecls :+ st"($x $t)"
      tipe match {
        case tipe: AST.Typed.Name if (tipe.ids == AST.Typed.isName || tipe.ids == AST.Typed.msName) && isAdtType(tipe.args(1)) =>
          typeConstraints = typeConstraints :+ st"(= (${sTypeOfName(tipe)} $x) ${typeHierarchyId(tipe)})"
        case tipe if isAdtType(tipe) =>
          typeConstraints = typeConstraints :+ st"(sub-type (type-of $x) ${typeHierarchyId(tipe)})"
        case _ =>
      }
    }
    return if (typeConstraints.nonEmpty)
      (varDecls,
        st"""(${if (isImply) "=>" else "and"}
            |  ${(typeConstraints, "\n")}
            |  $claim)""")
    else (varDecls, claim)
  }

  def l2RhsST(c: State.Claim.Let,
              v2st: State.Value => ST,
              lets: HashMap[Z, ISZ[State.Claim.Let]],
              declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): ST = {
    c match {
      case c: State.Claim.Let.SeqStore =>
        return st"(${typeOpId(c.seq.tipe, "up")} ${v2st(c.seq)} ${v2st(c.index)} ${v2st(c.element)})"
      case c: State.Claim.Let.FieldStore =>
        return st"(${typeOpId(c.adt.tipe, s"${c.id}_=")} ${v2st(c.adt)} ${v2st(c.value)})"
      case c: State.Claim.Let.SeqLit =>
        val newId = typeOpId(c.sym.tipe, s"new.${c.args.size}")
        return if (c.args.isEmpty) newId else st"($newId ${(for (arg <- c.args) yield st"${v2st(arg.index)} ${v2st(arg.value)}", " ")})"
      case c: State.Claim.Let.AdtLit =>
        val newId = typeOpId(c.sym.tipe, "new")
        return if (c.args.isEmpty) newId else st"($newId ${(for (arg <- c.args) yield v2st(arg), " ")})"
      case c: State.Claim.Let.CurrentName =>
        return currentNameId(c)
      case c: State.Claim.Let.Name =>
        return nameId(c)
      case c: State.Claim.Let.CurrentId =>
        return currentLocalId(c)
      case c: State.Claim.Let.Id =>
        return localId(c)
      case c: State.Claim.Let.Eq =>
        return v2st(c.value)
      case c: State.Claim.Let.TypeTest =>
        return st"(${if (c.isEq) "=" else "sub-type"} (type-of ${v2st(c.value)}) ${typeHierarchyId(c.tipe)})"
      case c: State.Claim.Let.Quant =>
        val (qvars, body) = addTypeConstraints(c.isAll, for (qvar <- c.vars) yield (qvar2ST(qvar), qvar.tipe),
          embeddedClaims(c.isAll, c.claims, ISZ(), Some(lets), declIds))
        return if (c.isAll)
          st"""(forall (${(qvars, " ")})
              |  $body
              |)"""
        else
          st"""(exists (${(qvars, " ")})
              |  $body
              |)"""
      case c: State.Claim.Let.Binary =>
        val op: String = c.op match {
          case AST.Exp.BinaryOp.Eq3 => AST.Exp.BinaryOp.Eq
          case AST.Exp.BinaryOp.Ne3 => AST.Exp.BinaryOp.Ne
          case _ => c.op
        }
        return if (Smt2.isSimpsOp(c)) v2ST(c.sym) else st"(${typeOpId(c.tipe, op)} ${v2st(c.left)} ${v2st(c.right)})"
      case c: State.Claim.Let.Unary =>
        return st"(${typeOpId(c.sym.tipe, s"unary_${c.op}")} ${v2st(c.value)})"
      case c: State.Claim.Let.SeqLookup =>
        return st"(${typeOpId(c.seq.tipe, "at")} ${v2st(c.seq)} ${v2st(c.index)})"
      case c: State.Claim.Let.FieldLookup =>
        return st"(${typeOpId(c.adt.tipe, c.id)} ${v2st(c.adt)})"
      case c: State.Claim.Let.SeqInBound =>
        return st"(${typeOpId(c.seq.tipe, "isInBound")} ${v2st(c.seq)} ${v2st(c.index)})"
      case c: State.Claim.Let.TupleLit =>
        return st"(${typeOpId(c.sym.tipe, "new")} ${(for (arg <- c.args) yield v2st(arg), " ")})"
      case c: State.Claim.Let.And =>
        return if (c.args.size == 0) Smt2.stFalse
        else if (c.args.size == 1) v2st(c.args(0))
        else st"(and ${(c.args.map(v2st), " ")})"
      case c: State.Claim.Let.Or =>
        return if (c.args.size == 0) Smt2.stTrue
        else if (c.args.size == 1) v2st(c.args(0))
        else st"(or ${(c.args.map(v2st), " ")})"
      case c: State.Claim.Let.Imply =>
        return st"(=> ${(c.args.map(v2st), " ")})"
      case c: State.Claim.Let.Ite =>
        return st"(ite ${v2st(c.cond)} ${v2st(c.left)} ${v2st(c.right)})"
      case c: State.Claim.Let.ProofFunApply =>
        return if (c.args.isEmpty) proofFunId(c.pf)
        else st"(${proofFunId(c.pf)} ${(for (arg <- c.args) yield v2st(arg), " ")})"
      case c: State.Claim.Let.Apply =>
        val args: ST =
          if (c.args.size == 1) v2st(c.args(0))
          else st"(${typeOpId(AST.Typed.Tuple(for (arg <- c.args) yield arg.tipe), c.id)} ${(for (arg <- c.args) yield v2st(arg), " ")})"
        return st"(select ${if (c.isLocal) currentLocalIdString(c.context, c.id) else currentNameIdString(c.context :+ c.id)} $args)"
      case _: State.Claim.Let.IApply =>
        halt("TODO") // TODO
      case _: State.Claim.Let.Random =>
        halt("Infeasible")
    }
  }

  def c2ST(c: State.Claim, v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]], declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): Option[ST] = {
    c match {
      case _: State.Claim.Let.Random =>
        return None()
      case c: State.Claim.Let =>
        c match {
          case c: State.Claim.Let.Binary if Smt2.isSimpsOp(c) =>
            return Some(st"(${typeOpId(c.tipe, c.op)} ${v2st(c.left)} ${v2st(c.right)} ${v2st(c.sym)})")
          case c: State.Claim.Let.CurrentId if c.declId =>
          case _ =>
            lets.get(c.sym.num) match {
              case Some(ls) if ls.size == 1 => return None()
              case _ =>
            }
        }
        val rhs: ST = c match {
          case c: State.Claim.Let.CurrentName =>
            return Some(st"(= ${currentNameId(c)} ${v2st(c.sym)})")
          case c: State.Claim.Let.Name =>
            return Some(st"(= ${nameId(c)} ${v2st(c.sym)})")
          case c: State.Claim.Let.CurrentId =>
            return Some(st"(= ${currentLocalId(c)} ${v2st(c.sym)})")
          case c: State.Claim.Let.Id =>
            return Some(st"(= ${localId(c)} ${v2st(c.sym)})")
          case _ => l2RhsST(c, v2st, lets, declIds)
        }
        return Some(st"(= ${v2st(c.sym)} $rhs)")
      case c: State.Claim.Prop =>
        return Some(if (c.isPos) v2st(c.value) else st"(not ${v2st(c.value)})")
      case _: State.Claim.Label =>
        return None()
      case c: State.Claim.If =>
        return Some(
          st"""(ite ${v2st(c.cond)}
              |  ${andST(c.tClaims, v2st, lets, declIds)}
              |  ${andST(c.fClaims, v2st, lets, declIds)}
              |)"""
        )
      case c: State.Claim.And => return Some(andST(c.claims, v2st, lets, declIds))
      case c: State.Claim.Or => return Some(orST(c.claims, v2st, lets, declIds))
      case c: State.Claim.Imply => return Some(implyST(c.claims, v2st, lets, declIds))
    }
  }

  def andSTH(sts: ISZ[ST]): ST = {
    if (sts.size == 0) {
      return Smt2.stTrue
    } else if (sts.size == 1) {
      return sts(0)
    } else {
      val r =
        st"""(and
            |  ${(sts, "\n")})"""
      return r
    }
  }

  def andST(cs: ISZ[State.Claim], v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]],
            declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): ST = {
    var sts = ISZ[ST]()
    for (c <- cs) {
      c2ST(c, v2st, lets, declIds) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    return andSTH(sts)
  }

  def orSTH(sts: ISZ[ST]): ST = {
    if (sts.size == 0) {
      return Smt2.stTrue
    } else if (sts.size == 1) {
      return sts(0)
    } else {
      val r =
        st"""(or
            |  ${(sts, "\n")})"""
      return r
    }
  }

  def orST(cs: ISZ[State.Claim], v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]],
           declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): ST = {
    var sts = ISZ[ST]()
    for (c <- cs) {
      c2ST(c, v2st, lets, declIds) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    return orSTH(sts)
  }

  def implySTH(sts: ISZ[ST], lastOpt: Option[ST]): ST = {
    if (sts.size == 0) {
      return lastOpt.getOrElse(Smt2.stTrue)
    } else {
      val sts2: ISZ[ST] = lastOpt match {
        case Some(st) => sts :+ st
        case _ => sts
      }
      val r =
        st"""(=>
            |  ${(sts2, "\n")})"""
      return r
    }
  }

  def implyST(cs: ISZ[State.Claim], v2st: State.Value => ST, lets: HashMap[Z, ISZ[State.Claim.Let]],
              declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id]): ST = {
    var sts = ISZ[ST]()
    for (i <- 0 until cs.size) {
      c2ST(cs(i), v2st, lets, declIds) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    if (sts.isEmpty) {
      return implySTH(ISZ(), None())
    } else if (sts.size === 1) {
      return implySTH(ISZ(), Some(sts(0)))
    } else {
      return implySTH(ops.ISZOps(sts).dropRight(1), Some(sts(sts.size - 1)))
    }
  }

  def c2DeclST(c: State.Claim): ISZ[(String, ST)] = {
    @pure def declareConst(n: ST, tipe: AST.Typed): ST = {
      val r: ST = tipe match {
        case tipe: AST.Typed.Name if (tipe.ids == AST.Typed.isName || tipe.ids == AST.Typed.msName) && isAdtType(tipe.args(1)) =>
          st"""(declare-const $n ${typeId(tipe)})
              |(assert (= (${sTypeOfName(tipe)} $n) ${typeHierarchyId(tipe)}))"""
        case _ =>
          if (isAdtType(tipe)) {
            st"""(declare-const $n ${typeId(tipe)})
                |(assert (sub-type (type-of $n) ${typeHierarchyId(tipe)}))"""
          } else {
            st"(declare-const $n ${typeId(tipe)})"
          }
      }

      return r
    }
    def def2DeclST(cDef: State.Claim.Let): ISZ[(String, ST)] = {
      val symST = v2ST(cDef.sym)
      return ISZ[(String, ST)](symST.render ~> st"(declare-const $symST ${typeId(cDef.sym.tipe)})")
    }
    c match {
      case _: State.Claim.Label => return ISZ()
      case c: State.Claim.Prop =>
        val vST = v2ST(c.value)
        return ISZ[(String, ST)](vST.render ~> st"(declare-const $vST B)")
      case c: State.Claim.If =>
        val condST = v2ST(c.cond)
        var r = ISZ[(String, ST)](condST.render ~> st"(declare-const $condST B)")
        for (tClaim <- c.tClaims) {
          r = r ++ c2DeclST(tClaim)
        }
        for (fClaim <- c.fClaims) {
          r = r ++ c2DeclST(fClaim)
        }
        return r
      case c: State.Claim.And => return for (claim <- c.claims; p <- c2DeclST(claim)) yield p
      case c: State.Claim.Or => return for (claim <- c.claims; p <- c2DeclST(claim)) yield p
      case c: State.Claim.Imply => return for (claim <- c.claims; p <- c2DeclST(claim)) yield p
      case c: State.Claim.Let.CurrentName =>
        if (Smt2.builtInCurrentNames.contains(c.ids)) {
          return def2DeclST(c)
        }
        var r = def2DeclST(c)
        val n = currentNameId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Let.Name =>
        var r = def2DeclST(c)
        val n = nameId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Let.CurrentId =>
        var r = def2DeclST(c)
        val n = currentLocalId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Let.Id =>
        var r = def2DeclST(c)
        val n = localId(c)
        val ns = n.render
        r = r :+ ns ~> declareConst(n, c.sym.tipe)
        return r
      case c: State.Claim.Let => return def2DeclST(c)
    }
  }

  @memoize def typeIdRaw(t: AST.Typed): ST = {
    Util.normType(t) match {
      case t: AST.Typed.Name =>
        val ids: ISZ[String] = if (t.ids.size === 1) Smt2.topPrefix +: t.ids else t.ids
        if (t.args.isEmpty) {
          return st"${(shorten(ids), ".")}"
        } else {
          return st"${(shorten(ids), ".")}[${(for (arg <- t.args) yield typeIdRaw(arg), ", ")}]"
        }
      case t: AST.Typed.TypeVar => return st"$$${t.id}"
      case t: AST.Typed.Enum => return st"${(shorten(t.name), ".")}"
      case t: AST.Typed.Tuple => return st"(${(for (arg <- t.args) yield typeIdRaw(arg), ", ")})"
      case t: AST.Typed.Fun => return st"${(for (arg <- t.args) yield typeIdRaw(arg), ", ")} => ${typeIdRaw(t.ret)}"
      case _ => halt(s"TODO: $t") // TODO
    }
  }

  @memoize def typeId(t: AST.Typed): ST = {
    Util.normType(t) match {
      case t: AST.Typed.Fun =>
        if (t.args.size === 1) {
          return st"(Array ${typeId(t.args(0))} ${typeId(t.ret)})"
        } else {
          return st"(Array ${typeId(AST.Typed.Tuple(t.args))} ${typeId(t.ret)})"
        }
      case _ => return id(t, "")
    }
  }

  @memoize def typeHierarchyId(t: AST.Typed): ST = {
    return id(t, "T")
  }

  @pure def id(t: AST.Typed, prefix: String): ST = {
    t match {
      case t: AST.Typed.Name =>
        val ids: ISZ[String] = if (t.ids.size === 1) Smt2.topPrefix +: t.ids else t.ids
        if (ids.size == 3 && t.args.isEmpty && ids(0) == "org" && ids(1) == "sireum") {
          return st"${ids(2)}"
        } else {
          if (t.args.nonEmpty) {
            return if (prefix == "") st"|${(shorten(ids), ".")}[${(for (arg <- t.args) yield typeIdRaw(arg), ", ")}]|"
            else st"|$prefix:${(shorten(ids), ".")}[${(for (arg <- t.args) yield typeIdRaw(arg), ", ")}]|"
          } else {
            return if (prefix == "") st"|${(ids, ".")}|" else st"|$prefix:${(ids, ".")}|"
          }
        }
      case t: AST.Typed.TypeVar => return st"$$${t.id}"
      case _ => return if (prefix == "") st"|${typeIdRaw(t)}|" else st"|$prefix:${typeIdRaw(t)}|"
    }
  }
}
