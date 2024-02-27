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
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.{TypeChecker, TypeHierarchy}
import org.sireum.logika.Logika.Reporter
import Util._

object Smt2 {

  type StrictPureMethods = HashSMap[State.ProofFun, (ST, ST)]

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
    AST.Typed.f64Name :+ "NaN", AST.Typed.f64Name :+ "PInf", AST.Typed.f64Name :+ "NInf"
  )

  val imsOps: HashSet[String] =
    HashSet.empty[String] ++
      ISZ(
        AST.Exp.BinaryOp.Append,
        AST.Exp.BinaryOp.AppendAll,
        AST.Exp.BinaryOp.Prepend,
        AST.Exp.BinaryOp.RemoveAll
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
        |(define-fun |C.>>>| ((x C) (y C)) C (bvlshr x y))
        |(define-fun |C.toZ| ((x C)) Z (bv2nat x))
        |(declare-fun |C.randomSeed(Z)| (Z) C)
        |(declare-fun |C.randomSeedBetween(Z, C, C)| (Z C C) C)"""

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
          |(define-fun |Z.%| ((x Z) (y Z)) Z (mod x y))
          |(declare-fun |Z.randomSeed(Z)| (Z) Z)
          |(declare-fun |Z.randomSeedBetween(Z, Z, Z)| (Z Z Z) Z)
          |(declare-fun |B.randomSeed(Z)| (Z) B)"""
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
          |(define-fun |Z.%| ((x Z) (y Z)) Z (bvsrem x y))
          |(declare-fun |Z.randomSeed(Z)| (Z) Z)
          |(declare-fun |Z.randomSeedBetween(Z, Z, Z)| (Z Z Z) Z)
          |(declare-fun |B.randomSeed(Z)| (Z) B)"""

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
        |(define-fun |R./| ((x R) (y R)) R (/ x y))
        |(declare-fun |R.randomSeed(Z)| (Z) R)
        |(declare-fun |R.randomSeedBetween(Z, R, R)| (Z R R) R)"""

  @pure def quotedEscape(s: String): String = {
    return ops.StringOps(s).replaceAllChars('|', '│')
  }

  val topPrefix: String = "_"

  val z3DefaultValidOpts: String = "z3"

  val z3DefaultSatOpts: String = "z3"

  val cvc4DefaultValidOpts: String = "cvc4,--full-saturate-quant"

  val cvc4DefaultSatOpts: String = "cvc4"

  val cvc5DefaultValidOpts: String = "cvc5,--full-saturate-quant"

  val cvc5DefaultSatOpts: String = "cvc5,--finite-model-find"

  val altErgoDefaultValidOpts: String = "alt-ergo"

  val altErgoDefaultSatOpts: String = "alt-ergo"

  val defaultValidOpts: String = s"$cvc4DefaultValidOpts; $z3DefaultValidOpts; $cvc5DefaultValidOpts"

  val defaultSatOpts: String = s"$z3DefaultSatOpts"

  val validTimeoutInMs: Z = 2000

  val satTimeoutInMs: Z = 500

  val rlimit: Z = 2000000

  val solverArgsMap: HashMap[String, ISZ[String]] = HashMap.empty[String, ISZ[String]] +
    "alt-ergo" ~> ISZ[String]("-i", "smtlib2") +
    "cvc4" ~> ISZ[String]("--lang=smt2.6") +
    "cvc5" ~> ISZ[String]("--lang=smt2.6") +
    "z3" ~> ISZ("-smt2", "-in")

  def solverArgs(name: String, timeoutInMs: Z, rlimit: Z): Option[ISZ[String]] = {
    name match {
      case string"alt-ergo" =>
        var timeoutInS: Z = timeoutInMs / 1000
        if (timeoutInMs % 1000 != 0) {
          timeoutInS = timeoutInS + 1
        }
        return Some(solverArgsMap.get(name).get ++ ISZ("--steps-bound", rlimit.string, "--timelimit", timeoutInS.string))
      case string"cvc4" => return Some(solverArgsMap.get(name).get ++ ISZ(s"--rlimit=$rlimit", s"--tlimit=$timeoutInMs"))
      case string"cvc5" => return Some(solverArgsMap.get(name).get ++ ISZ(s"--rlimit=$rlimit", s"--tlimit=$timeoutInMs"))
      case string"z3" => return Some(solverArgsMap.get(name).get ++ ISZ(s"rlimit=$rlimit", s"-t:$timeoutInMs"))
      case _ => return None()
    }
  }

  def parseConfigs(nameExePathMap: HashMap[String, String],
                   isSat: B,
                   options: String): Either[ISZ[Smt2Config], String] = {
    var r = ISZ[Smt2Config]()
    for (option <- ops.StringOps(options).split((c: C) => c == ';')) {
      val opts: ISZ[String] =
        for (e <- ops.StringOps(ops.StringOps(option).trim).split((c: C) => c == ',')) yield ops.StringOps(e).trim
      opts match {
        case ISZ(name, _*) =>
          solverArgs(name, validTimeoutInMs, rlimit) match {
            case Some(_) =>
              nameExePathMap.get(name) match {
                case Some(exe) => r = r :+ Smt2Config(isSat, name, exe, ops.ISZOps(opts).drop(1))
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
    st"""(assert (forall ((o $tid)) ($eq o o)))
        |(assert (forall ((o1 $tid) (o2 $tid)) (= ($eq o1 o2) ($eq o2 o1))))
        |(assert(forall ((o1 $tid) (o2 $tid) (o3 $tid)) (=> ($eq o1 o2) ($eq o2 o3) ($eq o1 o3))))"""

  @strictpure def eqTypeOfThProp(eq: ST, tid: ST, trel: String, typeofName: ST, thid: ST): ST =
    st"""(assert (forall ((o $tid)) (=> ($trel ($typeofName o) $thid) ($eq o o))))
        |(assert (forall ((o1 $tid) (o2 $tid)) (=> ($trel ($typeofName o1) $thid) ($trel ($typeofName o2) $thid) (= ($eq o1 o2) ($eq o2 o1)))))
        |(assert(forall ((o1 $tid) (o2 $tid) (o3 $tid)) (=> ($trel ($typeofName o1) $thid) ($trel ($typeofName o2) $thid) ($trel ($typeofName o3) $thid) ($eq o1 o2) ($eq o2 o3) ($eq o1 o3))))"""

  @strictpure def eqThProp(eq: ST, tid: ST, trel: String, thid: ST): ST = eqTypeOfThProp(eq, tid, trel, st"type-of", thid)
}

@msig trait Smt2 {

  def minimize: Smt2

  @strictpure def f32ST(useReal: B, fpRoundingMode: String): ST = if (useReal) {
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
        |(define-fun |F32.~~| ((x F32) (y F32)) B (= x y))
        |(define-fun |F32.!~| ((x F32) (y F32)) B (not (= x y)))
        |(define-fun |F32.+| ((x F32) (y F32)) F32 (+ x y))
        |(define-fun |F32.-| ((x F32) (y F32)) F32 (- x y))
        |(define-fun |F32.*| ((x F32) (y F32)) F32 (* x y))
        |(define-fun |F32./| ((x F32) (y F32)) F32 (/ x y))
        |(declare-fun |F32.%| (F32 F32) F32)
        |(declare-fun |F32.randomSeed(Z)| (Z) F32)
        |(declare-fun |F32.randomSeedBetween(Z, F32, F32)| (Z F32 F32) F32)"""
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
        |(define-fun |F32.==| ((x F32) (y F32)) B (= x y))
        |(define-fun |F32.!=| ((x F32) (y F32)) B (not (= x y)))
        |(define-fun |F32.~~| ((x F32) (y F32)) B (fp.eq x y))
        |(define-fun |F32.!~| ((x F32) (y F32)) B (not (fp.eq x y)))
        |(define-fun |F32.+| ((x F32) (y F32)) F32 (fp.add $fpRoundingMode x y))
        |(define-fun |F32.-| ((x F32) (y F32)) F32 (fp.sub $fpRoundingMode x y))
        |(define-fun |F32.*| ((x F32) (y F32)) F32 (fp.mul $fpRoundingMode x y))
        |(define-fun |F32./| ((x F32) (y F32)) F32 (fp.div $fpRoundingMode x y))
        |(define-fun |F32.%| ((x F32) (y F32)) F32 (fp.rem x y))
        |(declare-fun |F32.randomSeed(Z)| (Z) F32)
        |(declare-fun |F32.randomSeedBetween(Z, F32, F32)| (Z F32 F32) F32)"""
  }

  @strictpure def f64ST(useReal: B, fpRoundingMode: String): ST = if (useReal) {
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
        |(define-fun |F64.~~| ((x F64) (y F64)) B (= x y))
        |(define-fun |F64.!~| ((x F64) (y F64)) B (not (= x y)))
        |(define-fun |F64.+| ((x F64) (y F64)) F64 (+ x y))
        |(define-fun |F64.-| ((x F64) (y F64)) F64 (- x y))
        |(define-fun |F64.*| ((x F64) (y F64)) F64 (* x y))
        |(define-fun |F64./| ((x F64) (y F64)) F64 (/ x y))
        |(declare-fun |F64.%| (F64 F64) F64)
        |(declare-fun |F64.randomSeed(Z)| (Z) F64)
        |(declare-fun |F64.randomSeedBetween(Z, F64, F64)| (Z F64 F64) F64)"""
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
        |(define-fun |F64.==| ((x F64) (y F64)) B (= x y))
        |(define-fun |F64.!=| ((x F64) (y F64)) B (not (= x y)))
        |(define-fun |F64.~~| ((x F64) (y F64)) B (fp.eq x y))
        |(define-fun |F64.!~| ((x F64) (y F64)) B (not (fp.eq x y)))
        |(define-fun |F64.+| ((x F64) (y F64)) F64 (fp.add $fpRoundingMode x y))
        |(define-fun |F64.-| ((x F64) (y F64)) F64 (fp.sub $fpRoundingMode x y))
        |(define-fun |F64.*| ((x F64) (y F64)) F64 (fp.mul $fpRoundingMode x y))
        |(define-fun |F64./| ((x F64) (y F64)) F64 (fp.div $fpRoundingMode x y))
        |(define-fun |F64.%| ((x F64) (y F64)) F64 (fp.rem x y))
        |(declare-fun |F64.randomSeed(Z)| (Z) F64)
        |(declare-fun |F64.randomSeedBetween(Z, F64, F64)| (Z F64 F64) F64)"""
  }

  @pure def emptyCache(config: Config): Smt2

  def types: HashSet[AST.Typed]

  def typesUp(newTypes: HashSet[AST.Typed]): Unit

  def poset: Poset[AST.Typed.Name]

  def posetUp(newPoset: Poset[AST.Typed.Name]): Unit

  def sorts: HashSMap[AST.Typed, ISZ[ST]]

  def sortsUp(newSorts: HashSMap[AST.Typed, ISZ[ST]]): Unit

  def seqLits: HashSSet[Smt2.SeqLit]

  def seqLitsUp(newSeqLits: HashSSet[Smt2.SeqLit]): Unit

  def adtDecls: HashSMap[AST.Typed.Name, ISZ[ST]]

  def adtDeclsUp(newAdtDecls: HashSMap[AST.Typed.Name, ISZ[ST]]): Unit

  def typeDecls: HashSMap[AST.Typed, ISZ[ST]]

  def typeDeclsUp(newTypeDecls: HashSMap[AST.Typed, ISZ[ST]]): Unit

  def sTypeDecls: HashSMap[AST.Typed.Name, ISZ[ST]]

  def sTypeDeclsUp(newTypeDecls: HashSMap[AST.Typed.Name, ISZ[ST]]): Unit

  def pureFuns: HashSMap[State.ProofFun, (ST, ST)]

  def pureFunsUp(newProofFuns: HashSMap[State.ProofFun, (ST, ST)]): Unit

  def constraints: HashSMap[AST.Typed, ISZ[ST]]

  def constraintsUp(newConstraints: HashSMap[AST.Typed, ISZ[ST]]): Unit

  def writeFile(dir: String, filename: String, content: String): Unit

  def filenameCount: HashMap[String, Z]

  //def withConfig(isSat: B, options: String, timeout: Z, resourceLimit: Z, reporter: Reporter): MEither[Smt2, String]

  def combineWith(that: Smt2): Unit

  def updateFrom(that: Smt2): Unit

  def plugins: ISZ[plugin.ClaimPlugin]

  @pure def proofFunId(pf: State.ProofFun): ST = {
    val targs: ST = pf.receiverTypeOpt match {
      case Some(receiverType: AST.Typed.Name) =>
        if (receiverType.args.isEmpty) st"#"
        else st"[${(for (arg <- receiverType.args) yield typeIdRaw(arg), ", ")}]#"
      case _ => st"."
    }
    val pTypes: ST = st"(${(for (pt <- pf.paramTypes) yield typeIdRaw(pt), ", ")})"
    val context: ISZ[String] = if (pf.context.size == 3 && pf.context(0) == "org" && pf.context(1) == "sireum") ISZ(pf.context(2)) else pf.context
    return if (context.isEmpty) st"|${pf.id}$pTypes|" else st"|${(context, ".")}$targs${pf.id}$pTypes|"
  }

  def addProofFunDecl(config: Config, pf: State.ProofFun, sym: State.Value.Sym, invClaims: ISZ[State.Claim],
                      reporter: Reporter): (ST, ST) = {
    pf.receiverTypeOpt match {
      case Some(rt) => addType(config, rt, reporter)
      case _ =>
    }
    for (pt <- pf.paramTypes) {
      addType(config, pt, reporter)
    }
    addType(config, pf.returnType, reporter)

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
    val (decls, claim) = addTypeConstraints(T, paramIdTypes :+ ((v2ST(config, sym, reporter), pf.returnType)),
      st"""(=>
          |    (= ${v2ST(config, sym, reporter)} $app)
          |    ${embeddedClaims(config, F, T, invClaims, ISZ(), None(), HashSMap.empty, reporter)})"""
    )
    val declClaim: ST = if (invClaims.size == 0) st"" else
      st"""(assert (forall (${(decls, " ")})
          |  $claim
          |))"""
    val decl = st"(declare-fun $id (${(for (p <- paramIdTypes) yield adtId(p._2), " ")}) ${adtId(pf.returnType)})"
    pureFunsUp(pureFuns + pf ~> ((decl, declClaim)))
    return (decl, declClaim)
  }

  def addProofFun(config: Config, pos: message.Position, pf: State.ProofFun, svs: ISZ[(State, State.Value.Sym)],
                  statePrefix: Z, decl: ST, declClaim: ST, reporter: Reporter): Unit = {
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
    var ecs = ISZ[ST]()
    val nlc = NonLocalIdCollector(pf.context :+ pf.id, HashSSet.empty)
    for (sv <- svs if sv._1.ok) {
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
      val claims = State.Claim.Imply(F, ISZ(
        State.Claim.And(ops.ISZOps(s1.claims).slice(statePrefix, s1.claims.size)),
        State.Claim.Let.Def(v, v3)
      ))
      nlc.transformStateClaim(claims)
      ecs = ecs :+ embeddedClaims(config, T, T, ISZ(claims), ISZ(), None(), HashSMap.empty, reporter)
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
    val claim: ST = if (paramIdTypes.nonEmpty || nlc.nonLocals.nonEmpty) {
      val (decls, ec2) = addTypeConstraints(T, for (t <- paramIdTypes) yield (t._2, t._3), ec)
      st"""$declClaim
          |(assert (forall (${(decls ++ (for (id <- nlc.nonLocals.elements) yield st"(${localId(id)} ${typeId(id.sym.tipe)})"), " ")})
          |  $ec2))"""
    } else {
      st"""$declClaim
          |(assert $ec)"""
    }
    pureFunsUp(pureFuns + pf ~> ((decl, claim)))
  }

  def addSort(key: AST.Typed, d: ST): Unit = {
    val decls = sorts
    val newSorts: HashSMap[AST.Typed, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts :+ d)
      case _ => decls + key ~> ISZ(d)
    }
    sortsUp(newSorts)
  }

  def addAdtDecl(key: AST.Typed.Name, d: ST): Unit = {
    val decls = adtDecls
    val newAdtDecls: HashSMap[AST.Typed.Name, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts :+ d)
      case _ => decls + key ~> ISZ(d)
    }
    adtDeclsUp(newAdtDecls)
  }

  def addAdtDecls(key: AST.Typed.Name, ds: ISZ[ST]): Unit = {
    val decls = adtDecls
    val newAdtDecls: HashSMap[AST.Typed.Name, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts ++ ds)
      case _ => decls + key ~> ds
    }
    adtDeclsUp(newAdtDecls)
  }

  def addSTypeDecl(key: AST.Typed.Name, d: ST): Unit = {
    val decls = sTypeDecls
    val newSTypeDecls: HashSMap[AST.Typed.Name, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts :+ d)
      case _ => decls + key ~> ISZ(d)
    }
    sTypeDeclsUp(newSTypeDecls)
  }

  def addSTypeDecls(key: AST.Typed.Name, ds: ISZ[ST]): Unit = {
    val decls = sTypeDecls
    val newSTypeDecls: HashSMap[AST.Typed.Name, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts ++ ds)
      case _ => decls + key ~> ds
    }
    sTypeDeclsUp(newSTypeDecls)
  }

  def addTypeDecl(key: AST.Typed, d: ST): Unit = {
    val decls = typeDecls
    val newTypeDecls: HashSMap[AST.Typed, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts :+ d)
      case _ => decls + key ~> ISZ(d)
    }
    typeDeclsUp(newTypeDecls)
  }

  def addTypeDecls(key: AST.Typed, ds: ISZ[ST]): Unit = {
    val decls = typeDecls
    val newTypeDecls: HashSMap[AST.Typed, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts ++ ds)
      case _ => decls + key ~> ds
    }
    typeDeclsUp(newTypeDecls)
  }

  def addConstraint(key: AST.Typed, d: ST): Unit = {
    val decls = constraints
    val newConstraints: HashSMap[AST.Typed, ISZ[ST]] = decls.get(key) match {
      case Some(sts) => decls + key ~> (sts :+ d)
      case _ => decls + key ~> ISZ(d)
    }
    constraintsUp(newConstraints)
  }

  def typeHierarchyNamesUp(entry : (ISZ[String], Info)): Unit

  def typeHierarchyIds: HashSMap[AST.Typed, ST]

  def typeHierarchyIdsUp(newTypeHierarchyIds: HashSMap[AST.Typed, ST]): Unit

  def addTypeHierarchyId(key: AST.Typed, tId: ST): Unit = {
    typeHierarchyIdsUp(typeHierarchyIds + key ~> tId)
  }

  def shortIds: HashMap[ISZ[String], ISZ[String]]

  def shortIdsUp(newShortIds: HashMap[ISZ[String], ISZ[String]]): Unit

  def addShortIds(ids: ISZ[String], shortenedIds: ISZ[String]): Unit = {
    shortIdsUp(shortIds + ids ~> shortenedIds)
  }

  def addSeqLit(config: Config, t: AST.Typed.Name, n: Z, reporter: Reporter): Unit = {
    addType(config, t, reporter)
    seqLitsUp(seqLits + Smt2.SeqLit(t, n))
  }

  def typeHierarchy: TypeHierarchy

  def checkSat(config: Config, timeoutInMs: Z, query: String): Smt2Query.Result

  def checkUnsat(config: Config, timeoutInMs: Z, query: String): Smt2Query.Result

  def formatVal(width: Z, n: Z): ST

  def formatF32(config: Config, value: F32): ST

  def formatF64(config: Config, value: F64): ST

  def formatR(value: R): ST

  def formatTime(value: Z): ST

  @memoize def adtId(tipe: AST.Typed): ST = {
    tipe match {
      case tipe: AST.Typed.Name if typeHierarchy.isAdt(tipe) => return st"ADT"
      case _ => return typeId(tipe)
    }
  }

  @memoize def typeOpId(tipe: AST.Typed, op: String): ST = {
    return st"|${typeIdRaw(tipe)}.${Smt2.quotedEscape(op)}|"
  }

  @memoize def adtTypeOpId(t: AST.Typed, op: String): ST = {
    return if (typeHierarchy.isAdtType(t)) st"|ADT.${Smt2.quotedEscape(op)}|" else typeOpId(t, op)
  }

  def satResult(context: ISZ[String], config: Config, cache: Logika.Cache, timeoutInMs: Z, reportQuery: B,
                title: String, pos: message.Position, claims: ISZ[State.Claim], reporter: Reporter): (B, Smt2Query.Result) = {
    var cached = F
    def header(smt2res: Smt2Query.Result): String = {
      return st"""; Satisfiability check for $title
                 |${smt2res.info}
                 |; Time: ${formatTime(smt2res.timeMillis)}""".render
    }
    var smt2res = Smt2Query.Result.empty
    if (config.smt2Caching) {
      cache.getSmt2(T, typeHierarchy, config, timeoutInMs, claims) match {
        case Some(res) =>
          cached = T
          smt2res = res(info = header(smt2res))
        case _ =>
      }
    }
    if (!cached) {
      smt2res = checkSat(config, timeoutInMs, satQuery(config, claims, None(), reporter).render)
    }
    val r: B = smt2res.kind match {
      case Smt2Query.Result.Kind.Unsat => F
      case Smt2Query.Result.Kind.Sat => T
      case Smt2Query.Result.Kind.Error => F
      case Smt2Query.Result.Kind.Timeout => T
      case Smt2Query.Result.Kind.Unknown => T
    }
    if (cached) {
      if (reportQuery) {
        reporter.query(pos, title, T, smt2res.timeMillis, F, config.elideEncoding, smt2res)
      }
      return (r, smt2res)
    }
    val queryOpt: Option[String] = if (config.elideEncoding && r) None() else Some(smt2res.query)
    val res = smt2res(info = header(smt2res), query =
      st"""${if (config.rawInscription) toClaimST(F, claims, pos) else toExpST(config, F, context, claims, pos)}
          |$queryOpt""".render
    )
    if (reportQuery || config.logVc) {
      reporter.query(pos, title, T, smt2res.timeMillis, F, config.elideEncoding, res)
    }
    config.logVcDirOpt match {
      case Some(logDir) =>
        val filename: String =
          if (ops.StringOps(title).contains("[")) s"sat-$title"
          else s"sat-$title-at-${pos.beginLine}-${pos.beginColumn}"
        writeFile(logDir, filename, s"${res.info}\n${res.query}")
      case _ =>
    }
    if (config.smt2Caching && res.solverName != "none") {
      cache.setSmt2(T, typeHierarchy, config, timeoutInMs, claims, res)
    }
    return (r, smt2res)
  }

  def sat(context: ISZ[String], config: Config, cache: Logika.Cache, reportQuery: B,
          title: String, pos: message.Position, claims: ISZ[State.Claim], reporter: Reporter): B = {
    val (status, r) = satResult(context, config, cache,
      if (config.satTimeout) config.timeoutInMs else Smt2.satTimeoutInMs, reportQuery, title, pos, claims, reporter)
    if (r.kind == Smt2Query.Result.Kind.Error) {
      reporter.error(Some(pos), Logika.kind, s"Error occurred when doing ${ops.StringOps(title).firstToLower}")
    }
    return status
  }

  def toVal(config: Config, t: AST.Typed.Name, n: Z): ST = {
    val bw: Z = if (t == AST.Typed.z) {
      config.intBitWidth
    } else {
      val ast = typeHierarchy.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.SubZ].ast
      if (!ast.isBitVector) config.intBitWidth else ast.bitWidth
    }
    return formatVal(bw, n)
  }

  @pure def sTypeOfName(t: AST.Typed): ST = {
    t match {
      case t: AST.Typed.Name => return st"|type-of-${t.ids(t.ids.size - 1)}-${typeIdRaw(t.args(0))}-${typeIdRaw(t.args(1))}|"
      case _ => halt("Infeasible")
    }
  }

  @pure def tupleTypeOfName(t: AST.Typed): ST = {
    t match {
      case t: AST.Typed.Tuple => return st"|type-of-${typeIdRaw(t)}|"
      case _ => halt("Infeasible")
    }
  }

  def addType(config: Config, typed: AST.Typed, reporter: message.Reporter): Unit = {
    def addTypeH(tipe: AST.Typed): Unit = {
      def addS(t: AST.Typed.Name): Unit = {
        val it = t.args(0)
        val (itInt, capOpt): (B, Option[Z]) = if (it == AST.Typed.z) {
          (T, None())
        } else {
          it match {
            case it: AST.Typed.Name =>
              typeHierarchy.typeMap.get(it.ids) match {
                case Some(info: TypeInfo.SubZ) => (!info.ast.isBitVector, info.ast.capacityOpt)
                case _ => (F, None())
              }
            case _ => (F, None())
          }
        }
        addTypeH(it)
        val et = t.args(1)
        addTypeH(et)
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
        val itEqId = st"="
        val itAddId = typeOpId(it, "+")
        val itSubId = typeOpId(it, "-")
        val it2zId = typeOpId(it, "toZ")
        val firstIndexId = typeOpId(t, "firstIndex")
        val lastIndexId = typeOpId(t, "lastIndex")
        val zZero = toVal(config, AST.Typed.z, 0)
        val zOne = toVal(config, AST.Typed.z, 1)
        val zAddId = typeOpId(AST.Typed.z, "+")
        val zSubId = typeOpId(AST.Typed.z, "-")
        val zGeId = typeOpId(AST.Typed.z, ">=")
        val zGtId = typeOpId(AST.Typed.z, ">")
        val zEqId = typeOpId(AST.Typed.z, "==")
        val etThid = typeHierarchyId(et)
        val etEqId: ST = typeOpId(et, "==")
        val (etAdt, etS, etTuple): (B, B, B) = et match {
          case et: AST.Typed.Name => (typeHierarchy.isAdt(et), et.ids == AST.Typed.isName || et.ids == AST.Typed.msName, F)
          case _: AST.Typed.Tuple => (F, F, T)
          case _ => (F, F, F)
        }
        val typeofName = sTypeOfName(t)
        addTypeHierarchyId(t, thId)
        addSort(t, st"(define-sort $tId () (Array $itId $etId))")
        addSort(t, st"""(declare-const $thId Type)""")
        addSort(t, st"""(declare-fun $typeofName ($tId) Type)""")

        @pure def etThidSubtypeOpt(x: String): Option[ST] = {
          return if (etAdt) Some(st"(${if (typeHierarchy.isAdtLeafType(et)) "=" else "sub-type"} (type-of $x) $etThid)")
          else if (etS) Some(st"(= (${sTypeOfName(et)} $x) $etThid)")
          else if (etTuple) Some(st"(= (${tupleTypeOfName(et)} $x) $etThid)")
          else None()
        }

        @strictpure def thidTypeOpt(x: String): ST = st"(= ($typeofName $x) $thId)"

        addSTypeDecl(t, st"(declare-fun $sizeId ($tId) Z)")
        addSTypeDecl(t, st"(assert (forall ((x $tId)) ($zGeId ($sizeId x) $zZero)))")
        capOpt match {
          case Some(capacity) => addSTypeDecl(t, st"(assert (forall ((x $tId)) ($zGeId $capacity ($sizeId x))))")
          case _ =>
        }
        addSTypeDecl(t, st"(declare-fun $firstIndexId ($tId) $itId)")
        addSTypeDecl(t, st"(declare-fun $lastIndexId ($tId) $itId)")
        val (_, itOne): (ST, ST) = it match {
          case it: AST.Typed.Name =>
            if (it == AST.Typed.z) {
              val min = toVal(config, it, 0)
              addSTypeDecl(t, st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($firstIndexId x) $min))))")
              addSTypeDecl(t, st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($lastIndexId x) ($zSubId ($sizeId x) $zOne)))))")
              addSTypeDecl(t, st"(define-fun $atZId ((x $tId) (y $itId)) $etId (select x y))")
              (min, toVal(config, it, 1))
            } else {
              val ti = typeHierarchy.typeMap.get(it.ids).get.asInstanceOf[TypeInfo.SubZ]
              val min: ST = if (ti.ast.isZeroIndex) toVal(config, it, 0) else currentNameIdString(it.ids :+ "Min")
              addSTypeDecl(t, st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($firstIndexId x) $min))))")
              addSTypeDecl(t, st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($it2zId ($lastIndexId x)) ($zSubId ($sizeId x) $zOne)))))")
              addSTypeDecl(t, st"(declare-fun $atZId ($tId $itId) $etId)")
              (min, toVal(config, it, 1))
            }
          case it: AST.Typed.TypeVar =>
            val min = currentNameIdString(ISZ(it.id, "Min"))
            addSTypeDecl(t, st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($firstIndexId x) $min))))")
            addSTypeDecl(t, st"(assert (forall ((x $tId)) (=> (not ($zEqId ($sizeId x) $zZero)) (= ($it2zId ($lastIndexId x)) ($zSubId ($sizeId x) $zOne)))))")
            addSTypeDecl(t, st"(declare-fun $atZId ($tId $itId) $etId)")
            (min, typeOpId(it, "1"))
          case _ => halt(s"Infeasible: $it")
        }
        addSTypeDecl(t, st"(define-fun $isInBoundId ((x $tId) (y $itId)) B (and ($zGtId ($sizeId x) 0) ($itLeId ($firstIndexId x) y) ($itLeId y ($lastIndexId x))))")
        addSTypeDecl(t, st"(define-fun $atId ((x $tId) (y $itId)) $etId (select x y))")
        addTypeDecl(t,
          st"""(define-fun $appendId ((x $tId) (y $etId) (z $tId)) B
              |  (and
              |    ${thidTypeOpt("z")}
              |    ($itEqId ($sizeId z) ($zAddId ($sizeId x) $zOne))
              |    (forall ((i $itId)) (=> ($isInBoundId x i)
              |                        (= ($atId z i) ($atId x i))))
              |    (= ($atId z ($lastIndexId z)) y)))""")
        if (itInt) {
          addTypeDecl(t,
            st"""(define-fun $appendsId ((x $tId) (y $tId) (z $tId)) B
                |  (and
                |    ${thidTypeOpt("z")}
                |    (= ($sizeId z) ($zAddId ($sizeId x) ($sizeId y)))
                |    (forall ((i $itId)) (=> ($isInBoundId x i)
                |                            (= ($atId z i) ($atId x i))))
                |    (forall ((i $itId)) (=> ($isInBoundId y i)
                |                            (= ($atId z (+ ($sizeId x) i)) ($atId y i))))))""")
        } else {
          addTypeDecl(t,
            st"""(define-fun $appendsId ((x $tId) (y $tId) (z $tId)) B
                |  (and
                |    ${thidTypeOpt("z")}
                |    (= ($sizeId z) ($zAddId ($sizeId x) ($sizeId y)))
                |    (forall ((i $itId)) (=> ($isInBoundId x i)
                |                            (= ($atId z i) ($atId x i))))
                |    (forall ((i $itId)) (=> ($isInBoundId y i)
                |                            (= ($atId z ($itAddId ($itAddId ($lastIndexId x) ($itSubId i ($firstIndexId y))) $itOne)) ($atId y i))))))""")
        }
        addTypeDecl(t,
          st"""(define-fun $prependId ((x $etId) (y $tId) (z $tId)) B
              |  (and
              |    ${thidTypeOpt("z")}
              |    (= ($sizeId z) ($zAddId ($sizeId y) 1))
              |    (forall ((i $itId)) (=> ($isInBoundId y i)
              |                            (= ($atId z ($itAddId i $itOne)) ($atId y i))))
              |    (= ($atId z ($firstIndexId z)) x)))""")
        addTypeDecl(t,
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
        addTypeDecl(t,
          st"""(define-fun $eqId ((x $tId) (y $tId)) B
              |  (and
              |    (= ($sizeId x) ($sizeId y))
              |    (=> (not (= 0 ($sizeId x))) ($itEqId ($lastIndexId x) ($lastIndexId y)))
              |    (forall ((i $itId)) (=> ($isInBoundId x i) ($etEqId (select x i) (select y i))))))
              |(assert (forall ((x $tId) (y $tId)) (=> ${thidTypeOpt("x")} ${thidTypeOpt("y")} (= x y) ($eqId x y))))""")
        addTypeDecl(t, st"""(define-fun $neId ((x $tId) (y $tId)) B (not ($eqId x y)))""")
        if (typeHierarchy.isSubstitutableWithoutSpecVars(et)) {
          addTypeDecl(t,
            st"""(assert (forall ((x $tId) (y $tId))
                |  (=>
                |    ${thidTypeOpt("x")}
                |    ${thidTypeOpt("y")}
                |    ($eqId x y)
                |    (= x y))))""")
        }
        if (etAdt || etS) {
          addTypeDecl(t,
            st"""(assert (forall ((x $tId) (i $itId) (v $etId))
                |  (=>
                |    ${thidTypeOpt("x")}
                |    ($isInBoundId x i)
                |    (= ($atId x i) v)
                |    ${etThidSubtypeOpt("v")})))
                |(assert (forall ((x $tId) (y $tId) (i $itId))
                |  (=>
                |    ${thidTypeOpt("x")}
                |    ${thidTypeOpt("y")}
                |    (= ($sizeId x) ($sizeId y))
                |    (not ($isInBoundId x i))
                |    (not ($isInBoundId y i))
                |    (= ($atId x i) ($atId y i)))))""")
        } else {
          addTypeDecl(t,
            st"""(assert (forall ((x $tId) (y $tId) (i $itId))
                |  (=>
                |    (= ($sizeId x) ($sizeId y))
                |    (not ($isInBoundId x i))
                |    (not ($isInBoundId y i))
                |    (= ($atId x i) ($atId y i)))))""")
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
            addTypeH(p)
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
                addTypeH(childT)
                val childThId = typeHierarchyId(childT)
                addConstraint(t,
                  st"""(assert (forall ((o1 ADT) (o2 ADT))
                      |  (=> (sub-type (type-of o1) $childThId)
                      |      (sub-type (type-of o2) $childThId)
                      |      (= (${typeOpId(t, "==")} o1 o2) (${typeOpId(childT, "==")} o1 o2)))
                      |))"""
                )
                addConstraint(t,
                  st"""(assert (forall ((o1 ADT) (o2 ADT))
                      |  (=> (sub-type (type-of o1) $childThId)
                      |      (not (sub-type (type-of o2) $childThId))
                      |      (= (${typeOpId(t, "==")} o1 o2) false))
                      |))"""
                )
              } else {
                hasChild = T
                addTypeH(tipe)
              }
            }
          }
          if (!hasChild && children.isEmpty && t != AST.Typed.nothing && t != AST.Typed.string && t != AST.Typed.st) {
            reporter.warn(posOpt, Logika.kind, s"$t does not have any concrete implementation")
          }
          posetUp(poset.addChildren(t, children))
          addTypeDecls(t, for (child <- children) yield st"(assert (sub-type ${typeHierarchyId(child)} $tId))")
        }
      }

      def addAdt(t: AST.Typed.Name, ti: TypeInfo.Adt): Unit = {
        val sm = TypeChecker.buildTypeSubstMap(t.ids, None(), ti.ast.typeParams, t.args, reporter).get
        val thId = typeHierarchyId(t)
        addTypeHierarchyId(t, thId)
        addSort(t, st"(declare-const $thId Type)")
        addSub(ti.posOpt, ti.ast.isRoot, t, thId, ti.parents, sm)
        for (arg <- t.args) {
          addTypeH(arg.subst(sm))
        }
        for (v <- ti.vars.values) {
          addTypeH(v.typedOpt.get.subst(sm))
        }
        for (v <- ti.specVars.values) {
          addTypeH(v.typedOpt.get.subst(sm))
        }
        posetUp(poset.addNode(t))
        val tId = typeId(t)
        addSort(t, st"(define-sort $tId () ADT)")
        if (!ti.ast.isRoot) {
          addAdtDecl(t, st"(assert (forall ((x ${typeId(t)})) (= (sub-type (type-of x) $thId) (= (type-of x) $thId))))")
        }

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
          addAdtDecl(t,
            st"""(declare-fun $eqId ($tId $tId) B)
                |(assert (forall ((x $tId) (y $tId)) (=> (sub-type (type-of x) $thId) (sub-type (type-of y) $thId) (= x y) ($eqId x y))))"""
          )
          addAdtDecl(t, st"(define-fun $neId ((o1 $tId) (o2 $tId)) B (not ($eqId o1 o2)))")
          var leaves: ISZ[ST] = ISZ()
          for (child <- poset.childrenOf(t).elements) {
            typeHierarchy.typeMap.get(child.ids) match {
              case Some(info: TypeInfo.Adt) if !info.ast.isRoot => leaves = leaves :+ typeHierarchyId(child)
              case _ =>
            }
          }
          if (typeHierarchy.isSubstitutableWithoutSpecVars(t)) {
            addAdtDecl(t,
              st"""(assert (forall ((x $tId) (y $tId))
                  |  (=>
                  |    (sub-type (type-of x) $thId)
                  |    (sub-type (type-of y) $thId)
                  |    ($eqId x y)
                  |    (= x y))))"""
            )
          }
          if (leaves.nonEmpty) {
            addAdtDecl(t,
              st"""(assert (forall ((x $tId))
                  |  (let ((t (type-of x)))
                  |  (=> (sub-type t $thId)
                  |      (or
                  |        ${(for (leaf <- leaves) yield st"(sub-type t $leaf)", "\n")})))))"""
            )
          }
        } else {
          if (parents.nonEmpty) {
            addAdtDecl(t,
              st"""(assert (and
                  |  ${(for (p <- poset.parentsOf(t).elements) yield st"(sub-type $thId ${typeHierarchyId(p)})", "\n")}))"""
            )
          }
          val newId = typeOpId(t, "new")
          val params = HashSet.empty[String] ++ (for (p <- ti.ast.params) yield p.id.value)
          val fieldInfos: ISZ[Smt2.AdtFieldInfo] =
            (for (f <- ti.vars.values) yield fieldInfo(params.contains(f.ast.id.value), f)) ++ (for (f <- ti.specVars.values) yield specFieldInfo(f))
          for (q <- fieldInfos) {
            addTypeDecl(t, st"(declare-fun ${q.fieldLookupId} ($tId) ${q.fieldTypeId})")
            q.fieldType match {
              case ft: AST.Typed.Name =>
                if (ft.ids == AST.Typed.isName || ft.ids == AST.Typed.msName) {
                  addTypeDecl(t,
                    st"""(assert (forall ((o $tId))
                        |  (=> (= (type-of o) $thId)
                        |      (= (${sTypeOfName(ft)} (${q.fieldLookupId} o)) ${typeHierarchyId(ft)}))))""")
                } else if (typeHierarchy.isAdt(ft)) {
                  addTypeDecl(t,
                    st"""(assert (forall ((o $tId))
                        |  (=> (= (type-of o) $thId)
                        |      (${if (typeHierarchy.isAdtLeafType(ft)) "=" else "sub-type"} (type-of (${q.fieldLookupId} o)) ${typeHierarchyId(ft)}))))""")
                }
              case ft: AST.Typed.Tuple =>
                addTypeDecl(t,
                  st"""(assert (forall ((o $tId))
                      |  (=> (= (type-of o) $thId)
                      |      (= (${tupleTypeOfName(ft)} (${q.fieldLookupId} o)) ${typeHierarchyId(ft)}))))""")
              case _ =>
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
            addTypeDecl(t,
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
          addTypeDecl(t,
            st"""(declare-fun $newId (${(for (q <- fieldInfos if q.isParam) yield q.fieldTypeId, " ")}) $tId)
                |(assert (forall (${(for (q <- fieldInfos if q.isParam) yield st"(${q.fieldId} ${q.fieldTypeId})", " ")} (x!0 $tId))
                |  (=>
                |    ${(for (q <- fieldInfos if q.isParam && typeHierarchy.isAdtType(q.fieldType)) yield st"(sub-type (type-of ${q.fieldId}) ${typeHierarchyId(q.fieldType)})", "\n")}
                |    (= x!0 ${if (hasParam) st"($newId ${(for (q <- fieldInfos if q.isParam) yield q.fieldId, " ")})" else newId})
                |    (and
                |      (= (type-of x!0) $thId)
                |      ${(for (q <- fieldInfos if q.isParam) yield st"(= (${q.fieldLookupId} x!0) ${q.fieldId})", "\n")})
                |  )
                |))""")
          addTypeDecl(t,
            st"""(define-fun $eqId ((x!0 $tId) (x!1 $tId)) B
                |  (and
                |    (= (type-of x!0) (type-of x!1) $thId)
                |    ${(for (q <- fieldInfos if q.isParam) yield st"(${typeOpId(q.fieldType, "==")} (${q.fieldLookupId} x!0) (${q.fieldLookupId} x!1))", "\n")}))
                |(assert (forall ((x $tId) (y $tId)) (=> (= (type-of x) (type-of y) $thId) (= x y) ($eqId x y))))"""
          )
          addTypeDecl(t,
            st"""(assert (forall ((x $tId) (y $tId))
                |  (=>
                |    (= (type-of x) $thId)
                |    (= (type-of y) $thId)
                |    ${(st"($eqId x y)" +: (for (q <- fieldInfos if !q.isParam) yield st"(= (${q.fieldLookupId} x) (${q.fieldLookupId} y))"), "\n")}
                |    (= x y))))""")
          addTypeDecl(t, st"""(define-fun $neId ((x $tId) (y $tId)) B (not ($eqId x y)))""")
        }
        for (parent <- parents) {
          addTypeDecl(t,
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
          addTypeH(arg.subst(sm))
        }
        posetUp(poset.addNode(t))
        val thId = typeHierarchyId(t)
        addTypeHierarchyId(t, thId)
        val tid = typeId(t)
        val isString = t.ids == AST.Typed.stringName
        if (!isString) {
          addSort(t, st"(define-sort $tid () ADT)")
        }
        addSort(t, st"(declare-const $thId Type)")
        val eqId = typeOpId(t, "==")
        val neId = typeOpId(t, "!=")
        if (isString) {
          addAdtDecl(t, st"(define-fun $eqId ((x $tid) (y $tid)) B (= x y))")
        } else {
          addAdtDecl(t,
            st"""(declare-fun $eqId ($tid $tid) B)
                |(assert (forall ((x $tid) (y $tid)) (=> (sub-type (type-of x) $thId) (sub-type (type-of y) $thId) (= x y) ($eqId x y))))"""
          )
        }
        addAdtDecl(t, st"(define-fun $neId ((o1 $tid) (o2 $tid)) B (not ($eqId o1 o2)))")
        addSub(ti.posOpt, T, t, thId, ti.parents, sm)
        var ops = ISZ[(String, ST)]()
        for (info <- ti.specVars.values) {
          val opId = info.ast.id.value
          val op = typeOpId(t, opId)
          val opT = info.typedOpt.get.subst(sm)
          addTypeH(opT)
          val opTid = typeId(opT)
          addAdtDecl(t, st"(declare-fun $op ($tid) $opTid)")
          ops = ops :+ ((opId, opTid))
        }
        for (p <- ops) {
          val (opId, opTid) = p
          val opAssignId = s"${opId}_="
          val op = typeOpId(t, opId)
          val opAssign = typeOpId(t, opAssignId)
          addTypeDecl(t,
            st"""(define-fun $opAssign ((o $tid) ($opId $opTid) (o2 $tid)) B
                |  (and
                |    ($eqId o2 o)
                |    ${(for (p2 <- ops if p2._1 != opId) yield st"(= (${typeOpId(t, p2._1)} o2) (${typeOpId(t, p2._1)} o))", "\n")}
                |    (= $opId ($op o2) ($op o))))""")
        }

        if (ti.ast.isSealed) {
          var leaves: ISZ[ST] = ISZ()
          for (child <- poset.childrenOf(t).elements) {
            typeHierarchy.typeMap.get(child.ids) match {
              case Some(info: TypeInfo.Adt) if !info.ast.isRoot => leaves = leaves :+ typeHierarchyId(child)
              case _ =>
            }
          }
          if (leaves.nonEmpty) {
            addTypeDecl(t,
              st"""(assert (forall ((x $tid))
                  |  (let ((t (type-of x)))
                  |  (=> (sub-type t $thId)
                  |      (or
                  |        ${(for (leaf <- leaves) yield st"(sub-type t $leaf)", "\n")})))))"""
            )
          }
        }
        if (!isString) {
          for (parent <- poset.parentsOf(t).elements) {
            addTypeDecl(t,
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
        val tRandomSeedId = typeOpId(t, "randomSeed(Z)")
        val tRandomSeedBetweenId = typeOpId(t, st"randomSeedBetween(Z, $tId, $tId)".render)
        val t2ZId = typeOpId(t, "toZ")
        val tMaxOpt: Option[ST] =
          if (ti.ast.hasMax) Some(st"(define-const ${currentNameIdString(t.ids :+ "Max")} $tId ${toVal(config, t, ti.ast.max)})")
          else None()
        val tMinOpt: Option[ST] =
          if (ti.ast.hasMin) Some(st"(define-const ${currentNameIdString(t.ids :+ "Min")}  $tId ${toVal(config, t, ti.ast.min)})")
          else None()
        (ti.ast.isSigned, ti.ast.isBitVector) match {
          case (T, T) =>
            val bwM1 = ti.ast.bitWidth - 1
            val bwM2 = bwM1 - 1
            val n = ti.ast.max + 1
            addSort(t,
              st"""(define-sort $tId () (_ BitVec ${ti.ast.bitWidth}))
                  |(define-fun $t2ZId ((x $tId)) Z
                  |  (ite (= ((_ extract $bwM1 $bwM1) x) #b0)
                  |       (bv2nat ((_ extract $bwM2 0) x))
                  |       (- (bv2nat ((_ extract $bwM2 0) x)) $n)))
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
                  |(declare-fun $tRandomSeedId (Z) $tId)
                  |(declare-fun $tRandomSeedBetweenId (Z $tId $tId) $tId)
                  |$tMaxOpt
                  |$tMinOpt""")
          case (F, T) =>
            addSort(t,
              st"""(define-sort $tId () (_ BitVec ${ti.ast.bitWidth}))
                  |(define-fun $t2ZId ((x $tId)) Z (bv2nat x))
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
                  |(declare-fun $tRandomSeedId (Z) $tId)
                  |(declare-fun $tRandomSeedBetweenId (Z $tId $tId) $tId)
                  |$tMaxOpt
                  |$tMinOpt""")
          case (_, _) =>
            addSort(t,
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
                  |(declare-fun $tRandomSeedId (Z) $tId)
                  |(declare-fun $tRandomSeedBetweenId (Z $tId $tId) $tId)
                  |$tMaxOpt
                  |$tMinOpt""")
        }
      }

      def addEnum(t: AST.Typed.Name, ti: TypeInfo.Enum): Unit = {
        val tid = typeId(t)
        val owner = ops.ISZOps(ti.name).dropRight(1)
        val eqOp = typeOpId(t, "==")
        val neOp = typeOpId(t, "!=")
        val leOp = typeOpId(t, "<=")
        val randomSeedOp = typeOpId(t, "randomSeed(Z)")
        val randomSeedBetweenOp = typeOpId(t, st"randomSeedBetween(Z, $t, $t)".render)
        val ordinalOp = typeOpId(t, "ordinal")
        val nameOp = typeOpId(t, "name")
        addSort(t,
          st"""(declare-datatypes (($tid 0)) ((
              |  ${(for (element <- ti.elements.keys) yield st"(${typeHierarchyId(AST.Typed.Name(t.ids :+ element, ISZ()))})", " ")})))
              |(declare-fun $ordinalOp ($tid) Z)
              |(declare-fun $nameOp ($tid) String)
              |(define-fun $eqOp ((x $tid) (y $tid)) B (= x y))
              |(define-fun $neOp ((x $tid) (y $tid)) B (not (= x y)))
              |(define-fun $leOp ((x $tid) (y $tid)) B (<= ($ordinalOp x) ($ordinalOp y)))
              |(declare-fun $randomSeedOp (Z) $tid)
              |(declare-fun $randomSeedBetweenOp (Z $tid $tid) $tid)""")
        var ordinal = 0
        var elements = ISZ[ST]()
        for (elementId <- ti.elements.keys) {
          val element = enumId(owner, elementId)
          elements = elements :+ element
          addSort(t, st"(declare-const $element $tid)")
          addSort(t, st"(assert (= $element ${typeHierarchyId(AST.Typed.Name(t.ids :+ elementId, ISZ()))}))")
          addSort(t, st"(assert (= ($ordinalOp $element) $ordinal))")
          addSort(t, st"""(assert (= ($nameOp $element) "$elementId"))""")
          ordinal = ordinal + 1
        }
        if (ti.elements.size > 1) {
          addSort(t, st"(assert (distinct ${(elements, " ")}))")
        }
      }

      def addTypeVar(t: AST.Typed.TypeVar): Unit = {
        val tid = typeId(t)
        if (t.isIndex) {
          addSort(t, st"(define-sort $tid () Z)")
          val t2zId = typeOpId(t, "toZ")
          val oneId = typeOpId(t, "1")
          val minId = currentNameIdString(ISZ(t.id, "Min"))
          val leId = typeOpId(t, "<=")
          val eqId = typeOpId(t, "==")
          val neId = typeOpId(t, "!=")
          val addId = typeOpId(t, "+")
          val subId = typeOpId(t, "-")
          addSort(t,
            st"""(define-fun $eqId ((n1 $tid) (n2 $tid)) B (= n1 n2))
                |(define-fun $neId ((n1 $tid) (n2 $tid)) B (not (= n1 n2)))
                |(define-fun $leId ((n1 $tid) (n2 $tid)) B (<= n1 n2))
                |(define-fun $addId ((n1 $tid) (n2 $tid)) $tid (+ n1 n2))
                |(define-fun $subId ((n1 $tid) (n2 $tid)) $tid (- n1 n2))
                |(define-fun $t2zId ((n $tid)) Z n)
                |(define-const $oneId $tid 1)
                |(define-const $minId $tid 0)"""
          )
        } else {
          addSort(t, st"(declare-sort $tid 0)")
          val eqId = typeOpId(t, "==")
          val neId = typeOpId(t, "!=")
          addSort(t,
            st"""(declare-fun $eqId ($tid $tid) B)
                |${Smt2.eqProp(eqId, tid)}
                |(assert (forall ((x $tid) (y $tid)) (=> (= x y) ($eqId x y))))
                |(define-fun $neId ((x $tid) (y $tid)) B (not ($eqId x y)))"""
          )
        }
      }

      def addTuple(t: AST.Typed.Tuple): Unit = {
        for (arg <- t.args) {
          addTypeH(arg)
        }
        val tId = typeId(t)
        val eqId = typeOpId(t, "==")
        val neId = typeOpId(t, "!=")
        val typeOfName = tupleTypeOfName(t)
        val thId = typeHierarchyId(t)
        val newId = typeOpId(t, "new")
        addTypeHierarchyId(t, thId)
        addSort(t, st"(declare-const $thId Type)")
        addSort(t, st"(declare-datatypes (($tId 0)) ((($newId ${(for (i <- 1 to t.args.size) yield st"(${typeOpId(t, s"_$i")} ${adtId(t.args(i - 1))})", " ")}))))")
        addSort(t, st"(declare-fun $typeOfName ($tId) Type)")
        var eSTs = ISZ[ST]()
        for (i <- 1 to t.args.size) {
          val tArg = t.args(i - 1)
          val eSTOpt: Option[ST] = tArg match {
            case tArg: AST.Typed.Name =>
              if (tArg.ids == AST.Typed.isName || tArg.ids == AST.Typed.msName) {
                Some(st"(= (${sTypeOfName(tArg)} e$i) ${typeHierarchyId(tArg)})")
              } else if (typeHierarchy.isAdt(tArg)) {
                Some(st"(${if (typeHierarchy.isAdtLeafType(tArg)) "=" else "sub-type"} (type-of e$i) ${typeHierarchyId(tArg)})")
              } else {
                None()
              }
            case tArg: AST.Typed.Tuple => Some(st"(= (${tupleTypeOfName(tArg)} e$i) ${typeHierarchyId(tArg)})")
            case _ => None()
          }
          eSTOpt match {
            case Some(eST) =>
              eSTs = eSTs :+ eST
              addTypeDecl(t,
                st"""(assert (forall ((o $tId) (e$i ${typeId(tArg)}))
                    |  (=>
                    |    (= ($typeOfName o) $thId)
                    |    (= (${typeOpId(t, s"_$i")} o) e$i)
                    |    $eST)))""")
            case _ =>
          }
        }
        addTypeDecl(t,
          st"""(assert (forall ((o $tId) ${(for (i <- 1 to t.args.size) yield st"(e$i ${typeId(t.args(i - 1))})", " ")})
              |  (=>
              |    ${(eSTs, "\n")}
              |    (= o ($newId ${(for (i <- 1 to t.args.size) yield st"e$i", " ")}))
              |    (= ($typeOfName o) $thId)
              |  )
              |))"""
        )
        addTypeDecl(t,
          st"""(define-fun $eqId ((x $tId) (y $tId)) B
              |  (and
              |    (= ($typeOfName x) ($typeOfName y) $thId)
              |    ${(for (i <- 1 to t.args.size) yield st"(${typeOpId(t.args(i - 1), "==")} (${typeOpId(t, s"_$i")} x) (${typeOpId(t, s"_$i")} y))", "\n")}
              |  )
              |)
              |(assert (forall ((x $tId) (y $tId)) (=> (= ($typeOfName x) ($typeOfName y) $thId) (= x y) ($eqId x y))))
              |(define-fun $neId ((x $tId) (y $tId)) B (not ($eqId x y)))""")
        if (ops.ISZOps(t.args).forall((et: AST.Typed) => typeHierarchy.isSubstitutableWithoutSpecVars(et))) {
          addTypeDecl(t,
            st"""(assert (forall ((x $tId) (y $tId))
                |  (=>
                |    (= ($typeOfName x) $thId)
                |    (= ($typeOfName y) $thId)
                |    ($eqId x y)
                |    (= x y))))""")
        }
      }

      val t = Util.normType(tipe)
      if (types.contains(t)) {
        return
      }
      typesUp(types + t)
      t match {
        case AST.Typed.z => addSort(t, Smt2.zST(config.intBitWidth))
        case AST.Typed.c => addSort(t, Smt2.cST(config.charBitWidth))
        case AST.Typed.f32 => addSort(t, f32ST(config.useReal, config.fpRoundingMode))
        case AST.Typed.f64 => addSort(t, f64ST(config.useReal, config.fpRoundingMode))
        case AST.Typed.r => addSort(t, Smt2.rST)
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
            addTypeH(AST.Typed.Tuple(t.args))
          } else {
            addTypeH(t.args(0))
          }
          addTypeH(t.ret)
        case _ => halt(s"TODO: $tipe") // TODO
      }
    }
    addTypeH(typed)
  }

  @pure def seqLit2SmtDeclST(config: Config, seqLit: Smt2.SeqLit): ST = {
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
      if (size != 0) Some(st"($itEqId (${typeOpId(t, "lastIndex")} x) ${toVal(config, it, size - 1)})") else None()
    val distinctOpt: Option[ST] =
      if (size > 1) Some(st"(distinct ${(for (i <- 0 until size) yield st"i$i", " ")})")
      else None()
    val r =
      st"""(declare-fun $seqLitId (${(for (_ <- 0 until size) yield st"$itId $etId", " ")}) $tId)
          |(assert (forall (${(for (i <- 0 until size) yield st"(i$i $itId) (v$i $etId)", " ")} (x $tId))
          |  (=>
          |    $distinctOpt
          |    (= x ${if (size == 0) seqLitId else st"($seqLitId ${(for (i <- 0 until size) yield st"i$i v$i", " ")})"})
          |    (and
          |      (= (${sTypeOfName(t)} x) ${typeHierarchyId(t)})
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
          case _: State.Claim.Eq =>
          case _: State.Claim.Custom =>
          case _: State.Claim.Old =>
          case _: State.Claim.Input =>
        }
      }
    }
    collectLidsRec(claims)
    return r
  }

  def satQuery(config: Config, claims: ISZ[State.Claim], negClaimOpt: Option[State.Claim], reporter: Reporter): ST = {
    for (c <- claims; t <- c.types) {
      addType(config, t, reporter)
    }
    var decls: HashSMap[String, ST] = HashSMap.empty[String, ST] ++ (for (c <- claims; p <- c2DeclST(config, c, reporter)) yield p)
    val (lets, lsyms) = Util.collectLetClaims(config.simplifiedQuery, claims)
    val lids = collectLids(claims)
    val sv2ST = Util.value2ST(this, lets, lids)
    var claimSmts = ISZ[ST]()
    for (c <- claims) {
      c2ST(config, c, sv2ST, lets, lids, reporter) match {
        case Some(st) => claimSmts = claimSmts :+ st
        case _ =>
      }
    }
    negClaimOpt match {
      case Some(negClaim) =>
        claimSmts = claimSmts :+ st"(not ${c2ST(config, negClaim, sv2ST, lets, lids, reporter)})"
        decls = decls ++ c2DeclST(config, negClaim, reporter)
      case _ =>
    }
    val seqLitDecls: ISZ[ST] = for (seqLit <- seqLits.elements) yield seqLit2SmtDeclST(config, seqLit)
    if (lets.nonEmpty) {
      val uscdid = UsedSymsCurrentDeclIdCollector(HashSet.empty, ISZ())
      for (c <- claims) {
        uscdid.transformStateClaim(c)
      }
      val usedSyms = uscdid.syms
      val symNums = HashSet ++ (for (sym <- lsyms.elements) yield v2ST(config, sym, reporter).render) ++
        (for (ds <- lets.values if ds.size > 1 && usedSyms.contains(ds(0).sym)) yield v2ST(config, ds(0).sym, reporter).render)
      decls = HashSMap.empty[String, ST] ++
        (for (d <- decls.entries if !ops.StringOps(d._1).startsWith(Smt2.symPrefix) || symNums.contains(d._1)) yield d)
    }
    return query(config, seqLitDecls, decls.values, claimSmts)
  }

  @pure def commentLines(s: String): ISZ[ST] = {
    return for (line <- ops.StringOps(s).split(c => c == '\n')) yield st"; $line"
  }

  @pure def toSTs(claims: ISZ[State.Claim], defs: ClaimDefs): ISZ[ST] = {
    return for (cST <- State.Claim.claimsSTs(claims, defs)) yield st"${(commentLines(cST.render), "\n")}"
  }

  @pure def toClaimST(isSequent: B, claims: ISZ[State.Claim], pos: message.Position): ST = {
    val defs = ClaimDefs.empty
    val r: ST = if (isSequent) {
      val premises = ops.ISZOps(claims).dropRight(1)
      val conclusion = claims(claims.size - 1)
      st""";
          |; Sequent:
          |;
          |${(toSTs(premises, defs), ",\n")}
          |; ⊢
          |${(toSTs(ISZ(conclusion), defs), ",\n")}
          |;"""
    } else {
      st""";
          |; Claims:
          |;
          |${(toSTs(claims, ClaimDefs.empty), "\n")}
          |;"""
    }
    return r
  }

  @pure def toExpST(config: Config, isSequent: B, context: ISZ[String], claims: ISZ[State.Claim], pos: message.Position): ST = {
    val (exps, lastOpt, _) = Util.claimsToExpsLastOpt(plugins, pos, context, claims, typeHierarchy, config.atLinesFresh,
      config.atRewrite)
    lastOpt match {
      case Some(last) =>
        val r: ST = if (isSequent) {
          st""";
              |; Sequent:
              |;
              |${(commentLines(st"""${(exps, ",\n")}""".render), "\n")}
              |; ⊢
              |${(commentLines(last.string), "\n")}
              |;"""
        } else {
          st""";
              |; Claims:
              |;
              |${(commentLines(st"""${(exps :+ last, ",\n")}""".render), "\n")}
              |;"""
        }
        return r
      case _ => return toClaimST(isSequent, claims, pos)
    }
  }

  def valid(context: ISZ[String], config: Config, cache: Logika.Cache, reportQuery: B, title: String,
            pos: message.Position, premises: ISZ[State.Claim], conclusion: State.Claim, reporter: Reporter): Smt2Query.Result = {
    def header(smt2res: Smt2Query.Result): String = {
      return st"""; Validity Check for $title
                 |${smt2res.info}
                 |; Time: ${formatTime(smt2res.timeMillis)}""".render
    }
    if (config.smt2Caching) {
      val claims = premises :+ conclusion
      cache.getSmt2(F, typeHierarchy, config, config.timeoutInMs, claims) match {
        case Some(res) =>
          val forceReport = res.kind != Smt2Query.Result.Kind.Unsat
          if (reportQuery || forceReport) {
            reporter.query(pos, title, F, res.timeMillis, forceReport, config.elideEncoding, res)
          }
          return res(info = header(res))
        case _ =>
      }
    }
    val smt2res = checkUnsat(config, config.timeoutInMs, satQuery(config, premises, Some(conclusion), reporter).render)
    val queryOpt: Option[String] =
      if (config.elideEncoding && smt2res.kind == Smt2Query.Result.Kind.Unsat) None() else Some(smt2res.query)
    val claims = premises :+ conclusion
    val res = smt2res(info = header(smt2res), query =
      st"""${if (config.rawInscription) toClaimST(T, claims, pos) else toExpST(config, T, context, claims, pos)}
          |$queryOpt""".render
    )
    val forceReport = smt2res.kind != Smt2Query.Result.Kind.Unsat
    if (reportQuery || forceReport || config.logVc) {
      reporter.query(pos, title, F, res.timeMillis, forceReport, config.elideEncoding, res)
    }
    config.logVcDirOpt match {
      case Some(logDir) =>
        val filename: String =
          if (ops.StringOps(title).contains("[")) s"vc-$title"
          else s"vc-$title-at-${pos.beginLine}-${pos.beginColumn}"
        writeFile(logDir, filename, s"${res.info}\n${res.query}")
      case _ =>
    }
    if (config.smt2Caching && res.solverName != "none") {
      cache.setSmt2(F, typeHierarchy, config, config.timeoutInMs, claims, res)
    }
    return res
  }

  def query(config: Config, funDecls: ISZ[ST], decls: ISZ[ST], claims: ISZ[ST]): ST = {
    var ss: ISZ[ST] = for (ds <- sorts.values; d <- ds) yield d
    if (typeHierarchyIds.size > 1) {
      ss = ss :+
        st"""(assert (distinct
            |  ${(typeHierarchyIds.values, "\n")}))"""
    }

    val pureFunClaims: ISZ[ST] =
      if (config.strictPureMode == Config.StrictPureMode.Uninterpreted) ISZ()
      else for (p <- pureFuns.values) yield p._2

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
          |(define-fun |B.__>:| ((x B) (y B)) B (=> x y))
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
          |${(for (ds <- adtDecls.values; d <- ds) yield d, "\n")}
          |
          |${(for (ds <- sTypeDecls.values; d <- ds) yield d, "\n")}
          |
          |${(for (ds <- typeDecls.values; d <- ds) yield d, "\n")}
          |
          |${(for (ds <- constraints.values; d <- ds) yield d, "\n")}
          |
          |${(funDecls, "\n")}
          |
          |${(for (p <- pureFuns.values) yield p._1, "\n")}
          |
          |${(pureFunClaims, "\n")}
          |
          |${(decls, "\n")}
          |
          |${(for (a <- claims) yield st"(assert $a)", "\n")}
          |
          |(check-sat)
          |(exit)"""
    return r
  }

  def v2ST(config: Config, v: State.Value, reporter: Reporter): ST = {
    addType(config, v.tipe, reporter)
    v match {
      case v: State.Value.B => return if (v.value) Smt2.stTrue else Smt2.stFalse
      case v: State.Value.Z => return if (v.value < 0) st"(- ${v.value * -1})" else st"${v.value}"
      case v: State.Value.Sym => return st"${Smt2.symPrefix}${v.num}"
      case v: State.Value.Range => return if (v.value < 0) st"(- ${v.value * -1})" else st"${v.value}"
      case v: State.Value.Enum => return enumId(v.owner, v.id)
      case v: State.Value.S8 => return toVal(config, v.tipe, conversions.S8.toZ(v.value))
      case v: State.Value.S16 => return toVal(config, v.tipe, conversions.S16.toZ(v.value))
      case v: State.Value.S32 => return toVal(config, v.tipe, conversions.S32.toZ(v.value))
      case v: State.Value.S64 => return toVal(config, v.tipe, conversions.S64.toZ(v.value))
      case v: State.Value.U8 => return toVal(config, v.tipe, conversions.U8.toZ(v.value))
      case v: State.Value.U16 => return toVal(config, v.tipe, conversions.U16.toZ(v.value))
      case v: State.Value.U32 => return toVal(config, v.tipe, conversions.U32.toZ(v.value))
      case v: State.Value.U64 => return toVal(config, v.tipe, conversions.U64.toZ(v.value))
      case v: State.Value.F32 => return formatF32(config, v.value)
      case v: State.Value.F64 => return formatF64(config, v.value)
      case v: State.Value.C =>
        val t: AST.Typed.Name = config.charBitWidth match {
          case 8 => AST.Typed.u8
          case 16 => AST.Typed.u16
          case 32 => AST.Typed.u32
          case _ => halt("Infeasible")
        }
        return toVal(config, t, conversions.U32.toZ(conversions.C.toU32(v.value)))
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

  @pure def escapeId(id: String): String = {
    return st"${(for (c <- conversions.String.toCis(id)) yield escapeIdC(c), "")}".render
  }

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
    return if (ids(0) == Smt2.topPrefix) ids2ST(ids) else rec(ISZ(ids(ids.size - 1)))
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
    return st"${currentLocalIdString(x.context, x.id)}"
  }

  def enumId(owner: ISZ[String], id: String): ST = {
    return st"|e:${(shorten(owner), ".")}.${escapeId(id)}|"
  }

  def l2DeclST(config: Config, c: State.Claim.Let, declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
               reporter: Reporter): ST = {
    c match {
      case c: State.Claim.Let.CurrentId if c.declId => return st"(${l2RhsST(config, c, v2ST _, HashMap.empty, declIds, reporter)} ${v2ST(config, c.sym, reporter)})"
      case _ => return st"(${v2ST(config, c.sym, reporter)} ${l2RhsST(config, c, v2ST _, HashMap.empty, declIds, reporter)})"
    }
  }

  def embeddedClaims(config: Config,
                     isImply: B,
                     simplify: B,
                     claims: ISZ[State.Claim],
                     initSyms: ISZ[State.Value.Sym],
                     letsOpt: Option[HashMap[Z, ISZ[State.Claim.Let]]],
                     declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
                     reporter: Reporter): ST = {
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
        case _: State.Claim.Eq => return acc
        case _: State.Claim.Custom => return acc
        case _: State.Claim.Old => return acc
        case _: State.Claim.Input => return acc
      }
    }
    val lids = collectLids(claims) -- declIds.keys
    val simp = config.simplifiedQuery || simplify
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
          case claim: State.Claim.Eq => rest = rest :+ claim
          case claim: State.Claim.Custom => rest = rest :+ claim
          case _: State.Claim.Old =>
          case _: State.Claim.Input =>
        }
      }
      var body: ST =
        if (isImply) implyST(config, rest, v2ST _, HashMap.empty, declIds, reporter)
        else andST(config, rest, v2ST _, HashMap.empty, declIds, reporter).getOrElse(Smt2.stTrue)
      if (lets.nonEmpty) {
        val newDeclIds = lids ++ declIds.entries
        body =
          st"""(let (${l2DeclST(config, lets(lets.size - 1), newDeclIds, reporter)})
              |  $body)"""
        for (i <- (lets.size - 2) to 0 by -1) {
          val let = lets(i)
          body =
            st"""(let (${l2DeclST(config, let, newDeclIds, reporter)})
                |$body)"""
        }
      }
      val s = HashSSet.empty[State.Value.Sym] ++ syms -- lsyms
      if (s.nonEmpty || lids.nonEmpty) {
          val (decls, body2) = addTypeConstraintsH(isImply,
            (for (id <- lids.values) yield (localId(id), id.sym.tipe, T)) ++
              (for (sym <- s.elements) yield (v2ST(config, sym, reporter), sym.tipe, F)),
            body)
        body =
          st"""(${if (isImply) "forall" else "exists"} (${(decls, " ")})
              |  $body2)"""
      }
      return body
    }

    def simplified: ST = {
      var (lets, lsyms) = Util.collectLetClaims(simp, claims)
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
        c2ST(config, claims(i), sv2ST, lets, declIds, reporter) match {
          case Some(st) => simplifiedClaimSTs = simplifiedClaimSTs :+ st
          case _ =>
        }
      }
      var r: ST = if (isImply) {
        val lastClaim: State.Claim = claims(claims.size - 1) match {
          case claim: State.Claim.Let.Def => State.Claim.Eq(claim.sym, claim.value)
          case claim => claim
        }
        implySTH(simplifiedClaimSTs, c2ST(config, lastClaim, sv2ST, lets, declIds, reporter))
      } else {
        andSTH(simplifiedClaimSTs).getOrElse(Smt2.stTrue)
      }
      val uscdid = UsedSymsCurrentDeclIdCollector(HashSet.empty, ISZ())
      for (c <- claims) {
        uscdid.transformStateClaim(c)
      }
      val usedSyms = uscdid.syms
      val syms = lsyms.elements ++ (for (ds <- lets.values if ds.size > 1 && usedSyms.contains(ds(0).sym)) yield ds(0).sym)
      if (lids.nonEmpty || syms.nonEmpty || uscdid.currentDeclIds.nonEmpty) {
        val (decls, body) = addTypeConstraintsH(isImply,
          (for (id <- lids.values) yield (localId(id), id.sym.tipe, T)) ++
            (for (sym <- syms) yield (v2ST(config, sym, reporter), sym.tipe, F)) ++
            (for (cid <- uscdid.currentDeclIds) yield (currentLocalId(cid), cid.sym.tipe, T)), r)
        r =
          st"""(${if (isImply) "forall" else "exists"} (${(decls, " ")})
              |  $body)"""
      }
      return r
    }

    return if (simp) simplified else raw
  }

  @pure def addTypeConstraints(isImply: B, ps: ISZ[(ST, AST.Typed)], claim: ST): (ISZ[ST], ST) = {
    return addTypeConstraintsH(isImply, for (p <- ps) yield (p._1, p._2, T), claim)
  }

  @pure def addTypeConstraintsH(isImply: B, ps: ISZ[(ST, AST.Typed, B)], claim: ST): (ISZ[ST], ST) = {
    var varDecls = ISZ[ST]()
    var typeConstraints = ISZ[ST]()
    for (p <- ps) {
      val (x, tipe, addTypeConstraint) = p
      val t = typeId(tipe)
      varDecls = varDecls :+ st"($x $t)"
      if (addTypeConstraint) {
        tipe match {
          case tipe: AST.Typed.Name if tipe.ids == AST.Typed.isName || tipe.ids == AST.Typed.msName =>
            typeConstraints = typeConstraints :+ st"(= (${sTypeOfName(tipe)} $x) ${typeHierarchyId(tipe)})"
          case tipe if typeHierarchy.isAdtType(tipe) =>
            typeConstraints = typeConstraints :+ st"(${if (typeHierarchy.isAdtLeafType(tipe)) "=" else "sub-type"} (type-of $x) ${typeHierarchyId(tipe)})"
          case tipe: AST.Typed.Tuple =>
            typeConstraints = typeConstraints :+ st"(= (${tupleTypeOfName(tipe)} $x) ${typeHierarchyId(tipe)})"
          case _ =>
        }
      }
    }
    return if (typeConstraints.nonEmpty)
      (varDecls,
        st"""(${if (isImply) "=>" else "and"}
            |  ${(typeConstraints, "\n")}
            |  $claim)""")
    else (varDecls, claim)
  }

  def l2RhsST(config: Config,
              c: State.Claim.Let,
              v2st: (Config, State.Value, Reporter) => ST,
              lets: HashMap[Z, ISZ[State.Claim.Let]],
              declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
              reporter: Reporter): ST = {
    c match {
      case c: State.Claim.Let.SeqStore =>
        val seqT = c.seq.tipe.asInstanceOf[AST.Typed.Name]
        addType(config, AST.Typed.Tuple(ISZ(seqT.args(0), seqT.args(1))), reporter)
        return st"(${typeOpId(c.seq.tipe, "up")} ${v2st(config, c.seq, reporter)} ${v2st(config, c.index, reporter)} ${v2st(config, c.element, reporter)})"
      case c: State.Claim.Let.FieldStore =>
        return st"(${typeOpId(c.adt.tipe, s"${c.id}_=")} ${v2st(config, c.adt, reporter)} ${v2st(config, c.value, reporter)})"
      case c: State.Claim.Let.SeqLit =>
        addSeqLit(config, c.sym.tipe.asInstanceOf[AST.Typed.Name], c.args.size, reporter)
        val newId = typeOpId(c.sym.tipe, s"new.${c.args.size}")
        return if (c.args.isEmpty) newId else st"($newId ${(for (arg <- c.args) yield st"${v2st(config, arg.index, reporter)} ${v2st(config, arg.value, reporter)}", " ")})"
      case c: State.Claim.Let.AdtLit =>
        val newId = typeOpId(c.sym.tipe, "new")
        return if (c.args.isEmpty) newId else st"($newId ${(for (arg <- c.args) yield v2st(config, arg, reporter), " ")})"
      case c: State.Claim.Let.CurrentName =>
        return currentNameId(c)
      case c: State.Claim.Let.Name =>
        return nameId(c)
      case c: State.Claim.Let.CurrentId =>
        return currentLocalId(c)
      case c: State.Claim.Let.Id =>
        return localId(c)
      case c: State.Claim.Let.Def =>
        return v2st(config, c.value, reporter)
      case c: State.Claim.Let.TypeTest =>
        val typeOf: ST = c.tipe match {
          case t: AST.Typed.Name if t.ids == AST.Typed.isName || t.ids == AST.Typed.msName => sTypeOfName(c.tipe)
          case _ => st"type-of"
        }
        return st"(${if (c.isEq) "=" else "sub-type"} ($typeOf ${v2st(config, c.value, reporter)}) ${typeHierarchyId(c.tipe)})"
      case c: State.Claim.Let.Quant =>
        val (qvars, body) = addTypeConstraints(c.isAll, for (qvar <- c.vars) yield (qvar2ST(qvar), qvar.tipe),
          embeddedClaims(config, c.isAll, T, c.claims, ISZ(), Some(lets), declIds, reporter))
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
          case AST.Exp.BinaryOp.CondImply => AST.Exp.BinaryOp.Imply
          case AST.Exp.BinaryOp.CondAnd => AST.Exp.BinaryOp.And
          case AST.Exp.BinaryOp.CondOr => AST.Exp.BinaryOp.Or
          case AST.Exp.BinaryOp.Equiv => return st"(= ${v2st(config, c.left, reporter)} ${v2st(config, c.right, reporter)})"
          case AST.Exp.BinaryOp.EquivUni => return st"(= ${v2st(config, c.left, reporter)} ${v2st(config, c.right, reporter)})"
          case AST.Exp.BinaryOp.Inequiv => return st"(not (= ${v2st(config, c.left, reporter)} ${v2st(config, c.right, reporter)}))"
          case AST.Exp.BinaryOp.InequivUni => return st"(not (= ${v2st(config, c.left, reporter)} ${v2st(config, c.right, reporter)}))"
          case _ => c.op
        }
        return if (Smt2.isSimpsOp(c)) v2ST(config, c.sym, reporter) else st"(${typeOpId(c.tipe, op)} ${v2st(config, c.left, reporter)} ${v2st(config, c.right, reporter)})"
      case c: State.Claim.Let.Unary =>
        return st"(${typeOpId(c.sym.tipe, s"unary_${c.op}")} ${v2st(config, c.value, reporter)})"
      case c: State.Claim.Let.SeqLookup =>
        return st"(${typeOpId(c.seq.tipe, "at")} ${v2st(config, c.seq, reporter)} ${v2st(config, c.index, reporter)})"
      case c: State.Claim.Let.FieldLookup =>
        return st"(${typeOpId(c.adt.tipe, c.id)} ${v2st(config, c.adt, reporter)})"
      case c: State.Claim.Let.SeqInBound =>
        return st"(${typeOpId(c.seq.tipe, "isInBound")} ${v2st(config, c.seq, reporter)} ${v2st(config, c.index, reporter)})"
      case c: State.Claim.Let.TupleLit =>
        return st"(${typeOpId(c.sym.tipe, "new")} ${(for (arg <- c.args) yield v2st(config, arg, reporter), " ")})"
      case c: State.Claim.Let.And =>
        return if (c.args.size == 0) Smt2.stFalse
        else if (c.args.size == 1) v2st(config, c.args(0), reporter)
        else st"(and ${(for (arg <- c.args) yield v2st(config, arg, reporter), " ")})"
      case c: State.Claim.Let.Or =>
        return if (c.args.size == 0) Smt2.stTrue
        else if (c.args.size == 1) v2st(config, c.args(0), reporter)
        else st"(or ${(for (arg <- c.args) yield v2st(config, arg, reporter), " ")})"
      case c: State.Claim.Let.Imply =>
        return st"(=> ${(for (arg <- c.args) yield v2st(config, arg, reporter), " ")})"
      case c: State.Claim.Let.Ite =>
        return st"(ite ${v2st(config, c.cond, reporter)} ${v2st(config, c.left, reporter)} ${v2st(config, c.right, reporter)})"
      case c: State.Claim.Let.ProofFunApply =>
        return if (c.args.isEmpty) proofFunId(c.pf)
        else st"(${proofFunId(c.pf)} ${(for (arg <- c.args) yield v2st(config, arg, reporter), " ")})"
      case c: State.Claim.Let.Apply =>
        val args: ST =
          if (c.args.size == 1) v2st(config, c.args(0), reporter)
          else st"(${typeOpId(AST.Typed.Tuple(for (arg <- c.args) yield arg.tipe), c.id)} ${(for (arg <- c.args) yield v2st(config, arg, reporter), " ")})"
        return st"(select ${if (c.isLocal) currentLocalIdString(c.context, c.id) else currentNameIdString(c.context :+ c.id)} $args)"
      case c: State.Claim.Let.Random => halt(s"Infeasible: $c")
    }
  }

  def c2ST(config: Config, c: State.Claim, v2st: (Config, State.Value, Reporter) => ST,
           lets: HashMap[Z, ISZ[State.Claim.Let]], declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
           reporter: Reporter): Option[ST] = {
    if (plugins.nonEmpty) {
      for (p <- plugins if p.canHandleSmt2(T, c)) {
        return p.handleSmt2(this, c, v2st, lets, declIds, reporter)
      }
    }
    c match {
      case _: State.Claim.Let.Random =>
        return None()
      case c: State.Claim.Let =>
        c match {
          case c: State.Claim.Let.Binary if Smt2.isSimpsOp(c) =>
            return Some(st"(${typeOpId(c.tipe, c.op)} ${v2st(config, c.left, reporter)} ${v2st(config, c.right, reporter)} ${v2st(config, c.sym, reporter)})")
          case c: State.Claim.Let.CurrentId if c.declId =>
          case _ =>
            lets.get(c.sym.num) match {
              case Some(ls) if ls.size == 1 => return None()
              case _ =>
            }
        }
        return Some(st"(= ${v2st(config, c.sym, reporter)} ${l2RhsST(config, c, v2st, lets, declIds, reporter)})")
      case c: State.Claim.Prop =>
        return Some(if (c.isPos) v2st(config, c.value, reporter) else st"(not ${v2st(config, c.value, reporter)})")
      case c: State.Claim.Eq =>
        return Some(st"(= ${v2st(config, c.v1, reporter)} ${v2st(config, c.v2, reporter)})")
      case _: State.Claim.Label =>
        return None()
      case _: State.Claim.Old =>
        return None()
      case _: State.Claim.Input =>
        return None()
      case c: State.Claim.If =>
        return Some(
          st"""(ite ${v2st(config, c.cond, reporter)}
              |  ${andST(config, c.tClaims, v2st, lets, declIds, reporter).getOrElse(Smt2.stTrue)}
              |  ${andST(config, c.fClaims, v2st, lets, declIds, reporter).getOrElse(Smt2.stTrue)}
              |)"""
        )
      case c: State.Claim.And => return andST(config, c.claims, v2st, lets, declIds, reporter)
      case c: State.Claim.Or => return orST(config, c.claims, v2st, lets, declIds, reporter)
      case c: State.Claim.Imply => return Some(implyST(config, c.claims, v2st, lets, declIds, reporter))
      case _: State.Claim.Custom => return None()
    }
  }

  def andSTH(sts: ISZ[ST]): Option[ST] = {
    if (sts.size == 0) {
      return None()
    } else if (sts.size == 1) {
      return Some(sts(0))
    } else {
      val r =
        st"""(and
            |  ${(sts, "\n")})"""
      return Some(r)
    }
  }

  def andST(config: Config, cs: ISZ[State.Claim], v2st: (Config, State.Value, Reporter) => ST,
            lets: HashMap[Z, ISZ[State.Claim.Let]], declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
            reporter: Reporter): Option[ST] = {
    var sts = ISZ[ST]()
    for (c <- cs) {
      c2ST(config, c, v2st, lets, declIds, reporter) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    return andSTH(sts)
  }

  def orSTH(sts: ISZ[ST]): Option[ST] = {
    if (sts.size == 0) {
      return None()
    } else if (sts.size == 1) {
      return Some(sts(0))
    } else {
      val r =
        st"""(or
            |  ${(sts, "\n")})"""
      return Some(r)
    }
  }

  def orST(config: Config, cs: ISZ[State.Claim], v2st: (Config, State.Value, Reporter) => ST,
           lets: HashMap[Z, ISZ[State.Claim.Let]], declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
           reporter: Reporter): Option[ST] = {
    var sts = ISZ[ST]()
    for (c <- cs) {
      c2ST(config, c, v2st, lets, declIds, reporter) match {
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

  def implyST(config: Config, cs: ISZ[State.Claim], v2st: (Config, State.Value, Reporter) => ST,
              lets: HashMap[Z, ISZ[State.Claim.Let]], declIds: HashSMap[(ISZ[String], String, Z), State.Claim.Let.Id],
              reporter: Reporter): ST = {
    var sts = ISZ[ST]()
    for (i <- 0 until cs.size - 1) {
      c2ST(config, cs(i), v2st, lets, declIds, reporter) match {
        case Some(st) => sts = sts :+ st
        case _ =>
      }
    }
    val lastOpt = c2ST(config, cs(cs.size - 1), v2st, lets, declIds, reporter)
    return if (lastOpt.isEmpty) Smt2.stTrue else implySTH(sts, lastOpt)
  }

  def c2DeclST(config: Config, c: State.Claim, reporter: Reporter): ISZ[(String, ST)] = {
    @pure def declareConst(n: ST, tipe: AST.Typed): ST = {
      val r: ST = tipe match {
        case tipe: AST.Typed.Name if tipe.ids == AST.Typed.isName || tipe.ids == AST.Typed.msName =>
          st"""(declare-const $n ${typeId(tipe)})
              |(assert (= (${sTypeOfName(tipe)} $n) ${typeHierarchyId(tipe)}))"""
        case tipe: AST.Typed.Tuple =>
          st"""(declare-const $n ${typeId(tipe)})
              |(assert (= (${tupleTypeOfName(tipe)} $n) ${typeHierarchyId(tipe)}))"""
        case _ =>
          if (typeHierarchy.isAdtType(tipe)) {
            st"""(declare-const $n ${typeId(tipe)})
                |(assert (${if (typeHierarchy.isAdtLeafType(tipe)) "=" else "sub-type"} (type-of $n) ${typeHierarchyId(tipe)}))"""
          } else {
            st"(declare-const $n ${typeId(tipe)})"
          }
      }

      return r
    }
    def def2DeclST(cDef: State.Claim.Let): ISZ[(String, ST)] = {
      val symST = v2ST(config, cDef.sym, reporter)
      return ISZ[(String, ST)](symST.render ~> st"(declare-const $symST ${typeId(cDef.sym.tipe)})")
    }
    if (plugins.nonEmpty) {
      for (p <- plugins if p.canHandleDeclSmt2(c)) {
        return p.handleDeclSmt2(this, c)
      }
    }
    c match {
      case _: State.Claim.Label => return ISZ()
      case _: State.Claim.Eq => return ISZ()
      case _: State.Claim.Old => return ISZ()
      case _: State.Claim.Input => return ISZ()
      case c: State.Claim.Prop =>
        val vST = v2ST(config, c.value, reporter)
        return ISZ[(String, ST)](vST.render ~> st"(declare-const $vST B)")
      case c: State.Claim.If =>
        val condST = v2ST(config, c.cond, reporter)
        var r = ISZ[(String, ST)](condST.render ~> st"(declare-const $condST B)")
        for (tClaim <- c.tClaims) {
          r = r ++ c2DeclST(config, tClaim, reporter)
        }
        for (fClaim <- c.fClaims) {
          r = r ++ c2DeclST(config, fClaim, reporter)
        }
        return r
      case c: State.Claim.And => return for (claim <- c.claims; p <- c2DeclST(config, claim, reporter)) yield p
      case c: State.Claim.Or => return for (claim <- c.claims; p <- c2DeclST(config, claim, reporter)) yield p
      case c: State.Claim.Imply => return for (claim <- c.claims; p <- c2DeclST(config, claim, reporter)) yield p
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
      case _: State.Claim.Custom => return ISZ()
    }
  }

  @memoize def typeIdRaw(t: AST.Typed): ST = {
    Util.normType(t) match {
      case t: AST.Typed.Name =>
        val ids: ISZ[String] = if (t.ids.size == 1) Smt2.topPrefix +: t.ids else t.ids
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
        if (t.args.size == 1) {
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
        val ids: ISZ[String] = if (t.ids.size == 1) Smt2.topPrefix +: t.ids else t.ids
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
