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
import org.sireum.lang.ast.{CoreExp, MCoreExpTransformer}
import org.sireum.lang.symbol.{Info, TypeInfo}
import org.sireum.lang.{ast => AST}
import org.sireum.lang.tipe.TypeHierarchy

object RewritingSystem {
  type FunStack = Stack[(String, AST.Typed)]
  type Local = (ISZ[String], String)
  type LocalMap = HashSMap[Local, AST.CoreExp.Base]
  type LocalPatternSet = HashSSet[Local]
  type PendingApplications = ISZ[(ISZ[String], String, ISZ[AST.CoreExp.Base], AST.CoreExp.Base)]
  type UnificationMap = HashSMap[Local, AST.CoreExp.Base]
  type UnificationErrorMessages = ISZ[String]
  type UnificationResult = Either[UnificationMap, UnificationErrorMessages]
  type MethodDesc = (ISZ[String], B)
  type MethodPatternMap = HashSMap[MethodDesc, Rewriter.Pattern.Method]
  type UnfoldingNumMap = HashSMap[MethodDesc, Z]

  @datatype class EvalConfig(val constant: B,
                             val unary: B,
                             val funApplication: B,
                             val quantApplication: B,
                             val equality: B,
                             val tupleProjection: B,
                             val seqIndexing: B,
                             val fieldAccess: B,
                             val instanceOf: B,
                             val equivSubst: B,
                             val iteBranches: B)

  object EvalConfig {
    val all: EvalConfig = EvalConfig(T, T, T, T, T, T, T, T, T, T, T)
    val none: EvalConfig = EvalConfig(F, F, F, F, F, F, F, F, F, F, F)
  }

  @record class Substitutor(var map: HashMap[AST.CoreExp, AST.CoreExp.ParamVarRef]) extends AST.MCoreExpTransformer {
    override def transformCoreExpBase(o: AST.CoreExp.Base): MOption[AST.CoreExp.Base] = {
      map.get(o) match {
        case Some(pvr) => return MSome(pvr)
        case _ =>
          o match {
            case o: AST.CoreExp.Fun =>
              val r0: MOption[AST.CoreExp.Param] = transformCoreExpParam(o.param)
              val oldMap = map
              map = HashMap ++ (for (p <- map.entries) yield (p._1.incDeBruijn(1), p._2.incDeBruijn(1)))
              val r1: MOption[AST.CoreExp.Base] = transformCoreExpBase(o.exp)
              map = oldMap
              if (r0.nonEmpty || r1.nonEmpty) {
               return MSome(o(param = r0.getOrElse(o.param), exp = r1.getOrElse(o.exp)))
              } else {
                return MNone()
              }
            case o: AST.CoreExp.Quant =>
              val r0: MOption[AST.CoreExp.Param] = transformCoreExpParam(o.param)
              val oldMap = map
              map = HashMap ++ (for (p <- map.entries) yield (p._1.incDeBruijn(1), p._2.incDeBruijn(1)))
              val r1: MOption[AST.CoreExp.Base] = transformCoreExpBase(o.exp)
              map = oldMap
              if (r0.nonEmpty || r1.nonEmpty) {
                return MSome(o(param = r0.getOrElse(o.param), exp = r1.getOrElse(o.exp)))
              } else {
                return MNone()
              }
            case _ =>
          }
          return super.transformCoreExpBase(o)
      }
    }
  }

  @record class ParamSubstitutor(var map: HashMap[Z, AST.CoreExp.Base]) extends AST.MCoreExpTransformer {
    override def transformCoreExpBase(o: AST.CoreExp.Base): MOption[AST.CoreExp.Base] = {
      o match {
        case o: AST.CoreExp.ParamVarRef =>
          map.get(o.deBruijn) match {
            case Some(e) => return MSome(e)
            case _ => return MNone()
          }
        case o: AST.CoreExp.Fun =>
          val r0: MOption[AST.CoreExp.Param] = transformCoreExpParam(o.param)
          val oldMap = map
          map = HashMap ++ (for (p <- map.entries) yield (p._1 + 1, p._2.incDeBruijn(1)))
          val r1: MOption[AST.CoreExp.Base] = transformCoreExpBase(o.exp)
          map = oldMap
          if (r0.nonEmpty || r1.nonEmpty) {
            return MSome(o(param = r0.getOrElse(o.param), exp = r1.getOrElse(o.exp)))
          } else {
            return MNone()
          }
        case o: AST.CoreExp.Quant =>
          val r0: MOption[AST.CoreExp.Param] = transformCoreExpParam(o.param)
          val oldMap = map
          map = HashMap ++ (for (p <- map.entries) yield (p._1 + 1, p._2.incDeBruijn(1)))
          val r1: MOption[AST.CoreExp.Base] = transformCoreExpBase(o.exp)
          map = oldMap
          if (r0.nonEmpty || r1.nonEmpty) {
            return MSome(o(param = r0.getOrElse(o.param), exp = r1.getOrElse(o.exp)))
          } else {
            return MNone()
          }
        case _ =>
      }
      return super.transformCoreExpBase(o)
    }
  }

  @record class LocalPatternDetector(val localPatterns: LocalPatternSet, var hasLocalPattern: B) extends AST.MCoreExpTransformer {
    override def postCoreExpLocalVarRef(o: AST.CoreExp.LocalVarRef): MOption[AST.CoreExp.Base] = {
      if (localPatterns.contains((o.context, o.id))) {
        hasLocalPattern = T
      }
      return AST.MCoreExpTransformer.PostResultCoreExpLocalVarRef
    }
  }

  @record class LocalSubstitutor(val map: UnificationMap) extends AST.MCoreExpTransformer {
    override def postCoreExpLocalVarRef(o: AST.CoreExp.LocalVarRef): MOption[AST.CoreExp.Base] = {
      map.get((o.context, o.id)) match {
        case Some(e) => return MSome(e)
        case _ => return MNone()
      }
    }
  }

  @record class LabeledDetector(var found: B) extends AST.MCoreExpTransformer {
    override def preCoreExpLabeled(o: AST.CoreExp.Labeled): AST.MCoreExpTransformer.PreResult[AST.CoreExp.Base] = {
      found = T
      return AST.MCoreExpTransformer.PreResultCoreExpLabeled(continu = F)
    }

    override def transformCoreExpBase(o: AST.CoreExp.Base): MOption[AST.CoreExp.Base] = {
      if (found) {
        return MNone()
      }
      return super.transformCoreExpBase(o)
    }
  }

  @record class LabeledRemover extends AST.MCoreExpTransformer {
    override def postCoreExpLabeled(o: AST.CoreExp.Labeled): MOption[AST.CoreExp.Base] = {
      return MSome(o.exp)
    }
  }

  @datatype trait Trace {
    @pure def toST: ST
  }

  object Trace {
    @datatype class Begin(val title: String, val exp: AST.CoreExp.Base) extends Trace {
      @strictpure def toST: ST =
        st"""Begin $title ${exp.prettyST} ..."""
    }

    @datatype class Info(val isEval: B, val title: ST) extends Trace {
      @strictpure def toST: ST =
        st"""info [${if (isEval) "eval" else "rw"}] $title"""
    }

    @datatype class Eval(val desc: ST,
                         val from: AST.CoreExp.Base,
                         val to: AST.CoreExp.Base) extends Trace {
      @pure override def toST: ST = {
        val r = st"""by [eval] $desc:
                    |   ${from.prettyST}
                    |   ≡  ${to.prettyST}"""
        return r
      }
    }

    @datatype class Rewrite(val name: ISZ[String],
                            val rightToLeft: B,
                            val pattern: AST.CoreExp,
                            val original: AST.CoreExp.Base,
                            val rewritten: AST.CoreExp.Base,
                            val evaluatedOpt: Option[AST.CoreExp.Base],
                            val assumptions: ISZ[(AST.CoreExp.Base, (AST.ProofAst.StepId, AST.CoreExp.Base))]) extends Trace {
      @strictpure def toST: ST = {
        val assumptionsOpt: Option[ST] = if (assumptions.isEmpty) None() else Some(
          st"""using assumptions:
              |${(for (a <- assumptions) yield st"${a._2._1}) ${a._2._2.prettyST}", "\n")}"""
        )
        val evOpt: Option[ST] = evaluatedOpt match {
          case Some(evaluated) => Some(st"≡  ${evaluated.prettyST}")
          case _ => None()
        }
        st"""by [rw] ${if (rightToLeft) "~" else ""}${(name, ".")}: ${pattern.prettyPatternST}
            |   $assumptionsOpt
            |   on ${original.prettyST}
            |   ${if (rightToLeft) "<" else ">"}  ${rewritten.prettyST}
            |   $evOpt"""
      }
    }

    @datatype class Done(val exp: AST.CoreExp.Base, val done: AST.CoreExp.Base) extends Trace {
      @strictpure def toST: ST =
        st"""∴  ${exp.prettyST}
            |   ≡  ${done.prettyST}"""
    }
  }

  @record class Rewriter(val maxCores: Z,
                         val th: TypeHierarchy,
                         val provenClaims: HashSMap[AST.ProofAst.StepId, AST.CoreExp.Base],
                         val patterns: ISZ[Rewriter.Pattern.Claim],
                         val methodPatterns: MethodPatternMap,
                         val fromStepOpt: Option[AST.ProofAst.StepId],
                         val shouldTrace: B,
                         val shouldTraceEval: B,
                         val maxUnfolding: Z,
                         var labeledOnly: B,
                         var inLabel: B,
                         var done: B,
                         var trace: ISZ[Trace]) {
    @strictpure def unfoldingMap: MBox[UnfoldingNumMap] = MBox(HashSMap.empty)
    @memoize def provenClaimStepIdMapEval: HashSMap[AST.CoreExp.Base, AST.ProofAst.StepId] = {
      fromStepOpt match {
        case Some(fromStepId) => return HashSMap ++ (for (p <- provenClaimStepIdMap.entries if p._2 != fromStepId) yield p)
        case _ => return provenClaimStepIdMap
      }
    }
    @memoize def provenClaimStepIdMap: HashSMap[AST.CoreExp.Base, AST.ProofAst.StepId] = {
      @strictpure def conjuncts(e: AST.CoreExp.Base): ISZ[AST.CoreExp.Base] = {
        e match {
          case AST.CoreExp.Binary(left, AST.Exp.BinaryOp.And, right, _) => ISZ(e) ++ conjuncts(left) ++ conjuncts(right)
          case _ => ISZ(e)
        }
      }
      var r = HashSMap.empty[AST.CoreExp.Base, AST.ProofAst.StepId]
      for (p <- provenClaims.entries) {
        val (stepId, claim) = p
        def addBinary(e: AST.CoreExp.Binary): Unit = {
          e.op match {
            case AST.Exp.BinaryOp.Lt =>
              r = r + e ~> stepId
              r = r + e(op = AST.Exp.BinaryOp.Le) ~> stepId
              r = r + e(left = e.right, op = AST.Exp.BinaryOp.Gt, right = e.left) ~> stepId
              if (e.right < e.left) {
                r = r + e(left = e.right, op = AST.Exp.BinaryOp.InequivUni, right = e.left) ~> stepId
              } else {
                r = r + e(op = AST.Exp.BinaryOp.InequivUni) ~> stepId
              }
            case AST.Exp.BinaryOp.Le =>
              r = r + e ~> stepId
              r = r + e(left = e.right, op = AST.Exp.BinaryOp.Ge, right = e.left) ~> stepId
            case AST.Exp.BinaryOp.Gt =>
              r = r + e ~> stepId
              r = r + e(op = AST.Exp.BinaryOp.Ge) ~> stepId
              r = r + e(left = e.right, op = AST.Exp.BinaryOp.Lt, right = e.left) ~> stepId
              if (e.right < e.left) {
                r = r + e(left = e.right, op = AST.Exp.BinaryOp.InequivUni, right = e.left) ~> stepId
              } else {
                r = r + e(op = AST.Exp.BinaryOp.InequivUni) ~> stepId
              }
            case AST.Exp.BinaryOp.Ge =>
              r = r + e ~> stepId
              r = r + e(left = e.right, op = AST.Exp.BinaryOp.Le, right = e.left) ~> stepId
            case AST.Exp.BinaryOp.And =>
              r = r + e ~> stepId
              for (c <- conjuncts(e)) {
                r = r + c ~> stepId
              }
            case _ =>
              if (e.op == AST.Exp.BinaryOp.EquivUni) {
                e.left.tipe match {
                  case t: AST.Typed.Name =>
                    if (t.ids == AST.Typed.zName || th.typeMap.get(t.ids).get.isInstanceOf[TypeInfo.SubZ]) {
                      r = r + e(op = AST.Exp.BinaryOp.Le) ~> stepId
                      r = r + e(op = AST.Exp.BinaryOp.Ge) ~> stepId
                      r = r + e(left = e.right, op = AST.Exp.BinaryOp.Le, right = e.left) ~> stepId
                      r = r + e(left = e.right, op = AST.Exp.BinaryOp.Ge, right = e.left) ~> stepId
                    }
                  case _ =>
                }
              }
              if (e.op == AST.Exp.BinaryOp.EquivUni || e.op == AST.Exp.BinaryOp.InequivUni) {
                if (e.right < e.left) {
                  r = r + e(left = e.right, right = e.left) ~> stepId
                } else {
                  r = r + e ~> stepId
                }
              } else {
                r = r + e ~> stepId
              }
          }
        }
        claim match {
          case claim: AST.CoreExp.Unary if claim.op == AST.Exp.UnaryOp.Not =>
            r = r + claim ~> stepId
            claim.exp match {
              case e: AST.CoreExp.Binary =>
                val newOp = negBinaryOp(e.op)
                if (newOp != e.op) {
                  addBinary(e(op = newOp))
                }
              case _ =>
            }
          case claim: AST.CoreExp.Binary => addBinary(claim)
          case _ => r = r + claim ~> stepId
        }
      }
      return r
    }

    def transformCoreExpBases(cache: Logika.Cache, s: ISZ[AST.CoreExp.Base]): Option[ISZ[AST.CoreExp.Base]] = {
      var changed = F
      var r = ISZ[AST.CoreExp.Base]()
      for (o <- s) {
        transformCoreExpBase(cache, o) match {
          case Some(o2) =>
            changed = T
            r = r :+ o2
          case _ => r = r :+ o
        }
      }
      return if (changed) Some(r) else None()
    }
    def transformCoreExpBase(cache: Logika.Cache, o: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
      val r: Option[AST.CoreExp.Base] = {
        val hasChanged = F
        val rOpt: Option[AST.CoreExp.Base] = o match {
          case _: AST.CoreExp.Lit => None()
          case _: AST.CoreExp.ParamVarRef => None()
          case _: AST.CoreExp.LocalVarRef => None()
          case _: AST.CoreExp.VarRef => None()
          case o: AST.CoreExp.Binary =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.left)
            val r1: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.right)
            if (hasChanged || r0.nonEmpty || r1.nonEmpty)
              Some(o(left = r0.getOrElse(o.left), right = r1.getOrElse(o.right)))
            else
              None()
          case o: AST.CoreExp.Unary =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            if (hasChanged || r0.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp)))
            else
              None()
          case o: AST.CoreExp.Constructor =>
            val r1: Option[IS[Z, AST.CoreExp.Base]] = transformCoreExpBases(cache, o.args)
            if (hasChanged || r1.nonEmpty)
              Some(o(args = r1.getOrElse(o.args)))
            else
              None()
          case o: AST.CoreExp.Select =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            if (hasChanged || r0.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp)))
            else
              None()
          case o: AST.CoreExp.Update =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            val r1: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.arg)
            if (hasChanged || r0.nonEmpty || r1.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp), arg = r1.getOrElse(o.arg)))
            else
              None()
          case o: AST.CoreExp.Indexing =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            val r1: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.index)
            if (hasChanged || r0.nonEmpty || r1.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp), index = r1.getOrElse(o.index)))
            else
              None()
          case o: AST.CoreExp.IndexingUpdate =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            val r1: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.index)
            val r2: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.arg)
            if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp), index = r1.getOrElse(o.index), arg = r2.getOrElse(o.arg)))
            else
              None()
          case o: AST.CoreExp.If =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.cond)
            r0 match {
              case Some(cond: AST.CoreExp.LitB) =>
                if (cond.value)
                  transformCoreExpBase(cache, o.tExp)
                else
                  transformCoreExpBase(cache, o.fExp)
              case _ =>
                if (hasChanged || r0.nonEmpty)
                  Some(o(cond = r0.getOrElse(o.cond)))
                else
                  None()
            }
          case o: AST.CoreExp.Apply =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            val r1: Option[IS[Z, AST.CoreExp.Base]] = transformCoreExpBases(cache, o.args)
            if (hasChanged || r0.nonEmpty || r1.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp), args = r1.getOrElse(o.args)))
            else
              None()
          case o: AST.CoreExp.Fun =>
            val r1: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            if (hasChanged || r1.nonEmpty)
              Some(o(exp = r1.getOrElse(o.exp)))
            else
              None()
          case o: AST.CoreExp.Quant =>
            val r1: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            if (hasChanged || r1.nonEmpty)
              Some(o(exp = r1.getOrElse(o.exp)))
            else
              None()
          case o: AST.CoreExp.InstanceOfExp =>
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            if (hasChanged || r0.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp)))
            else
              None()
          case _: AST.CoreExp.Halt => None()
          case o: AST.CoreExp.Labeled =>
            val oldInLabel = inLabel
            inLabel = T
            val r0: Option[AST.CoreExp.Base] = transformCoreExpBase(cache, o.exp)
            inLabel = oldInLabel
            r0 match {
              case Some(r) =>
                o.numOpt match {
                  case Some(num) =>
                    val n = num - 1
                    if (n <= 0) {
                      return Some(r)
                    } else {
                      return Some(o(numOpt = Some(n), exp = r))
                    }
                  case _ => return Some(o(exp = r))
                }
              case _ =>
                if (r0.isEmpty && labeledOnly) {
                  evalBase(th, EvalConfig.all, cache, methodPatterns, unfoldingMap, 0,
                    provenClaimStepIdMapEval, o, F, shouldTraceEval) match {
                    case Some((r1, t)) =>
                      trace = trace ++ t
                      done = T
                      return Some(r1)
                    case _ =>
                  }
                }
            }
            if (hasChanged || r0.nonEmpty)
              Some(o(exp = r0.getOrElse(o.exp)))
            else
              None()
        }
        rOpt
      }
      val hasChanged: B = r.nonEmpty
      val o2: AST.CoreExp.Base = r.getOrElse(o)
      val shouldUnfold: B = o2 match {
        case o2: AST.CoreExp.VarRef if methodPatterns.contains((o2.owner :+ o2.id, o2.isInObject)) => T
        case o2: AST.CoreExp.Select =>
          val infoOpt: Option[Info.Method] = o2.exp.tipe match {
            case t: AST.Typed.Name =>
              th.typeMap.get(t.ids).get match {
                case ti: TypeInfo.Adt => ti.methods.get(o2.id)
                case ti: TypeInfo.Sig => ti.methods.get(o2.id)
                case _ => None()
              }
            case _ => None()
          }
          infoOpt match {
            case Some(info) if methodPatterns.contains((info.name, info.isInObject)) => T
            case _ => F
          }
        case _ => F
      }
      if (shouldUnfold && (!labeledOnly || inLabel)) {
        evalBase(th, EvalConfig.none, cache, methodPatterns, unfoldingMap, 1, HashSMap.empty, o2, F, shouldTraceEval) match {
          case Some((o3, t)) =>
            trace = trace ++ t
            return Some(o3)
          case _ =>
        }
      }
      val postR = rewrite(cache, o2)
      if (postR.nonEmpty) {
        return postR
      } else if (hasChanged) {
        return Some(o2)
      } else {
        return None()
      }
    }

    def rewrite(cache: Logika.Cache, o: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
      if (!inLabel && labeledOnly) {
        return None()
      }
      var rOpt = Option.none[AST.CoreExp.Base]()
      var i = 0
      while (!done && rOpt.isEmpty && i < patterns.size) {
        val pattern = patterns(i)
        var assumptions = ISZ[AST.CoreExp.Base]()
        @tailrec def arrowRec(e: AST.CoreExp): AST.CoreExp = {
          e match {
            case e: AST.CoreExp.Arrow =>
              assumptions = assumptions :+ e.left
              return arrowRec(e.right)
            case _ => return e
          }
        }
        def tryPattern(): Unit = {
          if (done) {
            return
          }
          val (from, to): (AST.CoreExp.Base, AST.CoreExp.Base) = arrowRec(pattern.exp) match {
            case AST.CoreExp.Binary(left, AST.Exp.BinaryOp.EquivUni, right, _) => (left, right)
            case e => halt(st"Infeasible: ${e.prettyST}".render)
          }
          def last(m: UnificationMap, patterns2: ISZ[Rewriter.Pattern.Claim], apcs: ISZ[(AST.ProofAst.StepId, AST.CoreExp.Base)]): Unit = {
            val o2: AST.CoreExp.Base = if (m.isEmpty) {
              to
            } else {
              LocalSubstitutor(m).transformCoreExpBase(to) match {
                case MSome(to2) => to2
                case _ =>
                  if (patterns2.isEmpty) {
                    o
                  } else {
                    Rewriter(maxCores, th, HashSMap.empty, patterns2, methodPatterns, fromStepOpt, F, F, maxUnfolding,
                      F, F, F, ISZ()).transformCoreExpBase(cache, o).getOrElse(o)
                  }
              }
            }
            val (o3Opt, t): (Option[AST.CoreExp.Base], ISZ[Trace]) =
              evalBase(th, EvalConfig.all, cache, methodPatterns, unfoldingMap, 0,
                provenClaimStepIdMapEval, o2, F, shouldTraceEval) match {
                case Some((o3o, t)) => (Some(o3o), t)
                case _ => (None(),  ISZ())
              }
            val o3 = o3Opt.getOrElse(o2)
            if (o == o3) {
              // skip
            } else if (pattern.isPermutative && o < o3) {
              // skip
            } else {
              if (shouldTrace) {
                trace = trace :+ Trace.Rewrite(pattern.name, pattern.rightToLeft, pattern.exp, o, o2,
                  if (!shouldTraceEval) o3Opt else None(), ops.ISZOps(assumptions).zip(apcs))
              }
              trace = trace ++ t
              rOpt = Some(o3)
              done = T
            }
          }
          if (assumptions.isEmpty) {
            unify(T, th, pattern.localPatternSet, ISZ(from), ISZ(o)) match {
              case Either.Left(m) => last(m, ISZ(), ISZ())
              case _ =>
            }
          } else {
            val pces = provenClaims.entries
            val par = maxCores > 1 && assumptions.size > 2 && pces.size > 2
            def recAssumption(pendingApplications: PendingApplications,
                              substMap: HashMap[String, AST.Typed],
                              apcs: ISZ[(AST.ProofAst.StepId, AST.CoreExp.Base)],
                              map: UnificationMap,
                              j: Z): Unit = {
              if (done) {
                return
              }
              if (j >= assumptions.size) {
                val ems: MBox[UnificationErrorMessages] = MBox(ISZ())
                val pas = MBox(pendingApplications)
                val sm = MBox(substMap)
                def r2l(p: Rewriter.Pattern.Claim): Rewriter.Pattern.Claim = {
                  return if (pattern.rightToLeft) p.toRightToLeft else p
                }
                val patterns2: ISZ[Rewriter.Pattern.Claim] =
                  (for (k <- 0 until apcs.size; apc <- toCondEquiv(th, apcs(k)._2)) yield
                    r2l(Rewriter.Pattern.Claim(pattern.isInObject, pattern.name :+ s"Assumption$k", F, isPermutative(apc), HashSSet.empty, apc))) ++
                    patterns
                val o2 = Rewriter(maxCores, th, HashSMap.empty, patterns2, methodPatterns, fromStepOpt, F, F,
                  maxUnfolding, F, F, F, ISZ()).transformCoreExpBase(cache, o).getOrElse(o)
                val m = unifyExp(T, th, pattern.localPatternSet, from, o2, map, pas, sm, ems)
                if (ems.value.isEmpty) {
                  unifyPendingApplications(T, th, pattern.localPatternSet, m, pas, sm, ems) match {
                    case Either.Left(m2) =>
                      last(m2, patterns2, apcs)
                    case _ =>
                  }
                }
                return
              }
              val assumption = assumptions(j)
              def tryAssumption(pc: (AST.ProofAst.StepId, AST.CoreExp.Base)): Unit = {
                if (done) {
                  return
                }
                val ems: MBox[UnificationErrorMessages] = MBox(ISZ())
                val pas = MBox(pendingApplications)
                val sm = MBox(substMap)
                val m = unifyExp(T, th, pattern.localPatternSet, assumption, pc._2, map, pas, sm, ems)
                if (ems.value.isEmpty) {
                  recAssumption(pas.value, sm.value, apcs :+ pc, m, j + 1)
                }
              }
              if (par) {
                ops.ISZOps(pces).mParMap(tryAssumption _)
              } else {
                var k = 0
                while (!done && k < pces.size) {
                  tryAssumption(pces(k))
                  k = k + 1
                }
              }
            }
            recAssumption(ISZ(), HashMap.empty, ISZ(), HashSMap.empty, 0)
          }
        }
        tryPattern()
        i = i + 1
      }
      return rOpt
    }
  }

  object Rewriter {
    @datatype trait Pattern {
      @pure def toRightToLeft: Rewriter.Pattern = {
        return this
      }
      @pure def isInObject: B
      @pure def name: ISZ[String]
    }

    object Pattern {

      @datatype class Claim(val isInObject: B,
                            val name: ISZ[String],
                            val rightToLeft: B,
                            val isPermutative: B,
                            val localPatternSet: LocalPatternSet,
                            val exp: AST.CoreExp) extends Pattern {
        @pure override def toRightToLeft: Rewriter.Pattern.Claim = {
          @pure def rec(e: AST.CoreExp): AST.CoreExp = {
            e match {
              case e: AST.CoreExp.Arrow =>
                return e(left = rec(e.left).asInstanceOf[AST.CoreExp.Base], right = rec(e.right))
              case e: AST.CoreExp.Binary if e.isEquiv && !e.right.isInstanceOf[AST.CoreExp.LitB] =>
                return e(left = e.right, right = e.left)
              case _ => return e
            }
          }
          val thiz = this
          return thiz(rightToLeft = !rightToLeft, exp = rec(exp))
        }
      }

      @datatype class Method(val isAbs: B,
                             val isInObject: B,
                             val owner: ISZ[String],
                             val id: String,
                             val params: ISZ[(String, AST.Typed)],
                             val exp: AST.CoreExp.Base) extends Pattern {
        @strictpure def name: ISZ[String] = owner :+ id
        @memoize def toFun: AST.CoreExp.Fun = {
          val context = owner :+ id
          var map = HashMap.empty[AST.CoreExp, AST.CoreExp.ParamVarRef]
          for (i <- params.size - 1 to 0 by -1) {
            val (id, t) = params(i)
            map = map + AST.CoreExp.LocalVarRef(F, context, id, t) ~> AST.CoreExp.ParamVarRef(params.size - i, id, t)
          }
          var r = Substitutor(map).transformCoreExpBase(exp).getOrElse(exp)
          if (params.isEmpty) {
            r = AST.CoreExp.Fun(AST.CoreExp.Param("_", AST.Typed.unit), r)
          } else {
            for (i <- params.size - 1 to 0 by -1) {
              val (id, t) = params(i)
              r = AST.CoreExp.Fun(AST.CoreExp.Param(id, t), r)
            }
          }
          return r.asInstanceOf[AST.CoreExp.Fun]
        }
      }
    }
  }

  @datatype class Translator(val th: TypeHierarchy, val isPattern: B) {
    @pure def translateBody(body: AST.Body, funStack: FunStack, localMap: LocalMap): AST.CoreExp.Base = {
      val stmts = body.stmts
      var m = localMap
      for (i <- 0 until stmts.size - 1) {
        m = translateStmt(stmts(i), funStack, m)._2
      }
      return translateAssignExp(stmts(stmts.size - 1).asAssignExp, funStack, m)
    }
    @pure def translatePattern(exp: AST.CoreExp.Base, pattern: AST.Pattern, funStack: FunStack, localMap: LocalMap): (ISZ[AST.CoreExp.Base], LocalMap) = {
      var r = ISZ[AST.CoreExp.Base]()
      var lMap = localMap
      pattern match {
        case _: AST.Pattern.Wildcard => // skip
        case pattern: AST.Pattern.Literal =>
          r = r :+ AST.CoreExp.Binary(exp, AST.Exp.BinaryOp.EquivUni,
            translateExp(pattern.lit, funStack, localMap), AST.Typed.b)
        case pattern: AST.Pattern.VarBinding =>
          lMap = lMap + (pattern.idContext, pattern.id.value) ~> exp
        case pattern: AST.Pattern.Structure =>
          val t = pattern.typedOpt.get
          lMap = pattern.idOpt match {
            case Some(id) => localMap + (pattern.idContext, id.value) ~> exp
            case _ => localMap
          }
          t match {
            case t: AST.Typed.Tuple =>
              var i = 0
              var conds = ISZ[AST.CoreExp.Base]()
              for (j <- 0 until t.args.size) {
                val pat = pattern.patterns(i)
                val f = AST.CoreExp.Select(exp, s"_${j + 1}", pat.typedOpt.get)
                val (pconds, lMap2) = translatePattern(f, pat, funStack, lMap)
                conds = conds ++ pconds
                lMap = lMap2
                i = i + 1
              }
              r = r :+ AST.CoreExp.condAnd(AST.CoreExp.InstanceOfExp(T, exp, t), AST.CoreExp.bigAnd(conds))
            case t: AST.Typed.Name =>
              var conds = ISZ[AST.CoreExp.Base]()
              if (t.ids == AST.Typed.isName || t.ids == AST.Typed.msName) {
                val hasWildcard = pattern.patterns.size > 0 && pattern.patterns(pattern.patterns.size - 1).
                  isInstanceOf[AST.Pattern.SeqWildcard]
                val (size, op): (Z, String) = if (hasWildcard) (pattern.patterns.size - 1, AST.Exp.BinaryOp.Ge)
                else (pattern.patterns.size, AST.Exp.BinaryOp.EquivUni)
                var mk: Z => AST.CoreExp.Lit @pure = (i: Z) => AST.CoreExp.LitZ(i)
                var n: Z = th.typeMap.get(t.args(0).asInstanceOf[AST.Typed.Name].ids).get match {
                  case ti: TypeInfo.SubZ =>
                    if (ti.ast.isBitVector) {
                      mk = (i: Z) => AST.CoreExp.LitBits(i.string, ti.typedOpt.get)
                    } else {
                      mk = (i: Z) => AST.CoreExp.LitRange(i, ti.typedOpt.get)
                    }
                    if (ti.ast.isZeroIndex) 0 else ti.ast.index
                  case _ => 0
                }
                conds = conds :+ AST.CoreExp.Binary(AST.CoreExp.Select(exp, "size", AST.Typed.z), op,
                  AST.CoreExp.LitZ(size), AST.Typed.b)
                for (i <- 0 until pattern.patterns.size - (if (hasWildcard) 1 else 0)) {
                  val pat = pattern.patterns(i)
                  val f = AST.CoreExp.Indexing(exp, mk(n), pat.typedOpt.get)
                  val (pconds, lMap2) = translatePattern(f, pat, funStack, lMap)
                  conds = conds ++ pconds
                  lMap = lMap2
                  n = n + 1
                }
              } else {
                val adt = th.typeMap.get(t.ids).get.asInstanceOf[TypeInfo.Adt]
                var i = 0
                for (p <- adt.ast.params if !p.isHidden) {
                  val pat = pattern.patterns(i)
                  val f = AST.CoreExp.Select(exp, p.id.value, pat.typedOpt.get)
                  val (pconds, lMap2) = translatePattern(f, pat, funStack, lMap)
                  conds = conds ++ pconds
                  lMap = lMap2
                  i = i + 1
                }
              }
              r = r :+ AST.CoreExp.condAnd(AST.CoreExp.InstanceOfExp(T, exp, t), AST.CoreExp.bigAnd(conds))
            case _ => halt("Infeasible")
          }
        case pattern: AST.Pattern.Ref =>
          val right: AST.CoreExp.Base = pattern.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Var =>
              if (res.isInObject) {
                val ids = pattern.name.ids
                val owner: ISZ[String] = for (i <- 0 until pattern.name.ids.size - 1) yield ids(i).value
                AST.CoreExp.VarRef(T, owner, ids(ids.size - 1).value, pattern.typedOpt.get)
              } else {
                AST.CoreExp.Select(
                  AST.CoreExp.LocalVarRef(F, pattern.idContext, "this", pattern.receiverTipeOpt.get),
                  res.id, pattern.typedOpt.get)
              }
            case res: AST.ResolvedInfo.LocalVar =>
              translateLocalInfo(res, pattern.typedOpt.get, funStack, localMap)
            case res: AST.ResolvedInfo.EnumElement =>
              AST.CoreExp.LitEnum(res.owner, res.name, res.ordinal)
            case _ => halt("Infeasible")
          }
          r = r :+ AST.CoreExp.Binary(exp, AST.Exp.BinaryOp.EquivUni, right, AST.Typed.b)
        case pattern: AST.Pattern.LitInterpolate => halt("TODO")
        case _: AST.Pattern.SeqWildcard => halt("Infeasible")
      }
      return (r, lMap)
    }
    @pure def translateLocalInfo(res: AST.ResolvedInfo.LocalVar, t: AST.Typed, funStack: FunStack, localMap: LocalMap): AST.CoreExp.Base = {
      localMap.get((res.context, res.id)) match {
        case Some(r) => return r
        case _ =>
      }
      val id = res.id
      val stackSize = funStack.size
      for (i <- stackSize - 1 to 0 by -1) {
        val p = funStack.elements(i)
        if (p._1 == id) {
          return AST.CoreExp.ParamVarRef(stackSize - i, id, p._2)
        }
      }
      return AST.CoreExp.LocalVarRef(isPattern, res.context, id, t)
    }
    @pure def translateStmt(stmt: AST.Stmt, funStack: FunStack, localMap: LocalMap): (Option[AST.CoreExp.Base], LocalMap) = {
      stmt match {
        case stmt: AST.Stmt.Expr =>
          return (Some(translateExp(stmt.exp, funStack, localMap)), localMap)
        case stmt: AST.Stmt.Var =>
          val res = stmt.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
          return (None(), localMap + (res.context, res.id) ~>
            translateAssignExp(stmt.initOpt.get, funStack, localMap))
        case stmt: AST.Stmt.Block =>
          return (Some(translateBody(stmt.body, funStack, localMap)), localMap)
        case stmt: AST.Stmt.If =>
          val condExp = translateExp(stmt.cond, funStack, localMap)
          val tExp = translateBody(stmt.thenBody, funStack, localMap)
          val fExp = translateBody(stmt.elseBody, funStack, localMap)
          return (Some(AST.CoreExp.If(condExp, tExp, fExp, stmt.attr.typedOpt.get)), localMap)
        case stmt: AST.Stmt.VarPattern =>
          val exp = translateAssignExp(stmt.init, funStack, localMap)
          val (conds, lMap) = translatePattern(exp, stmt.pattern, funStack, localMap)
          val cond = AST.CoreExp.bigAnd(conds)
          var lMap2 = lMap
          for (p <- lMap.entries if localMap.get(p._1) != Some(p._2)) {
            lMap2 = lMap2 + p._1 ~> AST.CoreExp.ite(cond, p._2, AST.CoreExp.Abort, p._2.tipe)
          }
          return (None(), lMap2)
        case stmt: AST.Stmt.Match =>
          val exp = translateExp(stmt.exp, funStack, localMap)
          var condBodyPairs = ISZ[(AST.CoreExp.Base, AST.CoreExp.Base)]()
          for (cas <- stmt.cases) {
            val (conds, lMap) = translatePattern(exp, cas.pattern, funStack, localMap)
            val conds2: ISZ[AST.CoreExp.Base] = cas.condOpt match {
              case Some(cond) => conds :+ translateExp(cond, funStack, lMap)
              case _ => conds
            }
            val body = translateBody(cas.body, funStack, lMap)
            condBodyPairs = condBodyPairs :+ (AST.CoreExp.bigAnd(conds2), body)
          }
          val t = stmt.typedOpt.get
          val (lastCond, lastBody) = condBodyPairs(condBodyPairs.size - 1)
          var r = AST.CoreExp.ite(
            AST.CoreExp.bigAnd((for (j <- 0 until condBodyPairs.size - 1) yield
              AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, condBodyPairs(j)._1).asInstanceOf[AST.CoreExp.Base]) :+ lastCond),
            lastBody, AST.CoreExp.Abort, t)
          for (i <- condBodyPairs.size - 2 to 0 by -1) {
            val (cond, body) = condBodyPairs(i)
            r = AST.CoreExp.ite(
              AST.CoreExp.bigAnd((for (j <- 0 until i) yield
                AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, condBodyPairs(j)._1).asInstanceOf[AST.CoreExp.Base]) :+ cond),
              body, r, t)
          }
          return (Some(r), localMap)
        case _ => halt(s"Infeasible: $stmt")
      }
    }
    @pure def translateAssignExp(ae: AST.AssignExp, funStack: FunStack, localMap: LocalMap): AST.CoreExp.Base = {
      val (Some(r), _) = translateStmt(ae.asStmt, funStack, localMap)
      return r
    }
    @pure def translateExp(e: AST.Exp, funStack: FunStack, localMap: LocalMap): AST.CoreExp.Base = {
      e match {
        case e: AST.Exp.LitB => return AST.CoreExp.LitB(e.value)
        case e: AST.Exp.LitZ => return AST.CoreExp.LitZ(e.value)
        case e: AST.Exp.LitC => return AST.CoreExp.LitC(e.value)
        case e: AST.Exp.LitString => return AST.CoreExp.LitString(e.value)
        case e: AST.Exp.LitR => return AST.CoreExp.LitR(e.value)
        case e: AST.Exp.LitF32 => return AST.CoreExp.LitF32(e.value)
        case e: AST.Exp.LitF64 => return AST.CoreExp.LitF64(e.value)
        case e: AST.Exp.StringInterpolate =>
          e.typedOpt match {
            case Some(t: AST.Typed.Name) =>
              th.typeMap.get(t.ids).get match {
                case ti: lang.symbol.TypeInfo.SubZ =>
                  if (ti.ast.isBitVector) {
                    return AST.CoreExp.LitBits(e.lits(0).value, t)
                  } else {
                    return AST.CoreExp.LitRange(Z(e.lits(0).value).get, t)
                  }
                case _ => halt(s"TODO: $e")
              }
            case _ => halt(s"Infeasible: expected typed expression")
          }
        case e: AST.Exp.Tuple =>
          return if (e.args.size == 1) translateExp(e.args(0), funStack, localMap)
          else AST.CoreExp.Constructor(e.typedOpt.get, for (arg <- e.args) yield translateExp(arg, funStack, localMap))
        case e: AST.Exp.This =>
          return AST.CoreExp.LocalVarRef(F, e.owner, "this", e.typedOpt.get)
        case e: AST.Exp.Ident =>
          e.resOpt.get match {
            case res: AST.ResolvedInfo.LocalVar =>
              return translateLocalInfo(res, e.typedOpt.get, funStack, localMap)
            case res: AST.ResolvedInfo.Var if res.isInObject =>
              if (res.owner == AST.Typed.sireumName) {
                res.id match {
                  case "T" => return AST.CoreExp.True
                  case "F" => return AST.CoreExp.False
                  case _ =>
                }
              }
              return AST.CoreExp.VarRef(T, res.owner, res.id, e.typedOpt.get)
            case res: AST.ResolvedInfo.Method =>
              return AST.CoreExp.VarRef(res.isInObject, res.owner, res.id, e.typedOpt.get)
            case _ =>
              halt(s"Infeasible: $e")
          }
        case e: AST.Exp.Unary =>
          val op: AST.Exp.UnaryOp.Type = if (e.typedOpt.get == AST.Typed.b && e.op == AST.Exp.UnaryOp.Complement)
            AST.Exp.UnaryOp.Not else e.op
          return AST.CoreExp.Unary(op, translateExp(e.exp, funStack, localMap))
        case e: AST.Exp.Binary =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.BuiltIn =>
              val left = translateExp(e.left, funStack, localMap)
              val right = translateExp(e.right, funStack, localMap)
              val op: String = res.kind match {
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
                  return AST.CoreExp.condAnd(left, right)
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
                  return AST.CoreExp.condOr(left, right)
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
                  return AST.CoreExp.condImply(left, right)
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv => AST.Exp.BinaryOp.EquivUni
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryEq if th.isSubstitutableWithoutSpecVars(left.tipe) => AST.Exp.BinaryOp.EquivUni
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryInequiv => AST.Exp.BinaryOp.InequivUni
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryNe if th.isSubstitutableWithoutSpecVars(left.tipe) => AST.Exp.BinaryOp.InequivUni
                case _ => e.op
              }
              return AST.CoreExp.Binary(left, op, right, e.typedOpt.get)
            case res: AST.ResolvedInfo.Method =>
              return AST.CoreExp.Apply(AST.CoreExp.Select(translateExp(e.left, funStack, localMap), e.op,
                AST.Typed.Method(res.isInObject, res.mode, res.typeParams, res.owner, res.id, res.paramNames,
                  res.tpeOpt.get)), ISZ(translateExp(e.right, funStack, localMap)), e.typedOpt.get)
            case _ => halt(s"Infeasible: $e")
          }
        case e: AST.Exp.Select =>
          e.resOpt.get match {
            case res: AST.ResolvedInfo.EnumElement => return AST.CoreExp.LitEnum(res.owner, res.name, res.ordinal)
            case res: AST.ResolvedInfo.Method if res.isInObject => return AST.CoreExp.VarRef(T, res.owner, res.id, e.typedOpt.get)
            case _ =>
          }
          e.receiverOpt match {
            case Some(receiver) => return AST.CoreExp.Select(translateExp(receiver, funStack, localMap), e.id.value, e.typedOpt.get)
            case _ => return translateExp(AST.Exp.Ident(e.id, e.attr), funStack, localMap)
          }
        case e: AST.Exp.If =>
          return AST.CoreExp.ite(translateExp(e.cond, funStack, localMap), translateExp(e.thenExp, funStack, localMap),
            translateExp(e.elseExp, funStack, localMap), e.typedOpt.get)
        case e: AST.Exp.Fun =>
          val params: ISZ[(String, AST.Typed)] = for (p <- e.params) yield
            (p.idOpt.get.value, p.typedOpt.get)
          var stack = funStack
          for (p <- params) {
            stack = stack.push(p)
          }
          val last = params(params.size - 1)
          var r = AST.CoreExp.Fun(AST.CoreExp.Param(last._1, last._2), translateAssignExp(e.exp, stack, localMap))
          for (i <- params.size - 2 to 0 by -1) {
            val p = params(i)
            r = AST.CoreExp.Fun(AST.CoreExp.Param(p._1, p._2), r)
          }
          return r
        case e: AST.Exp.Quant =>
          val kind: AST.CoreExp.Quant.Kind.Type =
            if (e.isForall) AST.CoreExp.Quant.Kind.ForAll
            else AST.CoreExp.Quant.Kind.Exists
          val params: ISZ[(String, AST.Typed)] = for (i <- 0 until e.fun.params.size) yield
            (e.fun.params(i).idOpt.get.value, e.fun.params(i).typedOpt.get)
          var stack = funStack
          for (p <- params) {
            stack = stack.push(p)
          }
          val last = params(params.size - 1)
          var r = AST.CoreExp.Quant(kind, AST.CoreExp.Param(last._1, last._2),
            translateAssignExp(e.fun.exp, stack, localMap))
          for (i <- params.size - 2 to 0 by -1) {
            val p = params(i)
            r = AST.CoreExp.Quant(kind, AST.CoreExp.Param(p._1, p._2), r)
          }
          return r
        case e: AST.Exp.StrictPureBlock =>
          return translateStmt(e.block, funStack, localMap)._1.get
        case e: AST.Exp.Invoke =>
          def args: ISZ[AST.CoreExp.Base] = {
            return for (arg <- e.args) yield translateExp(arg, funStack, localMap)
          }
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Spec =>
                case AST.MethodMode.Method =>
                case AST.MethodMode.Constructor =>
                  return AST.CoreExp.Constructor(e.typedOpt.get, args)
                case AST.MethodMode.Select =>
                  e.receiverOpt match {
                    case Some(receiver) => return AST.CoreExp.Indexing(translateExp(receiver, funStack, localMap),
                      translateExp(e.args(0), funStack, localMap), e.typedOpt.get)
                    case _ => return AST.CoreExp.Indexing(translateExp(e.ident, funStack, localMap),
                      translateExp(e.args(0), funStack, localMap), e.typedOpt.get)
                  }
                case AST.MethodMode.Store =>
                  val ie = translateExp(e.args(0), funStack, localMap)
                  val tuple = ie.tipe.asInstanceOf[AST.Typed.Tuple]
                  val (index, value): (AST.CoreExp.Base, AST.CoreExp.Base) = ie match {
                    case AST.CoreExp.Constructor(_, ISZ(i, v)) => (i, v)
                    case AST.CoreExp.Binary(i, AST.Exp.BinaryOp.MapsTo, v, _) => (i, v)
                    case _ => (AST.CoreExp.Select(ie, "_1", tuple.args(0)), AST.CoreExp.Select(ie, "_2", tuple.args(1)))
                  }
                  e.receiverOpt match {
                    case Some(receiver) => return AST.CoreExp.IndexingUpdate(translateExp(receiver, funStack, localMap),
                      index, value, e.typedOpt.get)
                    case _ => return AST.CoreExp.IndexingUpdate(translateExp(e.ident, funStack, localMap),
                      index, value, e.typedOpt.get)
                  }
                case AST.MethodMode.Extractor => halt("TODO")
                case AST.MethodMode.Ext => halt("TODO")
                case AST.MethodMode.ObjectConstructor => halt("TODO")
                case AST.MethodMode.Just => halt("Infeasible")
                case AST.MethodMode.Copy => halt("Infeasible")
              }
            case AST.ResolvedInfo.BuiltIn(AST.ResolvedInfo.BuiltIn.Kind.Halt) =>
              return AST.CoreExp.Abort
            case _ =>
          }
          val inObject: B = e.ident.resOpt.get match {
            case res: AST.ResolvedInfo.Method if res.isInObject => T
            case res: AST.ResolvedInfo.Var if res.isInObject => T
            case res: AST.ResolvedInfo.Enum => T
            case _ => F
          }
          e.receiverOpt match {
            case Some(receiver) if !inObject =>
              return AST.CoreExp.Apply(translateExp(e.ident, funStack, localMap),
                translateExp(receiver, funStack, localMap) +: args, e.typedOpt.get)
            case _ =>
              return AST.CoreExp.Apply(translateExp(e.ident, funStack, localMap),
                args, e.typedOpt.get)
          }
        case e: AST.Exp.InvokeNamed =>
          def getArgs: ISZ[AST.CoreExp.Base] = {
            val args = MS.create[Z, AST.CoreExp.Base](e.args.size, AST.CoreExp.False)
            for (arg <- e.args) {
              args(arg.index) = translateExp(arg.arg, funStack, localMap)
            }
            return args.toISZ
          }
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.Method =>
              res.mode match {
                case AST.MethodMode.Constructor =>
                  return AST.CoreExp.Constructor(e.typedOpt.get, getArgs)
                case AST.MethodMode.Spec =>
                case AST.MethodMode.Method =>
                case AST.MethodMode.Copy =>
                  var r: AST.CoreExp.Base = e.receiverOpt match {
                    case Some(receiver) => translateExp(receiver, funStack, localMap)
                    case _ => translateExp(e.ident, funStack, localMap)
                  }
                  val t = e.typedOpt.get
                  for (arg <- e.args) {
                    r = AST.CoreExp.Update(r, arg.id.value, translateExp(arg.arg, funStack, localMap), t)
                  }
                  return r
                case AST.MethodMode.Ext => halt("TODO")
                case AST.MethodMode.Extractor => halt("TODO")
                case AST.MethodMode.ObjectConstructor => halt("TODO")
                case AST.MethodMode.Just => halt("Infeasible")
                case AST.MethodMode.Select => halt("Infeasible")
                case AST.MethodMode.Store => halt("Infeasible")
              }
            case _ =>
          }
          e.receiverOpt match {
            case Some(receiver) =>
              return AST.CoreExp.Apply(translateExp(e.ident, funStack, localMap),
                translateExp(receiver, funStack, localMap) +: getArgs, e.typedOpt.get)
            case _ => return AST.CoreExp.Apply(translateExp(e.ident, funStack, localMap),
              getArgs, e.typedOpt.get)
          }
        case e: AST.Exp.Labeled =>
          val numOpt: Option[Z] = e.numOpt match {
            case Some(num) => Some(num.value)
            case _ => None()
          }
          return AST.CoreExp.Labeled(numOpt, translateExp(e.exp, funStack, localMap))
        case e => halt(s"TODO: $e")
      }
    }
  }

  @record class NoCache extends Logika.Cache {

    override def clearTransition(): Unit = {}
    override def getTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, transition: Logika.Cache.Transition, context: ISZ[String], state: State, smt2: Smt2): Option[(ISZ[State], U64)] = {
      return None()
    }
    override def setTransition(th: TypeHierarchy, config: Config, transition: Logika.Cache.Transition, context: ISZ[String], state: State, nextStates: ISZ[State], smt2: Smt2): U64 = {
      return U64.fromZ(0)
    }

    override def getAssignExpTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, exp: AST.AssignExp, context: ISZ[String], state: State, smt2: Smt2): Option[(ISZ[(State, State.Value)], U64)] = {
      return None()
    }

    override def setAssignExpTransition(th: TypeHierarchy, config: Config, exp: AST.AssignExp, context: ISZ[String], state: State, nextStatesValues: ISZ[(State, State.Value)], smt2: Smt2): U64 = {
      return U64.fromZ(0)
    }

    override def getSmt2(isSat: B, th: TypeHierarchy, config: Config, timeoutInMs: Z, claims: ISZ[State.Claim]): Option[Smt2Query.Result] = {
      return None()
    }

    override def setSmt2(isSat: B, th: TypeHierarchy, config: Config, timeoutInMs: Z, claims: ISZ[State.Claim], result: Smt2Query.Result): Unit = {}

    override def getPatterns(th: TypeHierarchy, isInObject: B, name: ISZ[String]): Option[ISZ[Rewriter.Pattern]] = {
      return None()
    }

    override def setPatterns(th: TypeHierarchy, isInObject: B, name: ISZ[String], patterns: ISZ[Rewriter.Pattern]): Unit = {}

    override def keys: ISZ[Logika.Cache.Key] = {
      return ISZ()
    }

    override def getValue(key: Logika.Cache.Key): Option[Logika.Cache.Value] = {
      return None()
    }

    override def setValue(key: Logika.Cache.Key, value: Logika.Cache.Value): Unit = {}

    override def clearValue(key: Logika.Cache.Key): Unit = {}

    override def taskKeys: ISZ[Logika.Cache.Key] = {
      return ISZ()
    }

    override def getTaskValue(key: Logika.Cache.Key): Option[Logika.Cache.Value] = {
      return None()
    }

    override def setTaskValue(key: Logika.Cache.Key, value: Logika.Cache.Value): Unit = {}

    override def clearTaskValue(key: Logika.Cache.Key): Unit = {}
  }

  val noCache: Logika.Cache = NoCache()

  @pure def translateExp(th: TypeHierarchy, isPattern: B, exp: AST.Exp): AST.CoreExp.Base = {
    return Translator(th, isPattern).translateExp(exp, Stack.empty, HashSMap.empty)
  }

  @pure def translateAssignExp(th: TypeHierarchy, isPattern: B, ae: AST.AssignExp): AST.CoreExp.Base = {
    return Translator(th, isPattern).translateAssignExp(ae, Stack.empty, HashSMap.empty)
  }

  @strictpure def paramId(n: String): String = s"_$n"

  @pure def unifyExp(silent: B,
                     th: TypeHierarchy,
                     localPatterns: LocalPatternSet,
                     pattern: AST.CoreExp.Base,
                     exp: AST.CoreExp.Base,
                     init: UnificationMap,
                     pendingApplications: MBox[PendingApplications],
                     substMap: MBox[HashMap[String, AST.Typed]],
                     errorMessages: MBox[UnificationErrorMessages]): UnificationMap = {
    var map = init
    @pure def rootLocalPatternOpt(e: AST.CoreExp.Base, args: ISZ[AST.CoreExp.Base]): Option[(ISZ[String], String, AST.Typed, ISZ[AST.CoreExp.Base])] = {
      e match {
        case e: AST.CoreExp.LocalVarRef =>
          val p = (e.context, e.id)
          val ls = LocalSubstitutor(map)
          return if (localPatterns.contains(p)) Some((p._1, p._2, e.tipe,
            for (arg <- args) yield ls.transformCoreExpBase(arg).getOrElse(arg))) else None()
        case e: AST.CoreExp.Apply => return rootLocalPatternOpt(e.exp, e.args ++ args)
        case _ => return None()
      }
    }
    def err(p: AST.CoreExp, e: AST.CoreExp): Unit = {
      if (silent) {
        if (errorMessages.value.isEmpty) {
          errorMessages.value = errorMessages.value :+ ""
        }
      } else {
        errorMessages.value = errorMessages.value :+
          st"Could not unify '${p.prettyST}' with '${e.prettyST}' in '${pattern.prettyST}' and '${exp.prettyST}'".render
      }
    }
    def err2(id: String, e1: AST.CoreExp, e2: AST.CoreExp): Unit = {
      if (silent) {
        if (errorMessages.value.isEmpty) {
          errorMessages.value = errorMessages.value :+ ""
        }
      } else {
        errorMessages.value = errorMessages.value :+
          st"Could not unify local pattern '$id' with both '${e1.prettyST}' and '${e2.prettyST}'".render
      }
    }
    def matchType(t1: AST.Typed, t2: AST.Typed, p: AST.CoreExp, e: AST.CoreExp): Unit = {
      def errType(et1: AST.Typed, et2: AST.Typed): Unit = {
        if (silent) {
          errorMessages.value = errorMessages.value :+ ""
        } else {
          errorMessages.value = errorMessages.value :+
            st"Could not unify types '$et1' and '$et2' in '${p.prettyST}' and '${e.prettyST}'".render
        }
      }
      (t1, t2) match {
        case (t1: AST.Typed.TypeVar, t2) =>
          substMap.value.get(t1.id) match {
            case Some(prevType) =>
              th.lub(ISZ(prevType, t2)) match {
                case Some(t3) => substMap.value = substMap.value + t1.id ~> t3
                case _ => errType(t2, prevType)
              }
            case _ => substMap.value = substMap.value + t1.id ~> t2
          }
        case (t1: AST.Typed.Name, t2: AST.Typed.Name) =>
          if (t1.args.size != t2.args.size || t1.ids != t2.ids) {
            errType(t1, t2)
          } else {
            for (i <- 0 until t1.args.size) {
              matchType(t1.args(i), t2.args(i), p, e)
            }
          }
        case (t1: AST.Typed.Tuple, t2: AST.Typed.Tuple) =>
          if (t1.args.size != t2.args.size) {
            errType(t1, t2)
          } else {
            for (i <- 0 until t1.args.size) {
              matchType(t1.args(i), t2.args(i), p, e)
            }
          }
        case (t1: AST.Typed.Fun, t2: AST.Typed.Fun) =>
          if (t1.args.size != t2.args.size) {
            errType(t1, t2)
          } else {
            for (i <- 0 until t1.args.size) {
              matchType(t1.args(i), t2.args(i), p, e)
            }
            matchType(t1.ret, t2.ret, p, e)
          }
        case (_, _) =>
          if (t1 != t2) {
            errType(t1, t2)
          }
      }
    }
    def matchPatternLocals(p: AST.CoreExp.Base, e: AST.CoreExp.Base): Unit = {
      if (errorMessages.value.nonEmpty) {
        return
      }
      (p, e) match {
        case (p: AST.CoreExp.Lit, e) =>
          if (p != e) {
            err(p, e)
          }
        case (p: AST.CoreExp.LocalVarRef, e) if p.isPattern =>
          val key = (p.context, p.id)
          if (localPatterns.contains(key)) {
            map.get(key) match {
              case Some(pe) =>
                if (pe != e) {
                  err2(p.id, pe, e)
                }
              case _ =>
                map = map + key ~> e
                matchType(p.tipe, e.tipe, p, e)
            }
          } else if (p != e) {
            err(p, e)
          }
        case (p: AST.CoreExp.LocalVarRef, e: AST.CoreExp.LocalVarRef) =>
          if (!(p.id == e.id && p.context == e.context)) {
            err(p, e)
          }
        case (p: AST.CoreExp.ParamVarRef, e: AST.CoreExp.ParamVarRef) =>
          if (p.deBruijn != e.deBruijn) {
            err(p, e)
          }
        case (p: AST.CoreExp.VarRef, e: AST.CoreExp.VarRef) =>
          if (!(p.id == e.id && p.owner == e.owner)) {
            err(p, e)
          }
        case (p: AST.CoreExp.Binary, e: AST.CoreExp.Binary) =>
          if (p.op != e.op) {
            err(p, e)
          } else {
            matchPatternLocals(p.left, e.left)
            matchPatternLocals(p.right, e.right)
          }
        case (p: AST.CoreExp.Unary, e: AST.CoreExp.Unary) =>
          if (p.op != e.op) {
            err(p, e)
          } else {
            matchPatternLocals(p.exp, e.exp)
          }
        case (p: AST.CoreExp.Constructor, e: AST.CoreExp.Constructor) =>
          if (p.args.size != e.args.size || p.tipe != e.tipe) {
            err(p, e)
          } else {
            for (i <- 0 until p.args.size) {
              matchPatternLocals(p.args(i), e.args(i))
            }
          }
        case (p: AST.CoreExp.Select, e: AST.CoreExp.Select) =>
          if (p.id != e.id) {
            err(p, e)
          } else {
            matchPatternLocals(p.exp, e.exp)
          }
        case (p: AST.CoreExp.Update, e: AST.CoreExp.Update) =>
          if (p.id != e.id) {
            err(p, e)
          } else {
            matchPatternLocals(p.exp, e.exp)
            matchPatternLocals(p.arg, e.arg)
          }
        case (p: AST.CoreExp.Indexing, e: AST.CoreExp.Indexing) =>
          matchPatternLocals(p.exp, e.exp)
          matchPatternLocals(p.index, e.index)
        case (p: AST.CoreExp.IndexingUpdate, e: AST.CoreExp.IndexingUpdate) =>
          matchPatternLocals(p.exp, e.exp)
          matchPatternLocals(p.index, e.index)
          matchPatternLocals(p.arg, e.arg)
        case (p: AST.CoreExp.If, e: AST.CoreExp.If) =>
          matchPatternLocals(p.cond, e.cond)
          matchPatternLocals(p.tExp, e.tExp)
          matchPatternLocals(p.fExp, e.fExp)
        case (p: AST.CoreExp.Apply, e) =>
          @pure def hasLocalPatternInArgs(args: ISZ[AST.CoreExp.Base]): B = {
            val lpd = LocalPatternDetector(localPatterns, F)
            for (arg <- args) {
              lpd.transformCoreExpBase(arg)
            }
            return lpd.hasLocalPattern
          }
          rootLocalPatternOpt(p, ISZ()) match {
            case Some((context, id, f: AST.Typed.Fun, args)) =>
              @strictpure def getArgTypes(t: AST.Typed, acc: ISZ[AST.Typed]): ISZ[AST.Typed] = t match {
                case f: AST.Typed.Fun => getArgTypes(f.ret, acc :+ f.args(0))
                case _ => acc
              }
              val argTypes = getArgTypes(f.curried, ISZ())
              if (args.size == argTypes.size) {
                if (hasLocalPatternInArgs(args)) {
                  pendingApplications.value = pendingApplications.value :+ (context, id, args, e)
                } else {
                  var substitutions = HashMap.empty[AST.CoreExp, AST.CoreExp.ParamVarRef]
                  for (i <- 0 until args.size) {
                    val n = args.size - i
                    substitutions = substitutions + args(i) ~> AST.CoreExp.ParamVarRef(n, paramId(n.string), argTypes(i))
                  }
                  val se = Substitutor(substitutions).transformCoreExpBase(e).getOrElse(e)
                  var r: AST.CoreExp.Base = AST.CoreExp.Fun(AST.CoreExp.Param(paramId(1.string), argTypes(args.size - 1).subst(substMap.value)), se)
                  for (i <- args.size - 2 to 0 by -1) {
                    r = AST.CoreExp.Fun(AST.CoreExp.Param(paramId((args.size - i).string), argTypes(i)), r)
                  }
                  val key = (context, id)
                  map.get(key) match {
                    case Some(f) if f != r => err2(id, f, r)
                    case _ => map = map + key ~> r
                  }
                }
                return
              }
            case _ =>
          }
          e match {
            case e: AST.CoreExp.Apply =>
              if (p.args.size != e.args.size) {
                err(p, e)
              } else {
                matchPatternLocals(p.exp, e.exp)
                for (argPair <- ops.ISZOps(p.args).zip(e.args)) {
                  matchPatternLocals(argPair._1, argPair._2)
                }
              }
            case _ => err(p, e)
          }
        case (p: AST.CoreExp.Fun, e: AST.CoreExp.Fun) =>
          matchPatternLocals(p.exp, e.exp)
        case (p: AST.CoreExp.Quant, e: AST.CoreExp.Quant) =>
          if (p.kind != e.kind) {
            err(p, e)
          } else {
            matchPatternLocals(p.exp, e.exp)
          }
        case (p: AST.CoreExp.InstanceOfExp, e: AST.CoreExp.InstanceOfExp) =>
          if (p.isTest != e.isTest || p.tipe != e.tipe) {
            err(p, e)
          } else {
            matchPatternLocals(p.exp, e.exp)
          }
        case (_, _) =>
          err(p, e)
      }
    }

    matchPatternLocals(pattern, exp)

    return map
  }

  @pure def unifyPendingApplications(silent: B,
                                     th: TypeHierarchy,
                                     localPatterns: LocalPatternSet,
                                     map: UnificationMap,
                                     pendingApplications: MBox[PendingApplications],
                                     substMap: MBox[HashMap[String, AST.Typed]],
                                     errorMessages: MBox[UnificationErrorMessages]): UnificationResult = {
    var m = map
    //while (pendingApplications.value.nonEmpty) {
    val pas = pendingApplications.value
    pendingApplications.value = ISZ()
    for (pa <- pas) {
      val (context, id, args, e) = pa
      m.get((context, id)) match {
        case Some(f: AST.CoreExp.Fun) =>
          applyFun(f, args, e.tipe) match {
            case Some((pattern, _)) =>
              m = unifyExp(silent, th, localPatterns, pattern, e, m, pendingApplications, substMap, errorMessages)
            case _ =>
              if (silent) {
                if (errorMessages.value.isEmpty) {
                  errorMessages.value = errorMessages.value :+ ""
                }
              } else {
                errorMessages.value = errorMessages.value :+
                  st"Could not reduce '$f(${(for (arg <- args) yield arg.prettyST, ", ")})'".render
              }
          }
        case Some(f) => errorMessages.value = errorMessages.value :+ s"Expecting to infer a function, but found '$f'"
        case _ =>
      }
      if (errorMessages.value.nonEmpty) {
        return Either.Right(errorMessages.value)
      }
    }
    //}
    for (localPattern <- localPatterns.elements if !m.contains(localPattern)) {
      if (silent) {
        if (errorMessages.value.isEmpty) {
          errorMessages.value = errorMessages.value :+ ""
        }
      } else {
        errorMessages.value = errorMessages.value :+ s"Could not find any matching expression for '${localPattern._2}'"
      }
    }
    return if (errorMessages.value.nonEmpty) Either.Right(errorMessages.value)
    else Either.Left(HashSMap ++ (for (p <- m.entries) yield (p._1, p._2.subst(substMap.value))))
  }

  @pure def unify(silent: B, th: TypeHierarchy, localPatterns: LocalPatternSet, patterns: ISZ[AST.CoreExp.Base], exps: ISZ[AST.CoreExp.Base]): UnificationResult = {
    val errorMessages: MBox[UnificationErrorMessages] = MBox(ISZ())
    val pendingApplications: MBox[PendingApplications] = MBox(ISZ())
    val substMap: MBox[HashMap[String, AST.Typed]] = MBox(HashMap.empty)
    var m: UnificationMap = HashSMap.empty
    for (i <- 0 until patterns.size) {
      m = unifyExp(silent, th, localPatterns, patterns(i), exps(i), m, pendingApplications, substMap, errorMessages)
      if (errorMessages.value.nonEmpty) {
        return Either.Right(errorMessages.value)
      }
    }
    return unifyPendingApplications(silent, th, localPatterns, m, pendingApplications, substMap, errorMessages)
  }

  @strictpure def evalBinaryLit(lit1: AST.CoreExp.Lit, op: String, lit2: AST.CoreExp.Lit): AST.CoreExp.Base = {
    if (op == AST.Exp.BinaryOp.MapsTo) {
      AST.CoreExp.Constructor(AST.Typed.Tuple(ISZ(lit1.tipe, lit2.tipe)), ISZ(lit1, lit2))
    } else {
      lit1 match {
        case lit1: AST.CoreExp.LitB =>
          val left = lit1.value
          val right = lit2.asInstanceOf[AST.CoreExp.LitB].value
          op match {
            case AST.Exp.BinaryOp.And => AST.CoreExp.LitB(left & right)
            case AST.Exp.BinaryOp.Or => AST.CoreExp.LitB(left | right)
            case AST.Exp.BinaryOp.Xor => AST.CoreExp.LitB(left |^ right)
            case AST.Exp.BinaryOp.Imply => AST.CoreExp.LitB(left __>: right)
            case AST.Exp.BinaryOp.EquivUni => AST.CoreExp.LitB(left ≡ right)
            case AST.Exp.BinaryOp.InequivUni => AST.CoreExp.LitB(left ≢ right)
            case _ => halt(s"Infeasible: $op on B")
          }
        case lit1: AST.CoreExp.LitZ =>
          val left = lit1.value
          val right = lit2.asInstanceOf[AST.CoreExp.LitZ].value
          op match {
            case AST.Exp.BinaryOp.Add => AST.CoreExp.LitZ(left + right)
            case AST.Exp.BinaryOp.Sub => AST.CoreExp.LitZ(left - right)
            case AST.Exp.BinaryOp.Mul => AST.CoreExp.LitZ(left * right)
            case AST.Exp.BinaryOp.Div => AST.CoreExp.LitZ(left / right)
            case AST.Exp.BinaryOp.Rem => AST.CoreExp.LitZ(left % right)
            case AST.Exp.BinaryOp.Lt => AST.CoreExp.LitB(left < right)
            case AST.Exp.BinaryOp.Le => AST.CoreExp.LitB(left <= right)
            case AST.Exp.BinaryOp.Gt => AST.CoreExp.LitB(left > right)
            case AST.Exp.BinaryOp.Ge => AST.CoreExp.LitB(left >= right)
            case AST.Exp.BinaryOp.EquivUni => AST.CoreExp.LitB(left ≡ right)
            case AST.Exp.BinaryOp.InequivUni => AST.CoreExp.LitB(left ≢ right)
            case _ => halt(s"Infeasible: $op on Z")
          }
        case lit1: AST.CoreExp.LitC =>
          val left = lit1.value
          val right = lit2.asInstanceOf[AST.CoreExp.LitC].value
          op match {
            case AST.Exp.BinaryOp.And => AST.CoreExp.LitC(left & right)
            case AST.Exp.BinaryOp.Or => AST.CoreExp.LitC(left | right)
            case AST.Exp.BinaryOp.Xor => AST.CoreExp.LitC(left |^ right)
            case AST.Exp.BinaryOp.Add => AST.CoreExp.LitC(left + right)
            case AST.Exp.BinaryOp.Sub => AST.CoreExp.LitC(left - right)
            case AST.Exp.BinaryOp.Lt => AST.CoreExp.LitB(left < right)
            case AST.Exp.BinaryOp.Le => AST.CoreExp.LitB(left <= right)
            case AST.Exp.BinaryOp.Gt => AST.CoreExp.LitB(left > right)
            case AST.Exp.BinaryOp.Ge => AST.CoreExp.LitB(left >= right)
            case AST.Exp.BinaryOp.EquivUni => AST.CoreExp.LitB(left ≡ right)
            case AST.Exp.BinaryOp.InequivUni => AST.CoreExp.LitB(left ≢ right)
            case AST.Exp.BinaryOp.Shl => AST.CoreExp.LitC(left << right)
            case AST.Exp.BinaryOp.Shr => AST.CoreExp.LitC(left >> right)
            case AST.Exp.BinaryOp.Ushr => AST.CoreExp.LitC(left >>> right)
            case _ => halt(s"Infeasible: $op on C")
          }
        case lit1: AST.CoreExp.LitF32 =>
          val left = lit1.value
          val right = lit2.asInstanceOf[AST.CoreExp.LitF32].value
          op match {
            case AST.Exp.BinaryOp.Add => AST.CoreExp.LitF32(left + right)
            case AST.Exp.BinaryOp.Sub => AST.CoreExp.LitF32(left - right)
            case AST.Exp.BinaryOp.Mul => AST.CoreExp.LitF32(left * right)
            case AST.Exp.BinaryOp.Div => AST.CoreExp.LitF32(left / right)
            case AST.Exp.BinaryOp.Rem => AST.CoreExp.LitF32(left % right)
            case AST.Exp.BinaryOp.Lt => AST.CoreExp.LitB(left < right)
            case AST.Exp.BinaryOp.Le => AST.CoreExp.LitB(left <= right)
            case AST.Exp.BinaryOp.Gt => AST.CoreExp.LitB(left > right)
            case AST.Exp.BinaryOp.Ge => AST.CoreExp.LitB(left >= right)
            case AST.Exp.BinaryOp.EquivUni => AST.CoreExp.LitB(left ≡ right)
            case AST.Exp.BinaryOp.FpEq => AST.CoreExp.LitB(left ~~ right)
            case AST.Exp.BinaryOp.InequivUni => AST.CoreExp.LitB(left ≢ right)
            case AST.Exp.BinaryOp.FpNe => AST.CoreExp.LitB(left !~ right)
            case _ => halt(s"Infeasible: $op on F32")
          }
        case lit1: AST.CoreExp.LitF64 =>
          val left = lit1.value
          val right = lit2.asInstanceOf[AST.CoreExp.LitF64].value
          op match {
            case AST.Exp.BinaryOp.Add => AST.CoreExp.LitF64(left + right)
            case AST.Exp.BinaryOp.Sub => AST.CoreExp.LitF64(left - right)
            case AST.Exp.BinaryOp.Mul => AST.CoreExp.LitF64(left * right)
            case AST.Exp.BinaryOp.Div => AST.CoreExp.LitF64(left / right)
            case AST.Exp.BinaryOp.Rem => AST.CoreExp.LitF64(left % right)
            case AST.Exp.BinaryOp.Lt => AST.CoreExp.LitB(left < right)
            case AST.Exp.BinaryOp.Le => AST.CoreExp.LitB(left <= right)
            case AST.Exp.BinaryOp.Gt => AST.CoreExp.LitB(left > right)
            case AST.Exp.BinaryOp.Ge => AST.CoreExp.LitB(left >= right)
            case AST.Exp.BinaryOp.Eq => AST.CoreExp.LitB(left ≡ right)
            case AST.Exp.BinaryOp.FpEq => AST.CoreExp.LitB(left ~~ right)
            case AST.Exp.BinaryOp.InequivUni => AST.CoreExp.LitB(left ≢ right)
            case AST.Exp.BinaryOp.FpNe => AST.CoreExp.LitB(left !~ right)
            case _ => halt(s"Infeasible: $op on F64")
          }
        case lit1: AST.CoreExp.LitR =>
          val left = lit1.value
          val right = lit2.asInstanceOf[AST.CoreExp.LitR].value
          op match {
            case AST.Exp.BinaryOp.Add => AST.CoreExp.LitR(left + right)
            case AST.Exp.BinaryOp.Sub => AST.CoreExp.LitR(left - right)
            case AST.Exp.BinaryOp.Mul => AST.CoreExp.LitR(left * right)
            case AST.Exp.BinaryOp.Div => AST.CoreExp.LitR(left / right)
            case AST.Exp.BinaryOp.Lt => AST.CoreExp.LitB(left < right)
            case AST.Exp.BinaryOp.Le => AST.CoreExp.LitB(left < right)
            case AST.Exp.BinaryOp.Gt => AST.CoreExp.LitB(left > right)
            case AST.Exp.BinaryOp.Ge => AST.CoreExp.LitB(left >= right)
            case AST.Exp.BinaryOp.EquivUni => AST.CoreExp.LitB(left ≡ right)
            case AST.Exp.BinaryOp.InequivUni => AST.CoreExp.LitB(left ≢ right)
            case _ => halt(s"Infeasible: $op on R")
          }
        case lit1: AST.CoreExp.LitRange => halt(st"TODO: ${lit1.prettyST} $op ${lit2.prettyST}".render)
        case lit1: AST.CoreExp.LitBits => halt(st"TODO: ${lit1.prettyST} $op ${lit2.prettyST}".render)
        case lit1: AST.CoreExp.LitString => halt(st"TODO: ${lit1.prettyST} $op ${lit2.prettyST}".render)
        case lit1: AST.CoreExp.LitEnum =>
          val left = lit1.ordinal
          val right = lit2.asInstanceOf[AST.CoreExp.LitEnum].ordinal
          op match {
            case AST.Exp.BinaryOp.EquivUni => AST.CoreExp.LitB(left == right)
            case AST.Exp.BinaryOp.InequivUni => AST.CoreExp.LitB(left != right)
            case _ => halt(s"Infeasible: $op on ${lit1.owner(lit1.owner.size - 1)}.${lit1.id}")
          }
      }
    }
  }

  @strictpure def evalUnaryLit(op: AST.Exp.UnaryOp.Type, lit: AST.CoreExp.Lit): AST.CoreExp.Lit =
    lit match {
      case lit: AST.CoreExp.LitB =>
        op match {
          case AST.Exp.UnaryOp.Not => AST.CoreExp.LitB(!lit.value)
          case AST.Exp.UnaryOp.Complement => AST.CoreExp.LitB(~lit.value)
          case _ => halt(s"Infeasible $op on B")
        }
      case lit: AST.CoreExp.LitZ =>
        op match {
          case AST.Exp.UnaryOp.Plus => AST.CoreExp.LitZ(lit.value)
          case AST.Exp.UnaryOp.Minus => AST.CoreExp.LitZ(-lit.value)
          case _ => halt(s"Infeasible $op on Z")
        }
      case lit: AST.CoreExp.LitC =>
        op match {
          case AST.Exp.UnaryOp.Complement => AST.CoreExp.LitC(~lit.value)
          case _ => halt(s"Infeasible $op on C")
        }
      case lit: AST.CoreExp.LitF32 =>
        op match {
          case AST.Exp.UnaryOp.Plus => AST.CoreExp.LitF32(lit.value)
          case AST.Exp.UnaryOp.Minus => AST.CoreExp.LitF32(lit.value)
          case _ => halt(s"Infeasible $op on F32")
        }
      case lit: AST.CoreExp.LitF64 =>
        op match {
          case AST.Exp.UnaryOp.Plus => AST.CoreExp.LitF64(lit.value)
          case AST.Exp.UnaryOp.Minus => AST.CoreExp.LitF64(-lit.value)
          case _ => halt(s"Infeasible $op on F64")
        }
      case lit: AST.CoreExp.LitR =>
        op match {
          case AST.Exp.UnaryOp.Plus => AST.CoreExp.LitR(lit.value)
          case AST.Exp.UnaryOp.Minus => AST.CoreExp.LitR(-lit.value)
          case _ => halt(s"Infeasible $op on R")
        }
      case lit: AST.CoreExp.LitBits => halt(st"TODO: $op ${lit.prettyST}".render)
      case lit: AST.CoreExp.LitRange => halt(st"TODO: $op ${lit.prettyST}".render)
      case lit: AST.CoreExp.LitString => halt(st"TODO: $op ${lit.prettyST}".render)
      case lit: AST.CoreExp.LitEnum => halt(s"Infeasible $op on ${lit.owner(lit.owner.size - 1)}.${lit.id}")
    }

  @pure def eval(th: TypeHierarchy,
                 config: EvalConfig,
                 cache: Logika.Cache,
                 methodPatterns: MethodPatternMap,
                 unfoldingMap: MBox[UnfoldingNumMap],
                 maxUnfolding: Z,
                 provenClaims: HashSMap[AST.CoreExp.Base, AST.ProofAst.StepId],
                 exp: AST.CoreExp,
                 removeLabels: B,
                 shouldTrace: B): Option[(AST.CoreExp, ISZ[Trace])] = {
    exp match {
      case exp: AST.CoreExp.Arrow =>
        var changed = F
        var trace = ISZ[Trace]()
        val left: AST.CoreExp.Base = evalBase(th, config, cache, methodPatterns, unfoldingMap, maxUnfolding,
          provenClaims, exp.left, removeLabels, shouldTrace) match {
          case Some((l, t)) =>
            trace = trace ++ t
            changed = T
            l
          case _ => exp.left
        }
        val right: AST.CoreExp = eval(th, config, cache, methodPatterns, unfoldingMap, maxUnfolding, provenClaims,
          exp.right, removeLabels, shouldTrace) match {
          case Some((r, t)) =>
            trace = trace ++ t
            changed = T
            r
          case _ => exp.right
        }
        return if (changed) Some((AST.CoreExp.Arrow(left, right), trace)) else None()
      case exp: AST.CoreExp.Base => evalBase(th, config, cache, methodPatterns, unfoldingMap, maxUnfolding,
        provenClaims, exp, removeLabels, shouldTrace) match {
        case Some((e, t)) => return Some((e, t))
        case _ => return None()
      }
    }
  }

  @pure def simplify(th: TypeHierarchy, exp: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
    evalBase(th, EvalConfig.all, NoCache(), HashSMap.empty, MBox(HashSMap.empty), 1, HashSMap.empty, exp, T, F) match {
      case Some((r, _)) => return Some(r)
      case _ => return None()
    }
  }

  @strictpure def incDeBruijnMap(deBruijnMap: HashMap[Z, AST.CoreExp.Base], inc: Z): HashMap[Z, AST.CoreExp.Base] =
    if (inc != 0) HashMap ++ (for (p <- deBruijnMap.entries) yield (p._1 + inc, p._2)) else deBruijnMap

  @pure def applyFun(f: AST.CoreExp.Fun, args: ISZ[AST.CoreExp.Base], t: AST.Typed): Option[(AST.CoreExp.Base, Z)] = {
    var params = ISZ[(String, AST.Typed)]()
    @tailrec def recParamsFun(fe: AST.CoreExp.Base): AST.CoreExp.Base = {
      fe match {
        case fe: AST.CoreExp.Fun if params.size < args.size =>
          params = params :+ (fe.param.id, fe.param.tipe)
          return recParamsFun(fe.exp)
        case _ => return fe
      }
    }
    val body = recParamsFun(f)
    var map = HashMap.empty[Z, AST.CoreExp.Base]
    for (i <- 0 until params.size) {
      map = map + (params.size - i) ~> args(i)
    }
    if (f.param.tipe == AST.Typed.unit && args.isEmpty) {
      return Some((f.exp, 0))
    }
    ParamSubstitutor(map).transformCoreExpBase(body) match {
      case MSome(body2) =>
        if (args.size > params.size) {
          return Some((AST.CoreExp.Apply(body2, ops.ISZOps(args).slice(params.size, args.size), t), params.size))
        } else {
          return Some((body2, args.size))
        }
      case _ => return None()
    }
  }

  @pure def applyQuant(q: AST.CoreExp.Quant, args: ISZ[AST.CoreExp.Base], t: AST.Typed): Option[(AST.CoreExp.Base, Z)] = {
    var params = ISZ[(String, AST.Typed)]()
    @tailrec def recParamsQuant(fe: AST.CoreExp.Base): AST.CoreExp.Base = {
      fe match {
        case fe: AST.CoreExp.Quant if params.size < args.size =>
          params = params :+ (fe.param.id, fe.param.tipe)
          return recParamsQuant(fe.exp)
        case _ => return fe
      }
    }
    val body = recParamsQuant(q)
    var map = HashMap.empty[Z, AST.CoreExp.Base]
    for (i <- 0 until params.size) {
      map = map + (params.size - i) ~> args(i)
    }
    ParamSubstitutor(map).transformCoreExpBase(body) match {
      case MSome(body2) =>
        if (args.size > params.size) {
          return Some((AST.CoreExp.Apply(body2, ops.ISZOps(args).slice(params.size, args.size), t), params.size))
        } else {
          return Some((body2, args.size))
        }
      case _ =>
    }
    return None()
  }

  @pure def evalBase(th: TypeHierarchy,
                     config: EvalConfig,
                     cache: Logika.Cache,
                     methodPatterns: MethodPatternMap,
                     unfoldingMap: MBox[UnfoldingNumMap],
                     maxUnfolding: Z,
                     provenClaims: HashSMap[AST.CoreExp.Base, AST.ProofAst.StepId],
                     exp: AST.CoreExp.Base,
                     removeLabels: B,
                     shouldTrace: B): Option[(AST.CoreExp.Base, ISZ[Trace])] = {
    @strictpure def equivST(left: AST.CoreExp.Base, right: AST.CoreExp.Base): ST =
      AST.CoreExp.Binary(left, AST.Exp.BinaryOp.EquivUni, right, AST.Typed.b).prettyST

    @strictpure def inequivST(left: AST.CoreExp.Base, right: AST.CoreExp.Base): ST =
      AST.CoreExp.Binary(left, AST.Exp.BinaryOp.InequivUni, right, AST.Typed.b).prettyST

    @strictpure def equiv(left: AST.CoreExp.Base, right: AST.CoreExp.Base): AST.CoreExp.Binary =
      if (right < left) AST.CoreExp.Binary(right, AST.Exp.BinaryOp.EquivUni, left, AST.Typed.b)
      else AST.CoreExp.Binary(left, AST.Exp.BinaryOp.EquivUni, right, AST.Typed.b)

    @strictpure def inequiv(left: AST.CoreExp.Base, right: AST.CoreExp.Base): AST.CoreExp.Binary =
      if (right < left) AST.CoreExp.Binary(right, AST.Exp.BinaryOp.InequivUni, left, AST.Typed.b)
      else AST.CoreExp.Binary(left, AST.Exp.BinaryOp.InequivUni, right, AST.Typed.b)

    def shouldUnfold(info: Info.Method): B = {
      val r = !info.ast.hasContract && info.ast.isStrictPure &&
        ((info.ast.purity == AST.Purity.Abs) ->: methodPatterns.contains((info.name, info.isInObject)))
      if (!r) {
        return F
      }
      return unfoldingMap.value.get((info.name, info.isInObject)).getOrElse(0) < maxUnfolding
    }

    def unfold(info: Info.Method, receiverOpt: Option[AST.CoreExp.Base]): AST.CoreExp.Base = {
      val key = (info.name, info.isInObject)
      unfoldingMap.value = unfoldingMap.value + key ~> (unfoldingMap.value.get(key).getOrElse(0) + 1)
      val pattern = methodPatternOf(th, cache, info)
      val f = pattern.toFun
      receiverOpt match {
        case Some(receiver) => return AST.CoreExp.Apply(f, ISZ(receiver), f.exp.tipe)
        case _ => return if (info.ast.sig.funType.isByName) AST.CoreExp.Apply(f, ISZ(), f.exp.tipe) else f
      }
    }

    var trace = ISZ[Trace]()
    var evalCache = HashMap.empty[AST.CoreExp.Base, Option[AST.CoreExp.Base]]

    def setCache(e: AST.CoreExp.Base, rOpt: Option[AST.CoreExp.Base]): Unit = {
      evalCache = evalCache + e ~> rOpt
    }

    def evalBaseH(e: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
      evalCache.get(e) match {
        case Some(rOpt) => rOpt match {
          case Some(r) =>
            trace = trace :+ Trace.Eval(st"cache", e, r)
            return Some(r)
          case _ => return rOpt
        }
        case _ =>
      }
      val eqMap: HashMap[AST.CoreExp.Base, (AST.CoreExp.Base, AST.ProofAst.StepId)] = if (config.equivSubst) {
        var r = HashMap.empty[AST.CoreExp.Base, (AST.CoreExp.Base, AST.ProofAst.StepId)]
        for (p <- provenClaims.entries) {
          val (claim, stepId) = p
          claim match {
            case AST.CoreExp.Binary(left, AST.Exp.BinaryOp.EquivUni, right, _) =>
              (left, right) match {
                case (left: AST.CoreExp.Lit, _) => r = r + right ~> (left, stepId)
                case (_, right: AST.CoreExp.Lit) => r = r + left ~> (right, stepId)
                case (left: AST.CoreExp.Constructor, _) => r = r + right ~> (left, stepId)
                case (_, right: AST.CoreExp.Constructor) => r = r + left ~> (right, stepId)
                case (_, _) =>
                  val (key, value): (AST.CoreExp.Base, AST.CoreExp.Base) =
                    if (left < right) (right, left) else (left, right)
                  r.get(key) match {
                    case Some((prev, _)) =>
                      if (value < prev) {
                        r = r + key ~> (value, stepId)
                      }
                    case _ => r = r + key ~> (value, stepId)
                  }
              }
            case _ =>
          }
        }
        r
      } else {
        HashMap.empty
      }
      var rOpt = Option.none[AST.CoreExp.Base]()
      if (e.tipe == AST.Typed.b) {
        provenClaims.get(e) match {
          case Some(stepId) =>
            val r = AST.CoreExp.True
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"using $stepId", e, r)
            }
            rOpt = Some(r)
          case _ =>
        }
        if (rOpt.isEmpty) {
          provenClaims.get(AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, e)) match {
            case Some(stepId) =>
              val r = AST.CoreExp.False
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"using $stepId", e, r)
              }
              rOpt = Some(r)
            case _ =>
          }
        }
      }
      if (rOpt.isEmpty && config.equivSubst) {
        val r = eqMap.get(e)
        r match {
          case Some((to, stepId)) =>
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"substitution using $stepId [${to.prettyST}/${e.prettyST}]", e, to)
            }
            rOpt = Some(to)
          case _ =>
        }
      }
      if (rOpt.isEmpty) {
        rOpt = e match {
          case _: AST.CoreExp.Halt => None()
          case _: AST.CoreExp.Lit => None()
          case _: AST.CoreExp.LocalVarRef => None()
          case e: AST.CoreExp.ParamVarRef => evalParamVarRef(e)
          case e: AST.CoreExp.VarRef => evalVarRef(e)
          case e: AST.CoreExp.Binary => evalBinary(e)
          case e: AST.CoreExp.Unary => evalUnary(e)
          case e: AST.CoreExp.Select => evalSelect(e)
          case e: AST.CoreExp.Update => evalUpdate(e)
          case e: AST.CoreExp.Indexing => evalIndexing(e)
          case e: AST.CoreExp.IndexingUpdate => evalIndexingUpdate(e)
          case e: AST.CoreExp.Constructor => evalConstructor(e)
          case e: AST.CoreExp.If => evalIf(e)
          case e: AST.CoreExp.Apply => evalApply(e)
          case e: AST.CoreExp.Fun => evalFun(e)
          case e: AST.CoreExp.Quant => evalQuant(e)
          case e: AST.CoreExp.InstanceOfExp => evalInstanceOf(e)
          case e: AST.CoreExp.Labeled => evalLabeled(e)
        }
      }
      rOpt match {
        case Some(r) =>
          eqMap.get(r) match {
            case Some((to, stepId)) =>
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"substitution using $stepId [${to.prettyST}/${e.prettyST}]", e, to)
              }
              rOpt = Some(to)
            case _ =>
          }
        case _ =>
      }
      setCache(e, rOpt)
      var done = rOpt.isEmpty
      while (!done) {
        rOpt match {
          case Some(_: AST.CoreExp.Lit) => done = T
          case Some(r) =>
            val rOpt2 = evalBaseH(r)
            rOpt2 match {
              case Some(r2) =>
                if (r != r2) {
                  setCache(r, rOpt2)
                  setCache(e, rOpt2)
                  rOpt = rOpt2
                } else {
                  setCache(r, None())
                  done = T
                }
              case _ =>
                setCache(r, None())
                done = T
            }
          case _ => done = T
        }
      }
      return rOpt
    }

    def evalParamVarRef(e: AST.CoreExp.ParamVarRef): Option[AST.CoreExp.Base] = {
      return None()
    }

    def evalVarRef(e: AST.CoreExp.VarRef): Option[AST.CoreExp.Base] = {
      val minfo: Info.Method = if (e.isInObject) {
        th.nameMap.get(e.owner :+ e.id) match {
          case Some(info: Info.Method) => info
          case _ => return None()
        }
      } else {
        th.typeMap.get(e.owner).get match {
          case ti: TypeInfo.Sig => ti.methods.get(e.id).get
          case ti: TypeInfo.Adt => ti.methods.get(e.id).get
          case ti: TypeInfo.Enum => halt(s"TODO: $ti")
          case ti: TypeInfo.SubZ => halt(s"TODO: $ti")
          case _ => halt("Infeasible")
        }
      }
      if (shouldUnfold(minfo)) {
        val r = unfold(minfo, None())
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"unfolding", e, r)
        }
        return Some(r)
      }
      return None()
    }

    def evalBinary(e: AST.CoreExp.Binary): Option[AST.CoreExp.Base] = {
      var changed = F
      val left: AST.CoreExp.Base = evalBaseH(e.left) match {
        case Some(l) =>
          changed = T
          l
        case _ => e.left
      }
      val right: AST.CoreExp.Base = evalBaseH(e.right) match {
        case Some(r) =>
          changed = T
          r
        case _ => e.right
      }
      if ((left.isHalt || right.isHalt) && e.op != AST.Exp.BinaryOp.EquivUni &&
        e.op != AST.Exp.BinaryOp.InequivUni) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(left = left, right = right).prettyST}", e, r)
        }
        return Some(r)
      }
      if (e.op == AST.Exp.BinaryOp.MapsTo) {
        val r = AST.CoreExp.Constructor(AST.Typed.Tuple(ISZ(left.tipe, right.tipe)), ISZ(left, right))
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"tuple construction ${equivST(AST.CoreExp.Binary(left, "~>", right, r.tipe), r)}", e, r)
        }
        return Some(r)
      }
      if (config.constant) {
        (left, right) match {
          case (left: AST.CoreExp.Lit, right: AST.CoreExp.Lit) =>
            val r = evalBinaryLit(left, e.op, right)
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"constant binop ${equivST(AST.CoreExp.Binary(left, e.op, right, r.tipe), r)}", e, r)
            }
            return Some(r)
          case _ =>
        }
      }
      var rOpt = Option.none[AST.CoreExp.Base]()
      e.op match {
        case AST.Exp.BinaryOp.And =>
          def andF: Option[AST.CoreExp.Base] = {
            val r = AST.CoreExp.False
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"${equiv(e(left = left, right = right), AST.CoreExp.False)}", e, r)
            }
            return Some(r)
          }
          (left, right) match {
            case (AST.CoreExp.False, _) => return andF
            case (_, AST.CoreExp.False) => return andF
            case (_ , _) =>
          }
        case AST.Exp.BinaryOp.Or =>
          def orT: Option[AST.CoreExp.Base] = {
            val r = AST.CoreExp.True
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"${equiv(e(left = left, right = right), AST.CoreExp.True)}", e, r)
            }
            return Some(r)
          }
          (left, right) match {
            case (AST.CoreExp.True, _) => return orT
            case (_, AST.CoreExp.True) => return orT
            case (_ , _) =>
          }
        case AST.Exp.BinaryOp.Imply =>
          def implyT: Option[AST.CoreExp.Base] = {
            val r = AST.CoreExp.True
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"${equiv(e(left = left, right = right), AST.CoreExp.True)}", e, r)
            }
            return Some(r)
          }
          (left, right) match {
            case (_, AST.CoreExp.True) => return implyT
            case (_ , _) =>
          }
        case AST.Exp.BinaryOp.Mul =>
          if (left.isZero) {
            rOpt = Some(left)
          } else if (right.isZero) {
            rOpt = Some(right)
          } else if (left.isOne) {
            rOpt = Some(right)
          } else if (right.isOne) {
            rOpt = Some(left)
          } else if (left.isMinusOne) {
            rOpt = Some(AST.CoreExp.Unary(AST.Exp.UnaryOp.Minus, right))
          } else if (right.isMinusOne) {
            rOpt = Some(AST.CoreExp.Unary(AST.Exp.UnaryOp.Minus, left))
          }
        case AST.Exp.BinaryOp.Add =>
          if (left.isZero) {
            rOpt = Some(right)
          } else if (right.isZero) {
            rOpt = Some(left)
          }
        case AST.Exp.BinaryOp.Sub =>
          if (left.isZero) {
            rOpt = Some(right)
          } else if (right.isZero) {
            rOpt = Some(left)
          }
        case AST.Exp.BinaryOp.Div =>
          if (right.isOne) {
            rOpt = Some(left)
          } else if (right.isMinusOne) {
            rOpt = Some(AST.CoreExp.Unary(AST.Exp.UnaryOp.Minus, left))
          }
        case _ =>
      }
      rOpt match {
        case Some(r) =>
          if (shouldTrace) {
            trace = trace :+ Trace.Eval(st"${equiv(e(left = left, right = right), r)}", e, r)
          }
          return rOpt
        case _ =>
      }
      if (config.equality) {
        if (left == right) {
          rOpt = e.op match {
            case AST.Exp.BinaryOp.EquivUni => Some(AST.CoreExp.True)
            case AST.Exp.BinaryOp.InequivUni => Some(AST.CoreExp.False)
            case AST.Exp.BinaryOp.Lt => Some(AST.CoreExp.False)
            case AST.Exp.BinaryOp.Le => Some(AST.CoreExp.True)
            case AST.Exp.BinaryOp.Gt => Some(AST.CoreExp.False)
            case AST.Exp.BinaryOp.Ge => Some(AST.CoreExp.True)
            case AST.Exp.BinaryOp.Eq => Some(AST.CoreExp.True)
            case AST.Exp.BinaryOp.Ne => Some(AST.CoreExp.False)
            case _ => None()
          }
          rOpt match {
            case Some(r) =>
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"equivalence ${equivST(left, right)}", e, r)
              }
              return rOpt
            case _ =>
          }
        }
        provenClaims.get(inequiv(left, right)) match {
          case Some(stepId) =>
            rOpt = e.op match {
              case AST.Exp.BinaryOp.EquivUni => Some(AST.CoreExp.False)
              case AST.Exp.BinaryOp.InequivUni => Some(AST.CoreExp.True)
              case _ => None()
            }
            rOpt match {
              case Some(r) =>
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"inequivalence ($stepId) ${inequivST(left, right)}", e, r)
                }
                return rOpt
              case _ =>
            }
          case _ =>
        }
      }
      val r = e(left = left, right = right)
      return if (changed) Some(r) else None()
    }

    def evalUnary(e: AST.CoreExp.Unary): Option[AST.CoreExp.Base] = {
      var changed = F
      val receiver: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(exp2) =>
          changed = T
          exp2
        case _ => e.exp
      }
      if (receiver.isHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(exp = receiver).prettyST}", e, r)
        }
        return Some(r)
      }
      if (config.constant) {
        receiver match {
          case exp: AST.CoreExp.Lit =>
            val r = evalUnaryLit(e.op, exp)
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"constant unop ${equivST(AST.CoreExp.Unary(e.op, exp), r)}", e, r)
            }
            return Some(r)
          case _ =>
        }
      }
      if (e.tipe == AST.Typed.b && e.op == AST.Exp.UnaryOp.Not) {
        provenClaims.get(e) match {
          case Some(stepId) =>
            val r = AST.CoreExp.True
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"! using $stepId", e, r)
            }
            return Some(r)
          case _ =>
        }
      }
      if (config.unary) {
        e.op match {
          case AST.Exp.UnaryOp.Plus =>
            val r = receiver
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"unary ${equivST(AST.CoreExp.Unary(e.op, receiver), r)}", e, r)
            }
            return Some(r)
          case _ =>
            receiver match {
              case receiver: AST.CoreExp.Unary =>
                if (e.op == receiver.op) {
                  val r = receiver.exp
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"unary ${equivST(AST.CoreExp.Unary(e.op, receiver), r)}", e, r)
                  }
                  return Some(r)
                }
              case receiver: AST.CoreExp.Binary if e.op == AST.Exp.UnaryOp.Not =>
                def notBin(negateLeft: B, op: String): Option[AST.CoreExp.Base] = {
                  val left: AST.CoreExp.Base = if (negateLeft) AST.CoreExp.Unary(e.op, receiver.left) else receiver.left
                  val r = receiver(left = left, op = op, right = AST.CoreExp.Unary(e.op, receiver.right))
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"unary ${equivST(AST.CoreExp.Unary(e.op, receiver), r)}", e, r)
                  }
                  return evalBaseH(r)
                }
                val newOp: String = receiver.op match {
                  case AST.Exp.BinaryOp.And => return notBin(T, AST.Exp.BinaryOp.Or)
                  case AST.Exp.BinaryOp.Or => return notBin(T, AST.Exp.BinaryOp.And)
                  case AST.Exp.BinaryOp.Imply => return notBin(F, AST.Exp.BinaryOp.And)
                  case _ => negBinaryOp(receiver.op)
                }
                if (receiver.op != newOp) {
                  val r = receiver(op = newOp)
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"unary ${equivST(AST.CoreExp.Unary(e.op, receiver), r)}", e, r)
                  }
                  return evalBaseH(r)
                }
              case receiver: AST.CoreExp.If =>
                val r = receiver(tExp = AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, receiver.tExp),
                  fExp = AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, receiver.fExp))
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"unary ${equivST(AST.CoreExp.Unary(e.op, receiver), r)}", e, r)
                }
                return Some(r)
              case _ =>
            }
        }
      }
      val r = e(exp = receiver)
      return if (changed) Some(r) else None()
    }

    def evalSelect(e: AST.CoreExp.Select): Option[AST.CoreExp.Base] = {
      var changed = F
      val receiver: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(exp2) =>
          changed = T
          exp2
        case _ => e.exp
      }
      if (receiver.isHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(exp = receiver).prettyST}", e, r)
        }
        return Some(r)
      }
      if (config.tupleProjection && receiver.tipe.isInstanceOf[AST.Typed.Tuple]) {
        receiver match {
          case receiver: AST.CoreExp.Constructor =>
            val n = Z(ops.StringOps(e.id).substring(1, e.id.size)).get - 1
            val r = receiver.args(n)
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"tuple projection ${equivST(AST.CoreExp.Select(receiver, s"_${n + 1}", r.tipe), r)}", e, r)
            }
            return Some(r)
          case _ =>
        }
      }
      val infoOpt: Option[Info.Method] = receiver.tipe match {
        case rt: AST.Typed.Name =>
          th.typeMap.get(rt.ids).get match {
            case ti: TypeInfo.Adt =>
              ti.methods.get(e.id) match {
                case io@Some(info) if shouldUnfold(info) => io
                case _ => None()
              }
            case ti: TypeInfo.Sig =>
              ti.methods.get(e.id) match {
                case io@Some(info) if shouldUnfold(info) => io
                case _ => None()
              }
            case info: TypeInfo.SubZ if config.fieldAccess =>
              val r: AST.CoreExp.Base = e.id match {
                case "Name" => AST.CoreExp.LitString(st"${(rt.ids, ".")}".render)
                case "isBitVector" => AST.CoreExp.LitB(info.ast.isBitVector)
                case "hasMin" => AST.CoreExp.LitB(info.ast.hasMin)
                case "hasMax" => AST.CoreExp.LitB(info.ast.hasMax)
                case "BitWidth" if info.ast.isBitVector => AST.CoreExp.LitZ(info.ast.bitWidth)
                case "Min" if info.ast.hasMin => AST.CoreExp.LitZ(info.ast.min)
                case "Max" if info.ast.hasMax => AST.CoreExp.LitZ(info.ast.max)
                case "isIndex" => AST.CoreExp.LitB(info.ast.isIndex)
                case "Index" => AST.CoreExp.LitZ(info.ast.index)
                case "isSigned" => AST.CoreExp.LitB(info.ast.isSigned)
                case "isZeroIndex" => AST.CoreExp.LitB(info.ast.isZeroIndex)
                case _ => halt(s"Infeasible: ${e.id}")
              }
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"field access ${equivST(AST.CoreExp.Select(receiver, e.id, r.tipe), r)}", e, r)
              }
              return Some(r)
            case info: TypeInfo.Enum if config.fieldAccess => halt("TODO")
            case _ => None()
          }
        case _ => None()
      }
      infoOpt match {
        case Some(info) =>
          unfold(info, Some(receiver)) match {
            case fApp@AST.CoreExp.Apply(f: AST.CoreExp.Fun, args, t) =>
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"unfolding", e(exp = receiver), fApp)
              }
              applyFun(f, args, t) match {
                case Some((r, _)) => return Some(r)
                case _ =>
              }
            case _ =>
          }
          halt("Infeasible")
        case _ =>
      }
      if (config.fieldAccess) {
        receiver match {
          case receiver: AST.CoreExp.Update =>
            if (receiver.id == e.id) {
              val r = receiver.arg
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"field access ${equivST(AST.CoreExp.Select(receiver, e.id, r.tipe), r)}", e, r)
              }
              return Some(r)
            } else {
              val r = e(exp = receiver.exp)
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"field access ${equivST(AST.CoreExp.Select(receiver, e.id, r.tipe), r)}", e, r)
              }
              return Some(r)
            }
          case receiver: AST.CoreExp.IndexingUpdate =>
            val r = e(exp = receiver.exp)
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"field access ${equivST(AST.CoreExp.Select(receiver, e.id, r.tipe), r)}", e, r)
            }
            return Some(r)
          case receiver: AST.CoreExp.Constructor =>
            val rt = receiver.tipe.asInstanceOf[AST.Typed.Name]
            if (e.id == "size" && (rt.ids == AST.Typed.isName || rt.ids == AST.Typed.msName)) {
              val r = AST.CoreExp.LitZ(receiver.args.size)
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"size access ${equivST(AST.CoreExp.Select(receiver, e.id, r.tipe), r)}", e, r)
              }
              return Some(r)
            } else {
              val info = th.typeMap.get(rt.ids).get.asInstanceOf[TypeInfo.Adt]
              val paramIndexMap = HashMap.empty[String, Z] ++ (for (i <- 0 until info.ast.params.size) yield
                (info.ast.params(i).id.value, i))
              paramIndexMap.get(e.id) match {
                case Some(i) =>
                  val r = receiver.args(i)
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"field access ${equivST(AST.CoreExp.Select(receiver, e.id, r.tipe), r)}", e, r)
                  }
                  return Some(r)
                case _ =>
              }
            }
          case _ =>
        }
      }
      return if (changed) Some(e(exp = receiver)) else None()
    }

    def evalUpdate(e: AST.CoreExp.Update): Option[AST.CoreExp.Base] = {
      var changed = F
      val receiver: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(exp2) =>
          changed = T
          exp2
        case _ => e.exp
      }
      val arg: AST.CoreExp.Base = evalBaseH(e.arg) match {
        case Some(arg2) =>
          changed = T
          arg2
        case _ => e.arg
      }
      if (receiver.isHalt || arg.isHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(exp = receiver, arg = arg).prettyST}", e, r)
        }
        return Some(r)
      }
      if (config.fieldAccess) {
        receiver match {
          case receiver: AST.CoreExp.Update if receiver.id == e.id =>
            val r = e(exp = receiver.exp, arg = arg)
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"field update ${equivST(AST.CoreExp.Update(receiver, e.id, arg, r.tipe), r)}", e, r)
            }
            return Some(r)
          case _ =>
        }
      }
      return if (changed) Some(e(exp = receiver, arg = arg)) else None()
    }

    def evalIndexing(e: AST.CoreExp.Indexing): Option[AST.CoreExp.Base] = {
      var changed = F
      val receiver: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(exp2) =>
          changed = T
          exp2
        case _ => e.exp
      }
      val index: AST.CoreExp.Base = evalBaseH(e.index) match {
        case Some(index2) =>
          changed = T
          index2
        case _ => e.index
      }
      if (receiver.isHalt || index.isHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(exp = receiver, index = index).prettyST}", e, r)
        }
        return Some(r)
      }
      if (config.seqIndexing) {
        receiver match {
          case receiver: AST.CoreExp.IndexingUpdate =>
            if (index == receiver.index) {
              val r = receiver.arg
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"indexing ${equivST(AST.CoreExp.Indexing(receiver, index, r.tipe), r)}", e, r)
              }
              return Some(r)
            }

            provenClaims.get(equiv(index, receiver.index)) match {
              case Some(stepId) =>
                val r = receiver.arg
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"indexing with $stepId (${equivST(index, receiver.index)}) ${equivST(AST.CoreExp.Indexing(receiver, index, r.tipe), r)}", e, r)
                }
                return Some(r)
              case _ =>
            }

            provenClaims.get(inequiv(index, receiver.index)) match {
              case Some(stepId) =>
                val r = e(exp = receiver.exp, index = index)
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"indexing with $stepId (${inequivST(index, receiver.index)}) ${equivST(AST.CoreExp.Indexing(receiver, index, r.tipe), r)}", e, r)
                }
                return Some(r)
              case _ =>
            }
          case _ =>
        }
      }
      return if (changed) Some(e(exp = receiver, index = index)) else None()
    }

    def evalIndexingUpdate(e: AST.CoreExp.IndexingUpdate): Option[AST.CoreExp.Base] = {
      var changed = F
      val receiver: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(exp2) =>
          changed = T
          exp2
        case _ => e.exp
      }
      val index: AST.CoreExp.Base = evalBaseH(e.index) match {
        case Some(index2) =>
          changed = T
          index2
        case _ => e.index
      }
      val arg: AST.CoreExp.Base = evalBaseH(e.arg) match {
        case Some(arg2) =>
          changed = T
          arg2
        case _ => e.arg
      }
      if (receiver.isHalt || index.isHalt || arg.isHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(exp = receiver, index = index, arg = arg).prettyST}", e, r)
        }
        return Some(r)
      }
      if (config.seqIndexing) {
        receiver match {
          case receiver: AST.CoreExp.IndexingUpdate =>
            if (index == receiver.index) {
              val r = e(exp = receiver.exp, index = index, arg = arg)
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"indexing update ${equivST(AST.CoreExp.IndexingUpdate(receiver, index, arg, r.tipe), r)}", e, r)
              }
              return Some(r)
            }
            provenClaims.get(equiv(index, receiver.index)) match {
              case Some(stepId) =>
                val r = e(exp = receiver.exp, index = index, arg = arg)
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"indexing with $stepId (${equivST(index, receiver.index)}) ${equivST(AST.CoreExp.IndexingUpdate(receiver, index, arg, r.tipe), r)}", e, r)
                }
                return Some(r)
              case _ =>
            }
          case _ =>
        }
      }
      return if (changed) Some(e(exp = receiver, index = index, arg = arg)) else None()
    }

    def evalConstructor(e: AST.CoreExp.Constructor): Option[AST.CoreExp.Base] = {
      var changed = F
      var args = ISZ[AST.CoreExp.Base]()
      var hasHalt = F
      for (arg <- e.args) {
        evalBaseH(arg) match {
          case Some(arg2) =>
            if (arg2.isHalt) {
              hasHalt = T
            }
            args = args :+ arg2
            changed = T
          case _ =>
            args = args :+ arg
        }
      }
      if (hasHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(args = args).prettyST}", e, r)
        }
        return Some(r)
      }
      return if (changed) Some(e(args = args)) else None()
    }

    def evalIf(e: AST.CoreExp.If): Option[AST.CoreExp.Base] = {
      var changed = F
      val cond: AST.CoreExp.Base = evalBaseH(e.cond) match {
        case Some(c@AST.CoreExp.LitB(b)) if config.constant =>
          val r: AST.CoreExp.Base = if (b) e.tExp else e.fExp
          if (shouldTrace) {
            trace = trace :+ Trace.Eval(st"constant condition ${equivST(e.cond, c)}", e, r)
          }
          return Some(r)
        case Some(c) =>
          changed = T
          c
        case _ => e.cond
      }
      if (cond.isHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(cond = cond).prettyST}", e, r)
        }
        return Some(r)
      }
      return if (changed) Some(e(cond = cond)) else None()
    }

    def evalApply(e: AST.CoreExp.Apply): Option[AST.CoreExp.Base] = {
      var op = e.exp
      var changed = F
      var hasHalt = F
      evalBaseH(e.exp) match {
        case Some(o) =>
          if (o.isHalt) {
            hasHalt = T
          }
          op = o
          changed = T
        case _ =>
      }
      var args = ISZ[AST.CoreExp.Base]()
      for (arg <- e.args) {
        evalBaseH(arg) match {
          case Some(arg2) =>
            if (arg2.isHalt) {
              hasHalt = T
            }
            args = args :+ arg2
            changed = T
          case _ =>
            if (arg.isHalt) {
              hasHalt = T
            }
            args = args :+ arg
        }
      }
      if (hasHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(exp = op, args = args).prettyST}", e, r)
        }
        return Some(r)
      }
      op match {
        case f: AST.CoreExp.Fun if config.funApplication =>
          applyFun(f, args, e.tipe) match {
            case Some((r, paramsSize)) =>
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"function application ${f.prettyST}(${(for (arg <- ops.ISZOps(args).slice(0, paramsSize)) yield arg.prettyST, ", ")}) ≡ ${r.prettyST}", e, r)
              }
              return Some(r)
            case _ =>
          }
        case q: AST.CoreExp.Quant if config.quantApplication && q.kind == AST.CoreExp.Quant.Kind.ForAll =>
          applyQuant(q, args, e.tipe) match {
            case Some((r, paramsSize)) =>
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"∀-elimination ${q.prettyST}(${(for (arg <- ops.ISZOps(args).slice(0, paramsSize)) yield arg.prettyST, ", ")}) ≡ ${r.prettyST}", e, r)
              }
              return Some(r)
            case _ =>
          }
        case _ =>
      }
      return if (changed) Some(e(exp = op, args = args)) else None()
    }

    def evalFun(e: AST.CoreExp.Fun): Option[AST.CoreExp.Base] = {
      var changed = F
      val body: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(b) =>
          changed = T
          b
        case _ => e.exp
      }
      return if (changed) Some(e(exp = body)) else None()
    }

    def evalQuant(e: AST.CoreExp.Quant): Option[AST.CoreExp.Base] = {
      var changed = F
      val body: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(b) =>
          changed = T
          b
        case _ => e.exp
      }
      return if (changed) Some(e(exp = body)) else None()
    }

    def evalInstanceOf(e: AST.CoreExp.InstanceOfExp): Option[AST.CoreExp.Base] = {
      var changed = F
      val receiver: AST.CoreExp.Base = evalBaseH(e.exp) match {
        case Some(r) =>
          changed = T
          r
        case _ => e.exp
      }
      if (receiver.isHalt) {
        val r = AST.CoreExp.Abort
        if (shouldTrace) {
          trace = trace :+ Trace.Eval(st"halted ${e(exp = receiver).prettyST}", e, r)
        }
        return Some(r)
      }
      if (config.instanceOf) {
        def checkSubtyping(): Option[AST.CoreExp.Base] = {
          val isSubType = th.isSubType(receiver.tipe, e.tipe)
          if (e.isTest) {
            val r: AST.CoreExp.Base = if (isSubType) {
              AST.CoreExp.True
            } else if (receiver.isInstanceOf[AST.CoreExp.Constructor]) {
              AST.CoreExp.False
            } else  {
              return None()
            }
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"type test ${receiver.prettyST}.isInstanceOf[${receiver.tipe}]", e, r)
            }
            return Some(r)
          } else {
            val r: AST.CoreExp.Base = if (isSubType) {
              receiver
            } else if (receiver.isInstanceOf[AST.CoreExp.Constructor]) {
              AST.CoreExp.Abort
            } else {
              return None()
            }
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"type test ${receiver.prettyST}.isInstanceOf[${receiver.tipe}]", e, r)
            }
            return Some(r)
          }
        }
        val r = checkSubtyping()
        if (r.nonEmpty) {
          return r
        }
      }
      return if (changed) Some(e(exp = receiver)) else None()
    }

    def evalLabeled(e: AST.CoreExp.Labeled): Option[AST.CoreExp.Base] = {
      evalBaseH(e.exp) match {
        case Some(r) => return Some(if (removeLabels) r else e(exp = r))
        case _ => return if (removeLabels) Some(e.exp) else None()
      }
    }

    evalBaseH(exp) match {
      case Some(e) => return Some((e, trace))
      case _ => return None()
    }
  }

  @pure def toCondEquiv(th: TypeHierarchy, exp: AST.CoreExp): ISZ[AST.CoreExp] = {
    @pure def toEquiv(e: AST.CoreExp.Base): AST.CoreExp.Base = {
      e match {
        case AST.CoreExp.Binary(_, AST.Exp.BinaryOp.EquivUni, _, _) => return e
        case _ => return AST.CoreExp.Binary(e, AST.Exp.BinaryOp.EquivUni, AST.CoreExp.True, AST.Typed.b)
      }
    }
    @pure def toCondEquivH(e: AST.CoreExp.Base): ISZ[AST.CoreExp] = {
      e match {
        case e: AST.CoreExp.Unary if e.op == AST.Exp.UnaryOp.Not =>
          return ISZ(AST.CoreExp.Binary(e.exp, AST.Exp.BinaryOp.EquivUni, AST.CoreExp.False, AST.Typed.b))
        case e: AST.CoreExp.Binary =>
          e.op match {
            case AST.Exp.BinaryOp.EquivUni => return ISZ(e)
            case AST.Exp.BinaryOp.Imply =>
              return for (r <- toCondEquivH(e.right)) yield AST.CoreExp.Arrow(e.left, r)
            case AST.Exp.BinaryOp.And =>
              return toCondEquivH(e.left) ++ toCondEquivH(e.right)
            case _ => return ISZ(toEquiv(e))
          }
        case e: AST.CoreExp.Quant if e.kind == AST.CoreExp.Quant.Kind.ForAll =>
          return toCondEquivH(applyQuant(e, ISZ(AST.CoreExp.LocalVarRef(T, ISZ(), paramId(e.param.id), e.param.tipe)),
            AST.Typed.b).get._1)
        case e: AST.CoreExp.If =>
          return (for (t <- toCondEquivH(e.tExp)) yield AST.CoreExp.Arrow(e.cond, t).asInstanceOf[AST.CoreExp]) ++
            (for (f <- toCondEquivH(e.fExp)) yield AST.CoreExp.Arrow(e.cond, f).asInstanceOf[AST.CoreExp])
        case e => return ISZ(toEquiv(e))
      }
    }
    @pure def rec(e: AST.CoreExp): ISZ[AST.CoreExp] = {
      e match {
        case AST.CoreExp.Arrow(left, right) => return for (r <- rec(right)) yield AST.CoreExp.Arrow(left, r)
        case e: AST.CoreExp.Base => return toCondEquivH(e)
      }
    }
    return rec(exp)
  }

  def methodPatternOf(th: TypeHierarchy, cache: Logika.Cache, info: Info.Method): Rewriter.Pattern.Method = {
    assert(info.ast.isStrictPure && !info.ast.hasContract)
    cache.getPatterns(th, info.isInObject, info.name) match {
      case Some(ISZ(r: Rewriter.Pattern.Method)) => return r
      case rOpt => assert(rOpt.isEmpty)
    }
    val (mi, body): (Info.Method, AST.CoreExp.Base) = if (info.ast.bodyOpt.nonEmpty && info.isInObject) {
      (info, translateAssignExp(th, F, Util.extractAssignExpOpt(info).get))
    } else {
      val id = info.ast.sig.id.value
      def findDefault(name: ISZ[String], defaultOpt: MBox[Option[(Info.Method, AST.CoreExp.Base)]]): Unit = {
        def mTranslate(minfo: Info.Method): Unit = {
          if (minfo.ast.bodyOpt.isEmpty) {
            return
          }
          Util.extractAssignExpOpt(minfo) match {
            case Some(ae) => defaultOpt.value = Some((minfo, translateAssignExp(th, F, ae)))
            case _ =>
          }
        }
        th.typeMap.get(name).get match {
          case ti: TypeInfo.Sig =>
            ti.methods.get(id) match {
              case Some(minfo) => mTranslate(minfo)
              case _ =>
            }
          case ti: TypeInfo.Adt =>
            ti.methods.get(id) match {
              case Some(minfo) => mTranslate(minfo)
              case _ =>
            }
          case _ =>
        }
        if (defaultOpt.value.nonEmpty) {
          return
        }
        val parents = th.poset.parentsOf(name).elements
        var i = 0
        while (defaultOpt.value.isEmpty && i < parents.size) {
          findDefault(parents(i), defaultOpt)
          i = i + 1
        }
      }
      val descendants = th.poset.descendantsOf(info.owner).elements
      if (descendants.isEmpty) {
        val mdo = MBox(Option.none[(Info.Method, AST.CoreExp.Base)]())
        findDefault(info.owner, mdo)
        val p = (info, AST.CoreExp.Abort.asInstanceOf[AST.CoreExp.Base])
        mdo.value.getOrElse(p)
      } else {
        var leaves = ISZ[ISZ[String]]()
        for (descendant <- descendants if th.poset.childrenOf(descendant).isEmpty) {
          leaves = leaves :+ descendant
        }
        var allLeavesNoImpl = T
        for (leaf <- leaves if allLeavesNoImpl) {
          th.typeMap.get(leaf).get match {
            case ti: TypeInfo.Sig => ti.methods.get(id) match {
              case Some(minfo) if minfo.ast.bodyOpt.nonEmpty => allLeavesNoImpl = F
              case _ =>
            }
            case ti: TypeInfo.Adt => ti.methods.get(id) match {
              case Some(minfo) if minfo.ast.bodyOpt.nonEmpty => allLeavesNoImpl = F
              case _ =>
            }
            case _ =>
          }
        }
        if (allLeavesNoImpl) {
          val mdo = MBox(Option.none[(Info.Method, AST.CoreExp.Base)]())
          findDefault(info.owner, mdo)
          val p = (info, AST.CoreExp.Abort.asInstanceOf[AST.CoreExp.Base])
          mdo.value.getOrElse(p)
        } else {
          halt("TODO")
        }
      }
    }
    var params = ISZ[(String, AST.Typed)]()
    if (!info.isInObject) {
      params = params :+ ("this", th.typeMap.get(mi.owner).get.tpe)
    }
    for (p <- info.ast.sig.params) {
      params = params :+ (p.id.value, p.tipe.typedOpt.get)
    }
    val r = Rewriter.Pattern.Method(mi.ast.purity == AST.Purity.Abs, mi.isInObject,
      mi.owner, mi.ast.sig.id.value, params, body)
    cache.setPatterns(th, info.isInObject, info.name, ISZ(r))
    if (info.name != mi.name) {
      cache.setPatterns(th, mi.isInObject, mi.name, ISZ(r))
    }
    return r
  }

  def patternsOf(th: TypeHierarchy, cache: Logika.Cache, isInObject: B, name: ISZ[String], rightToLeft: B,
                 seen: HashSet[ISZ[String]]): ISZ[Rewriter.Pattern] = {
    if (seen.contains(name)) {
      return ISZ()
    }
    cache.getPatterns(th, isInObject, name) match {
      case Some(r) => return if (rightToLeft) for (e <- r) yield e.toRightToLeft else r
      case _ =>
    }
    def patternsOfH(): ISZ[Rewriter.Pattern] = {
      val minfo: Info.Method = if (isInObject) {
        th.nameMap.get(name).get match {
          case info: Info.Theorem =>
            var localPatternSet: RewritingSystem.LocalPatternSet = HashSSet.empty
            val claim: AST.CoreExp = info.ast.claim match {
              case AST.Exp.QuantType(true, AST.Exp.Fun(_, params, AST.Stmt.Expr(c))) =>
                for (p <- params) {
                  localPatternSet = localPatternSet + (info.name, p.idOpt.get.value)
                }
                RewritingSystem.translateExp(th, T, c)
              case c => RewritingSystem.translateExp(th, T, c)
            }
            return for (c <- RewritingSystem.toCondEquiv(th, claim)) yield
              Rewriter.Pattern.Claim(T, name, F, isPermutative(c), localPatternSet, c)
          case info: Info.Fact =>
            var localPatternSet: RewritingSystem.LocalPatternSet = HashSSet.empty
            var r = ISZ[Rewriter.Pattern]()
            for (factClaim <- info.ast.claims) {
              val claim: AST.CoreExp = factClaim match {
                case AST.Exp.QuantType(true, AST.Exp.Fun(_, params, AST.Stmt.Expr(c))) =>
                  for (p <- params) {
                    localPatternSet = localPatternSet + (info.name, p.idOpt.get.value)
                  }
                  RewritingSystem.translateExp(th, T, c)
                case c => RewritingSystem.translateExp(th, T, c)
              }
              for (c <- RewritingSystem.toCondEquiv(th, claim)) {
                r = r :+ Rewriter.Pattern.Claim(T, name, F, isPermutative(c), localPatternSet, c)
              }
            }
            return r
          case info: Info.RsVal => return retrievePatterns(th, cache, info.ast.init, seen + name)
          case info: Info.Method => info
          case _ => halt("Infeasible")
        }
      } else {
        val id = name(name.size - 1)
        th.typeMap.get(ops.ISZOps(name).dropRight(1)).get match {
          case ti: TypeInfo.Sig => ti.methods.get(id).get
          case ti: TypeInfo.Adt => ti.methods.get(id).get
          case _ => halt("Infeasible")
        }
      }
      var r = ISZ[Rewriter.Pattern]()
      if (minfo.ast.hasContract) {
        val context = minfo.name
        var localPatternSet = HashSSet.empty[(ISZ[String], String)]
        if (!isInObject) {
          localPatternSet = localPatternSet + (minfo.name, "this")
        }
        for (p <- minfo.ast.sig.params) {
          localPatternSet = localPatternSet + (context, p.id.value)
        }

        def addContract(title: String, requires: ISZ[AST.Exp], ensures: ISZ[AST.Exp]): Unit = {
          var exp: AST.CoreExp = if (ensures.isEmpty) {
            AST.CoreExp.True
          } else {
            var ensure: AST.CoreExp.Base = translateExp(th, T, ensures(0))
            for (i <- 1 until ensures.size) {
              ensure = AST.CoreExp.Binary(ensure, AST.Exp.BinaryOp.And, translateExp(th, T, ensures(i)), AST.Typed.b)
            }
            ensure
          }
          for (i <- requires.size - 1 to 0 by -1) {
            exp = AST.CoreExp.Arrow(translateExp(th, T, requires(i)), exp)
          }
          for (e <- toCondEquiv(th, exp)) {
            r = r :+ Rewriter.Pattern.Claim(minfo.isInObject, minfo.name :+ title, F, isPermutative(exp), localPatternSet, e)
          }
        }

        minfo.ast.contract match {
          case c: AST.MethodContract.Simple => addContract("contract", c.requires, c.ensures)
          case c: AST.MethodContract.Cases =>
            for (i <- 0 until c.cases.size) {
              val cas = c.cases(i)
              var label = cas.label.value
              if (label == "") {
                label = s"contract.case.$i"
              } else {
                label = s"contract.case.$label"
              }
              addContract(label, cas.requires, cas.ensures)
            }
        }
      } else {
        r = r :+ methodPatternOf(th, cache, minfo)
      }
      return r
    }
    val r = patternsOfH()
    cache.setPatterns(th, isInObject, name, r)
    return if (rightToLeft) for (e <- r) yield e.toRightToLeft else r
  }

  def retrievePatterns(th: TypeHierarchy, cache: Logika.Cache, exp: AST.Exp, seen: HashSet[ISZ[String]]): ISZ[Rewriter.Pattern] = {
    def rec(rightToLeft: B, e: AST.Exp): HashSMap[ISZ[String], ISZ[Rewriter.Pattern]] = {
      var r = HashSMap.empty[ISZ[String], ISZ[Rewriter.Pattern]]
      e match {
        case e: AST.Exp.Ref =>
          e.resOpt.get match {
            case res: AST.ResolvedInfo.Theorem =>
              return r + res.name ~> patternsOf(th, cache, T, res.name, rightToLeft, seen)
            case res: AST.ResolvedInfo.Fact =>
              return r + res.name ~> patternsOf(th, cache, T, res.name, rightToLeft, seen)
            case res: AST.ResolvedInfo.Method =>
              val name = res.owner :+ res.id
              return r + name ~> patternsOf(th, cache, res.isInObject, name, rightToLeft, seen)
            case res: AST.ResolvedInfo.Var =>
              val name = res.owner :+ res.id
              return r + name ~> patternsOf(th, cache, T, name, rightToLeft, seen)
            case _ => halt("Infeasible")
          }
        case e: AST.Exp.Binary =>
          r = rec(rightToLeft, e.left)
          if (e.op == "++") {
            r = r ++ rec(rightToLeft, e.right).entries
          } else {
            r = r -- rec(rightToLeft, e.right).keys
          }
          return r
        case e: AST.Exp.RS =>
          for (ref <- e.refs) {
            r = r ++ rec(e.rightToLeft, ref.asExp).entries
          }
          return r
        case _ => halt("Infeasible")
      }
    }
    var r = ISZ[Rewriter.Pattern]()
    for (patterns <- rec(F, exp).values) {
      r = r ++ patterns
    }
    return r
  }

  @tailrec @pure def isPermutative(exp: AST.CoreExp): B = {
    exp match {
      case exp: AST.CoreExp.Arrow => return isPermutative(exp.right)
      case exp: AST.CoreExp.Binary if exp.isEquiv =>
        val numMap = MBox(HashMap.empty[(ISZ[String], String), Z])
        return exp.left.numberPattern(numMap) == exp.right.numberPattern(numMap)
      case _ => return F
    }
  }

  @strictpure def negBinaryOp(op: String): String = op match {
    case AST.Exp.BinaryOp.EquivUni => AST.Exp.BinaryOp.InequivUni
    case AST.Exp.BinaryOp.InequivUni => AST.Exp.BinaryOp.EquivUni
    case AST.Exp.BinaryOp.Lt => AST.Exp.BinaryOp.Ge
    case AST.Exp.BinaryOp.Le => AST.Exp.BinaryOp.Gt
    case AST.Exp.BinaryOp.Gt => AST.Exp.BinaryOp.Le
    case AST.Exp.BinaryOp.Ge => AST.Exp.BinaryOp.Ge
    case AST.Exp.BinaryOp.FpEq => AST.Exp.BinaryOp.FpNe
    case AST.Exp.BinaryOp.FpNe => AST.Exp.BinaryOp.FpEq
    case _ => op
  }
}
