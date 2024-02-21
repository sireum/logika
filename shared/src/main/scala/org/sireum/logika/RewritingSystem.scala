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
                             val equivSubst: B)

  object EvalConfig {
    val all: EvalConfig = EvalConfig(T, T, T, T, T, T, T, T, T, T)
    val none: EvalConfig = EvalConfig(F, F, F, F, F, F, F, F, F, F)
    val funApplicationOnly: EvalConfig = none(funApplication = T)
    val quantApplicationOnly: EvalConfig = none(quantApplication = T)
    val allButEquivSubst: EvalConfig = all(equivSubst = F)
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

  @datatype trait Trace {
    @pure def toST: ST
  }

  object Trace {
    @datatype class Begin(val title: String, val exp: AST.CoreExp.Base) extends Trace {
      @strictpure def toST: ST =
        st"""Begin $title ${exp.prettyST} ..."""
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
                         val shouldTrace: B,
                         val shouldTraceEval: B,
                         var done: B,
                         var trace: ISZ[Trace]) {
    val unfoldingMap: MBox[UnfoldingNumMap] = MBox(HashSMap.empty)
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
        claim match {
          case claim: AST.CoreExp.Binary =>
            claim.op match {
              case AST.Exp.BinaryOp.Lt =>
                r = r + claim ~> stepId
                r = r + claim(left = claim.right, op = AST.Exp.BinaryOp.Gt, right = claim.left) ~> stepId
                if (claim.right < claim.left) {
                  r = r + claim(left = claim.right, op = AST.Exp.BinaryOp.InequivUni, right = claim.left) ~> stepId
                } else {
                  r = r + claim(op = AST.Exp.BinaryOp.InequivUni) ~> stepId
                }
              case AST.Exp.BinaryOp.Le =>
                r = r + claim ~> stepId
                r = r + claim(left = claim.right, op = AST.Exp.BinaryOp.Ge, right = claim.left) ~> stepId
              case AST.Exp.BinaryOp.Gt =>
                r = r + claim ~> stepId
                r = r + claim(left = claim.right, op = AST.Exp.BinaryOp.Lt, right = claim.left) ~> stepId
                if (claim.right < claim.left) {
                  r = r + claim(left = claim.right, op = AST.Exp.BinaryOp.InequivUni, right = claim.left) ~> stepId
                } else {
                  r = r + claim(op = AST.Exp.BinaryOp.InequivUni) ~> stepId
                }
              case AST.Exp.BinaryOp.Ge =>
                r = r + claim ~> stepId
                r = r + claim(left = claim.right, op = AST.Exp.BinaryOp.Le, right = claim.left) ~> stepId
              case AST.Exp.BinaryOp.And =>
                r = r + claim ~> stepId
                for (c <- conjuncts(claim)) {
                  r = r + c ~> stepId
                }
              case _ =>
                if (claim.op == AST.Exp.BinaryOp.EquivUni || claim.op == AST.Exp.BinaryOp.InequivUni) {
                  if (claim.right < claim.left) {
                    r = r + claim(left = claim.right, right = claim.left) ~> stepId
                  } else {
                    r = r + claim ~> stepId
                  }
                } else {
                  r = r + claim ~> stepId
                }
            }
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
          case _: AST.CoreExp.ObjectVarRef => None()
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
        }
        rOpt
      }
      val hasChanged: B = r.nonEmpty
      val o2: AST.CoreExp.Base = r.getOrElse(o)
      val shouldUnfold: B = o2 match {
        case o2: AST.CoreExp.ObjectVarRef if methodPatterns.contains((o2.owner :+ o2.id, F)) => T
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
      if (shouldUnfold) {
        evalBase(th, EvalConfig.none, cache, methodPatterns, unfoldingMap, 1, HashSMap.empty, o2, shouldTraceEval) match {
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
            case _ => halt("Infeasible")
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
                    Rewriter(maxCores, th, HashSMap.empty, patterns2, methodPatterns, F, F, F, ISZ()).
                      transformCoreExpBase(cache, o).getOrElse(o)
                  }
              }
            }
            val (o3Opt, t): (Option[AST.CoreExp.Base], ISZ[Trace]) =
              evalBase(th, EvalConfig.allButEquivSubst, cache, methodPatterns, unfoldingMap, 1,
                provenClaimStepIdMap, o2, shouldTraceEval) match {
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
                    r2l(Rewriter.Pattern.Claim(pattern.name :+ s"Assumption$k", F, isPermutative(apc), HashSSet.empty, apc))) ++
                    patterns
                val o2 = Rewriter(maxCores, th, HashSMap.empty, patterns2, methodPatterns, F, F, F, ISZ()).
                  transformCoreExpBase(cache, o).getOrElse(o)
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
    }

    object Pattern {

      @datatype class Claim(val name: ISZ[String],
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
      for (i <- 0 until stmts.size - 2) {
        m = translateStmt(stmts(i), funStack, m)._2
      }
      return translateAssignExp(stmts(stmts.size - 1).asAssignExp, funStack, m)
    }
    @pure def translateStmt(stmt: AST.Stmt, funStack: FunStack, localMap: LocalMap): (Option[AST.CoreExp.Base], LocalMap) = {
      stmt match {
        case stmt: AST.Stmt.Expr => return (Some(translateExp(stmt.exp, funStack, localMap)), localMap)
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
        case stmt: AST.Stmt.VarPattern => halt(s"TODO: $stmt")
        case stmt: AST.Stmt.Match => halt(s"TODO: $stmt")
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
              return AST.CoreExp.LocalVarRef(isPattern, res.context, id, e.typedOpt.get)
            case res: AST.ResolvedInfo.Var if res.isInObject =>
              if (res.owner == AST.Typed.sireumName) {
                res.id match {
                  case "T" => return AST.CoreExp.True
                  case "F" => return AST.CoreExp.False
                  case _ =>
                }
              }
              return AST.CoreExp.ObjectVarRef(res.owner, res.id, e.typedOpt.get)
            case res: AST.ResolvedInfo.Method =>
              return AST.CoreExp.ObjectVarRef(res.owner, res.id, e.typedOpt.get)
            case _ => halt(s"Infeasible: $e")
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
            case _ => halt(s"TODO: $e")
          }
        case e: AST.Exp.Select =>
          e.receiverOpt match {
            case Some(receiver) => return AST.CoreExp.Select(translateExp(receiver, funStack, localMap), e.id.value, e.typedOpt.get)
            case _ => return translateExp(AST.Exp.Ident(e.id, e.attr), funStack, localMap)
          }
        case e: AST.Exp.If =>
          return AST.CoreExp.ite(translateExp(e.cond, funStack, localMap), translateExp(e.elseExp, funStack, localMap),
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
          val args: ISZ[AST.CoreExp.Base] = for (arg <- e.args) yield translateExp(arg, funStack, localMap)
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
            case _ =>
          }
          e.receiverOpt match {
            case Some(receiver) =>
              return AST.CoreExp.Apply(T, translateExp(e.ident, funStack, localMap),
                translateExp(receiver, funStack, localMap) +: args, e.typedOpt.get)
            case _ =>
              return AST.CoreExp.Apply(F, translateExp(e.ident, funStack, localMap),
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
              return AST.CoreExp.Apply(T, translateExp(e.ident, funStack, localMap),
                translateExp(receiver, funStack, localMap) +: getArgs, e.typedOpt.get)
            case _ => return AST.CoreExp.Apply(F, translateExp(e.ident, funStack, localMap),
              getArgs, e.typedOpt.get)
          }
        case e => halt(s"TODO: $e")
      }
    }
  }

  @record class NoCache extends Logika.Cache {

    override def clearTransition(): Unit = {}
    override def getTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, transition: Logika.Cache.Transition, state: State, smt2: Smt2): Option[(ISZ[State], U64)] = {
      return None()
    }
    override def setTransition(th: TypeHierarchy, config: Config, transition: Logika.Cache.Transition, state: State, nextStates: ISZ[State], smt2: Smt2): U64 = {
      return U64.fromZ(0)
    }

    override def getAssignExpTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, exp: AST.AssignExp, state: State, smt2: Smt2): Option[(ISZ[(State, State.Value)], U64)] = {
      return None()
    }

    override def setAssignExpTransition(th: TypeHierarchy, config: Config, exp: AST.AssignExp, state: State, nextStatesValues: ISZ[(State, State.Value)], smt2: Smt2): U64 = {
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
        case (p: AST.CoreExp.ObjectVarRef, e: AST.CoreExp.ObjectVarRef) =>
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
              if (p.hasReceiver != e.hasReceiver || p.args.size != e.args.size) {
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
          evalBase(th, EvalConfig.funApplicationOnly, noCache, HashSMap.empty, MBox(HashSMap.empty), 1, HashSMap.empty,
            AST.CoreExp.Apply(F, f, args, e.tipe), F) match {
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
        case lit1 => halt(st"TODO: ${lit1.prettyST} $op ${lit2.prettyST}".render)
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
      case lit => halt(st"TODO: $op ${lit.prettyST}".render)
    }

  @pure def eval(th: TypeHierarchy,
                 config: EvalConfig,
                 cache: Logika.Cache,
                 methodPatterns: MethodPatternMap,
                 unfoldingMap: MBox[UnfoldingNumMap],
                 maxUnfolding: Z,
                 provenClaims: HashSMap[AST.CoreExp.Base, AST.ProofAst.StepId],
                 exp: AST.CoreExp,
                 shouldTrace: B): Option[(AST.CoreExp, ISZ[Trace])] = {
    exp match {
      case exp: AST.CoreExp.Arrow =>
        var changed = F
        var trace = ISZ[Trace]()
        val left: AST.CoreExp.Base = evalBase(th, config, cache, methodPatterns, unfoldingMap, maxUnfolding,
          provenClaims, exp.left, shouldTrace) match {
          case Some((l, t)) =>
            trace = trace ++ t
            changed = T
            l
          case _ => exp.left
        }
        val right: AST.CoreExp = eval(th, config, cache, methodPatterns, unfoldingMap, maxUnfolding, provenClaims,
          exp.right, shouldTrace) match {
          case Some((r, t)) =>
            trace = trace ++ t
            changed = T
            r
          case _ => exp.right
        }
        return if (changed) Some((AST.CoreExp.Arrow(left, right), trace)) else None()
      case exp: AST.CoreExp.Base => evalBase(th, config, cache, methodPatterns, unfoldingMap, maxUnfolding,
        provenClaims, exp, shouldTrace) match {
        case Some((e, t)) => return Some((e, t))
        case _ => return None()
      }
    }
  }

  @pure def evalBase(th: TypeHierarchy,
                     config: EvalConfig,
                     cache: Logika.Cache,
                     methodPatterns: MethodPatternMap,
                     unfoldingMap: MBox[UnfoldingNumMap],
                     maxUnfolding: Z,
                     provenClaims: HashSMap[AST.CoreExp.Base, AST.ProofAst.StepId],
                     exp: AST.CoreExp.Base,
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
    @strictpure def incDeBruijnMap(deBruijnMap: HashMap[Z, AST.CoreExp.Base], inc: Z): HashMap[Z, AST.CoreExp.Base] =
      if (inc != 0) HashMap ++ (for (p <- deBruijnMap.entries) yield (p._1 + inc, p._2)) else deBruijnMap
    def shouldUnfold(info: Info.Method): B = {
      return !info.ast.hasContract && info.ast.isStrictPure &&
        ((info.ast.purity == AST.Purity.Abs) ->: methodPatterns.contains((info.name, info.isInObject)))
    }
    def unfold(info: Info.Method, receiverOpt: Option[AST.CoreExp.Base]): AST.CoreExp.Base = {
      val pattern = methodPatternOf(th, cache, info)
      val f = pattern.toFun
      receiverOpt match {
        case Some(receiver) => return AST.CoreExp.Apply(T, f, ISZ(receiver), f.exp.tipe)
        case _ => return f
      }
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
    var trace = ISZ[Trace]()
    def evalBaseH(deBruijnMap: HashMap[Z, AST.CoreExp.Base], e: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
      if (e.tipe == AST.Typed.b) {
        provenClaims.get(e) match {
          case Some(stepId) =>
            val r = AST.CoreExp.True
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"using $stepId", e, r)
            }
            return Some(r)
          case _ =>
        }
      }
      if (config.equivSubst) {
        val r = eqMap.get(e)
        r match {
          case Some((to, stepId)) =>
            if (shouldTrace) {
              trace = trace :+ Trace.Eval(st"substitution using $stepId [${to.prettyST}/${e.prettyST}]", e, to)
            }
            return Some(to)
          case _ =>
        }
      }
      return rec(deBruijnMap, e)
    }
    def rec(deBruijnMap: HashMap[Z, AST.CoreExp.Base], e: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
      e match {
        case _: AST.CoreExp.Lit => return None()
        case _: AST.CoreExp.LocalVarRef => return None()
        case e: AST.CoreExp.ParamVarRef =>
          deBruijnMap.get(e.deBruijn) match {
            case Some(e2) => return Some(evalBaseH(deBruijnMap, e2).getOrElse(e2))
            case _ => return None()
          }
        case e: AST.CoreExp.ObjectVarRef =>
          th.nameMap.get(e.owner :+ e.id) match {
            case Some(info: Info.Method) if shouldUnfold(info) =>
              val r = unfold(info, None())
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"unfolding", e, r)
              }
              return Some(r)
            case _ =>
          }
          return None()
        case e: AST.CoreExp.Binary =>
          var changed = F
          val left: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.left) match {
            case Some(l) =>
              changed = T
              l
            case _ => e.left
          }
          val right: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.right) match {
            case Some(r) =>
              changed = T
              r
            case _ => e.right
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
              provenClaims.get(e.left) match {
                case Some(leftStepId) => provenClaims.get(e.right) match {
                  case Some(rightStepId) =>
                    val r = AST.CoreExp.True
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"& using $leftStepId and $rightStepId", e, r)
                    }
                    return Some(r)
                  case _ =>
                }
                case _ =>
              }
            case AST.Exp.BinaryOp.Or =>
              provenClaims.get(e.left) match {
                case Some(leftStepId) =>
                  val r = AST.CoreExp.True
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"| using $leftStepId", e, r)
                  }
                  return Some(r)
                case _ =>
              }
              provenClaims.get(e.right) match {
                case Some(rightStepId) =>
                  val r = AST.CoreExp.True
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"| using $rightStepId", e, r)
                  }
                  return Some(r)
                case _ =>
              }
            case AST.Exp.BinaryOp.Imply =>
              provenClaims.get(AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, e.left)) match {
                case Some(leftStepId) =>
                  val r = AST.CoreExp.True
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"__>: using $leftStepId", e, r)
                  }
                  return Some(r)
                case _ =>
              }
              provenClaims.get(e.right) match {
                case Some(rightStepId) =>
                  val r = AST.CoreExp.True
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"__>: using $rightStepId", e, r)
                  }
                  return Some(r)
                case _ =>
              }
            case AST.Exp.BinaryOp.Xor =>
              provenClaims.get(left) match {
                case Some(leftStepId) => provenClaims.get(AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, right)) match {
                  case Some(rightStepId) =>
                    val r = AST.CoreExp.True
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"|^ using $leftStepId and $rightStepId", e, r)
                    }
                    return Some(r)
                  case _ =>
                }
                case _ =>
              }
              provenClaims.get(AST.CoreExp.Unary(AST.Exp.UnaryOp.Not, left)) match {
                case Some(leftStepId) => provenClaims.get(right) match {
                  case Some(rightStepId) =>
                    val r = AST.CoreExp.True
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"|^ using $leftStepId and $rightStepId", e, r)
                    }
                    return Some(r)
                  case _ =>
                }
                case _ =>
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
                rOpt = Some(AST.CoreExp.Unary(AST.Exp.UnaryOp.Minus , left))
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
            var eq = F
            var stepIdOpt = Option.none[ST]()
            if (left == right) {
              eq = T
            } else {
              provenClaims.get(equiv(left, right)) match {
                case Some(stepId) =>
                  stepIdOpt = Some(st" ($stepId)")
                  eq = T
                case _ =>
              }
            }
            if (eq) {
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
                    trace = trace :+ Trace.Eval(st"equivalence$stepIdOpt ${equivST(left, right)}", e, r)
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
                  case AST.Exp.BinaryOp.Eq => Some(AST.CoreExp.False)
                  case AST.Exp.BinaryOp.Ne => Some(AST.CoreExp.True)
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
        case e: AST.CoreExp.Unary =>
          var changed = F
          val ue: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          if (config.constant) {
            ue match {
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
                val r = ue
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"unary ${equivST(AST.CoreExp.Unary(e.op, ue), r)}", e, r)
                }
                return Some(r)
              case _ =>
                ue match {
                  case ue: AST.CoreExp.Unary =>
                    if (e.op == ue.op) {
                      val r = ue.exp
                      if (shouldTrace) {
                        trace = trace :+ Trace.Eval(st"unary ${equivST(AST.CoreExp.Unary(e.op, ue), r)}", e, r)
                      }
                      return Some(r)
                    }
                  case _ =>
                }
            }
          }
          val r = e(exp = ue)
          return if (changed) Some(r) else None()
        case e: AST.CoreExp.Select =>
          var changed = F
          val receiver: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
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
              val fApp = unfold(info, Some(receiver))
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"unfolding", e(exp = receiver), fApp)
              }
              val p = evalBase(th, EvalConfig.funApplicationOnly, cache, HashSMap.empty,
                MBox(HashSMap.empty), 1, HashSMap.empty, fApp, shouldTrace).get
              trace = trace ++ p._2
              return Some(p._1)
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
                  return Some(evalBaseH(deBruijnMap, r).getOrElse(r))
                }
              case receiver: AST.CoreExp.IndexingUpdate =>
                val r = e(exp = receiver.exp)
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"field access ${equivST(AST.CoreExp.Select(receiver, e.id, r.tipe), r)}", e, r)
                }
                return Some(evalBaseH(deBruijnMap, r).getOrElse(r))
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
        case e: AST.CoreExp.Update =>
          var changed = F
          val receiver: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          val arg: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.arg) match {
            case Some(arg2) =>
              changed = T
              arg2
            case _ => e.arg
          }
          if (config.fieldAccess) {
            receiver match {
              case receiver: AST.CoreExp.Update if receiver.id == e.id =>
                val r = e(exp = receiver.exp, arg = arg)
                if (shouldTrace) {
                  trace = trace :+ Trace.Eval(st"field update ${equivST(AST.CoreExp.Update(receiver, e.id, arg, r.tipe), r)}", e, r)
                }
                return Some(evalBaseH(deBruijnMap, r).getOrElse(r))
              case _ =>
            }
          }
          return if (changed) Some(e(exp = receiver, arg = arg)) else None()
        case e: AST.CoreExp.Indexing =>
          var changed = F
          val receiver: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          val index: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.index) match {
            case Some(index2) =>
              changed = T
              index2
            case _ => e.index
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
                    return Some(evalBaseH(deBruijnMap,r).getOrElse(r))
                  case _ =>
                }
              case _ =>
            }
          }
          return if (changed) Some(e(exp = receiver, index = index)) else None()
        case e: AST.CoreExp.IndexingUpdate =>
          var changed = F
          val receiver: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          val index: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.index) match {
            case Some(index2) =>
              changed = T
              index2
            case _ => e.index
          }
          val arg: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.arg) match {
            case Some(arg2) =>
              changed = T
              arg2
            case _ => e.arg
          }
          if (config.seqIndexing) {
            receiver match {
              case receiver: AST.CoreExp.IndexingUpdate =>
                if (index == receiver.index) {
                  val r = e(exp = receiver.exp, index = index, arg = arg)
                  if (shouldTrace) {
                    trace = trace :+ Trace.Eval(st"indexing update ${equivST(AST.CoreExp.IndexingUpdate(receiver, index, arg, r.tipe), r)}", e, r)
                  }
                  return Some(evalBaseH(deBruijnMap, r).getOrElse(r))
                }
                provenClaims.get(equiv(index, receiver.index)) match {
                  case Some(stepId) =>
                    val r = e(exp = receiver.exp, index = index, arg = arg)
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"indexing with $stepId (${equivST(index, receiver.index)}) ${equivST(AST.CoreExp.IndexingUpdate(receiver, index, arg, r.tipe), r)}", e, r)
                    }
                    return Some(evalBaseH(deBruijnMap, r).getOrElse(r))
                  case _ =>
                }
              case _ =>
            }
          }
          return if (changed) Some(e(exp = receiver, index = index, arg = arg)) else None()
        case e: AST.CoreExp.Constructor =>
          var changed = F
          var args = ISZ[AST.CoreExp.Base]()
          for (arg <- e.args) {
            evalBaseH(deBruijnMap, arg) match {
              case Some(arg2) =>
                args = args :+ arg2
                changed = T
              case _ =>
                args = args :+ arg
            }
          }
          return if (changed) Some(e(args = args)) else None()
        case e: AST.CoreExp.If =>
          var changed = F
          val cond: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.cond) match {
            case Some(c@AST.CoreExp.LitB(b)) if config.constant =>
              val r: AST.CoreExp.Base = if (b) e.tExp else e.fExp
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"constant condition ${equivST(e.cond, c)}", e, r)
              }
              return Some(evalBaseH(deBruijnMap, r).getOrElse(r))
            case Some(c) =>
              changed = T
              c
            case _ => e.cond
          }
          return if (changed) Some(e(cond = cond)) else None()
        case e: AST.CoreExp.Apply =>
          var op = e.exp
          var changed = F
          evalBaseH(deBruijnMap, e.exp) match {
            case Some(o) =>
              op = o
              changed = T
            case _ =>
          }
          var args = ISZ[AST.CoreExp.Base]()
          for (arg <- e.args) {
            evalBaseH(deBruijnMap, arg) match {
              case Some(arg2) =>
                args = args :+ arg2
                changed = T
              case _ =>
                args = args :+ arg
            }
          }
          op match {
            case f: AST.CoreExp.Fun if config.funApplication =>
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
              var map = incDeBruijnMap(deBruijnMap, params.size)
              for (i <- 0 until params.size) {
                map = map + (params.size - i) ~> args(i)
              }
              evalBaseH(map, body) match {
                case Some(body2) =>
                  if (args.size > params.size) {
                    val r = e(exp = body2, args = ops.ISZOps(args).slice(params.size, args.size))
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"function application ${f.prettyST}(${(for (arg <- ops.ISZOps(args).slice(0, params.size)) yield arg.prettyST, ", ")}) ≡ ${r.prettyST}", e, r)
                    }
                    return Some(r)
                  } else {
                    val r = body2
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"function application ${f.prettyST}(${(for (arg <- args) yield arg.prettyST, ", ")}) ≡ ${r.prettyST}", e, r)
                    }
                    return Some(r)
                  }
                case _ =>
              }
            case q: AST.CoreExp.Quant if config.quantApplication && q.kind == AST.CoreExp.Quant.Kind.ForAll =>
              var params = ISZ[(String, AST.Typed)]()
              @tailrec def recParamsQuqnt(fe: AST.CoreExp.Base): AST.CoreExp.Base = {
                fe match {
                  case fe: AST.CoreExp.Quant if params.size < args.size =>
                    params = params :+ (fe.param.id, fe.param.tipe)
                    return recParamsQuqnt(fe.exp)
                  case _ => return fe
                }
              }
              val body = recParamsQuqnt(q)
              var map = incDeBruijnMap(deBruijnMap, params.size)
              for (i <- 0 until params.size) {
                map = map + (params.size - i) ~> args(i)
              }
              evalBaseH(map, body) match {
                case Some(body2) =>
                  if (args.size > params.size) {
                    val r = e(exp = body2, args = ops.ISZOps(args).slice(params.size, args.size))
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"∀-elimination ${q.prettyST}(${(for (arg <- ops.ISZOps(args).slice(0, params.size)) yield arg.prettyST, ", ")}) ≡ ${r.prettyST}", e, r)
                    }
                    return Some(r)
                  } else {
                    val r = body2
                    if (shouldTrace) {
                      trace = trace :+ Trace.Eval(st"∀-elimination ${q.prettyST}(${(for (arg <- args) yield arg.prettyST, ", ")}) ≡ ${r.prettyST}", e, r)
                    }
                    return Some(r)
                  }
                case _ =>
              }
            case _ =>
          }
          return if (changed) Some(e(exp = op, args = args)) else None()
        case e: AST.CoreExp.Fun =>
          var changed = F
          val body: AST.CoreExp.Base = evalBaseH(incDeBruijnMap(deBruijnMap, 1), e.exp) match {
            case Some(b) =>
              changed = T
              b
            case _ => e.exp
          }
          return if (changed) Some(e(exp = body)) else None()
        case e: AST.CoreExp.Quant =>
          var changed = F
          val body: AST.CoreExp.Base = evalBaseH(incDeBruijnMap(deBruijnMap, 1), e.exp) match {
            case Some(b) =>
              changed = T
              b
            case _ => e.exp
          }
          return if (changed) Some(e(exp = body)) else None()
        case e: AST.CoreExp.InstanceOfExp =>
          var changed = F
          val receiver: AST.CoreExp.Base = evalBaseH(deBruijnMap, e.exp) match {
            case Some(r) =>
              changed = T
              r
            case _ => e
          }
          if (config.instanceOf && th.isSubType(receiver.tipe, e.tipe)) {
            if (e.isTest) {
              val r = AST.CoreExp.True
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"type test ${receiver.prettyST}.isInstanceOf[${receiver.tipe}]", e, r)
              }
              return Some(r)
            } else {
              val r = receiver
              if (shouldTrace) {
                trace = trace :+ Trace.Eval(st"type test ${receiver.prettyST}.isInstanceOf[${receiver.tipe}]", e, r)
              }
              return Some(r)
            }
          }
          return if (changed) Some(e(exp = receiver)) else None()
      }
    }
    evalBaseH(HashMap.empty, exp) match {
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
          return toCondEquivH(evalBase(th, EvalConfig.quantApplicationOnly, noCache, HashSMap.empty,
            MBox(HashSMap.empty), 1, HashSMap.empty,
            AST.CoreExp.Apply(F, e,
              ISZ(AST.CoreExp.LocalVarRef(T, ISZ(), paramId(e.param.id), e.param.tipe)),
              AST.Typed.b), F).get._1)
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
    var params = ISZ[(String, AST.Typed)]()
    if (!info.isInObject) {
      params = params :+ ("this", th.typeMap.get(info.owner).get.tpe)
    }
    for (p <- info.ast.sig.params) {
      params = params :+ (p.id.value, p.tipe.typedOpt.get)
    }
    val r = Rewriter.Pattern.Method(info.ast.purity == AST.Purity.Abs, info.isInObject,
      info.owner, info.ast.sig.id.value, params,
      translateAssignExp(th, F, Util.extractAssignExpOpt(info).get))
    cache.setPatterns(th, info.isInObject, info.name, ISZ(r))
    return r
  }

  def patternsOf(th: TypeHierarchy, cache: Logika.Cache, name: ISZ[String], rightToLeft: B): ISZ[Rewriter.Pattern] = {
    cache.getPatterns(th, F, name) match {
      case Some(r) => return if (rightToLeft) for (e <- r) yield e.toRightToLeft else r
      case _ =>
    }
    var r = ISZ[Rewriter.Pattern]()
    cache.setPatterns(th, F, name, r)
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
        for (c <- RewritingSystem.toCondEquiv(th, claim)) {
          r = r :+ Rewriter.Pattern.Claim(name, F, isPermutative(c), localPatternSet, c)
        }
      case info: Info.Fact =>
        var localPatternSet: RewritingSystem.LocalPatternSet = HashSSet.empty
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
            r = r :+ Rewriter.Pattern.Claim(name, F, isPermutative(c), localPatternSet, c)
          }
        }
      case info: Info.RsVal => r = r ++ retrievePatterns(th, cache, info.ast.init)
      case info: Info.Method =>
        if (info.ast.hasContract) {
          val context = info.name
          val localPatternSet = HashSSet ++ (for (p <- info.ast.sig.params) yield (context, p.id.value))
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
            r = r :+ Rewriter.Pattern.Claim(info.name :+ title, F, isPermutative(exp), localPatternSet, exp)
          }
          info.ast.contract match {
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
          r = r :+ methodPatternOf(th, cache, info)
        }
      case _ => halt("Infeasible")
    }
    cache.setPatterns(th, F, name, r)
    return if (rightToLeft) for (e <- r) yield e.toRightToLeft else r
  }

  def retrievePatterns(th: TypeHierarchy, cache: Logika.Cache, exp: AST.Exp): ISZ[Rewriter.Pattern] = {
    def rec(rightToLeft: B, e: AST.Exp): HashSMap[ISZ[String], ISZ[Rewriter.Pattern]] = {
      var r = HashSMap.empty[ISZ[String], ISZ[Rewriter.Pattern]]
      e match {
        case e: AST.Exp.Ref =>
          e.resOpt.get match {
            case res: AST.ResolvedInfo.Theorem =>
              return r + res.name ~> patternsOf(th, cache, res.name, rightToLeft)
            case res: AST.ResolvedInfo.Fact =>
              return r + res.name ~> patternsOf(th, cache, res.name, rightToLeft)
            case res: AST.ResolvedInfo.Method =>
              val name = res.owner :+ res.id
              return r + name ~> patternsOf(th, cache, name, rightToLeft)
            case res: AST.ResolvedInfo.Var =>
              val name = res.owner :+ res.id
              return r + name ~> patternsOf(th, cache, name, rightToLeft)
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
}
