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
import org.sireum.lang.symbol.Info
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

  @datatype class EvalConfig(val constantPropagation: B,
                             val funApplication: B,
                             val quantApplication: B,
                             val equality: B,
                             val tupleProjection: B,
                             val seqIndexing: B,
                             val fieldAccess: B,
                             val instanceOf: B)

  object EvalConfig {
    val all: EvalConfig = EvalConfig(T, T, T, T, T, T, T, T)
    val none: EvalConfig = EvalConfig(F, F, F, F, F, F, F, F)
    val funApplicationOnly: EvalConfig = none(funApplication = T)
    val quantApplicationOnly: EvalConfig = none(quantApplication = T)
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

  @datatype class TraceElement(val name: ISZ[String],
                               val rightToLeft: B,
                               val pattern: AST.CoreExp,
                               val original: AST.CoreExp.Base,
                               val rewritten: AST.CoreExp.Base,
                               val evaluatedOpt: Option[AST.CoreExp.Base],
                               val done: AST.CoreExp.Base) {
    @strictpure def toST: ST = evaluatedOpt match {
      case Some(evaluated) =>
        st"""by ${(name, ".")}: ${pattern.prettyPatternST}
            |     ${original.prettyST}
            |   ${if (rightToLeft) "<" else ">"} ${rewritten.prettyST}
            |   ≡ ${evaluated.prettyST}
            |   ∴ ${done.prettyST}"""
      case _ =>
        st"""by ${(name, ".")}: ${pattern.prettyPatternST}
            |     ${original.prettyST}
            |   ${if (rightToLeft) "<" else ">"} ${rewritten.prettyST}
            |   ∴ ${done.prettyST}"""
    }
  }

  @record class Rewriter(val th: TypeHierarchy,
                         val provenClaims: HashSSet[AST.CoreExp.Base],
                         val rwPatterns: ISZ[Rewriter.Pattern],
                         val shouldTrace: B,
                         var trace: ISZ[TraceElement]) extends AST.MCoreExpTransformer {
    override def preCoreExpIf(o: AST.CoreExp.If): AST.MCoreExpTransformer.PreResult[AST.CoreExp.Base] = {
      o.cond match {
        case cond: AST.CoreExp.LitB => return AST.MCoreExpTransformer.PreResult(T, if (cond.value) MSome(o.tExp) else MSome(o.fExp))
        case _ => return AST.MCoreExpTransformer.PreResult(F, MNone())
      }
    }

    override def postCoreExpBase(o: AST.CoreExp.Base): MOption[AST.CoreExp.Base] = {
      var rOpt = MOption.none[AST.CoreExp.Base]()
      var i = 0
      var patterns = rwPatterns
      while (rOpt.isEmpty && i < patterns.size) {
        val pattern = patterns(i)
        var assumptions = ISZ[AST.CoreExp.Base]()
        def arrowRec(e: AST.CoreExp): AST.CoreExp = {
          e match {
            case e: AST.CoreExp.Arrow =>
              assumptions = assumptions :+ e.left
              return arrowRec(e.right)
            case _ => return e
          }
        }
        def tryPattern(): Unit = {
          val (from, to): (AST.CoreExp.Base, AST.CoreExp.Base) = arrowRec(pattern.exp) match {
            case AST.CoreExp.Binary(left, AST.Exp.BinaryOp.EquivUni, right) =>
              if (pattern.rightToLeft) (right, left) else (left, right)
            case _ => halt("Infeasible")
          }
          def last(m: UnificationMap): Unit = {
            val o2 = LocalSubstitutor(m).transformCoreExpBase(to).getOrElse(o)
            val o3Opt = evalBase(th, EvalConfig.all, o2)
            val o3 = o3Opt.getOrElse(o2)
            if (o == o3) {
              // skip
            } else if (pattern.isPermutative && o < o3) {
              // skip
            } else {
              if (shouldTrace) {
                trace = trace :+ TraceElement(pattern.name, pattern.rightToLeft, pattern.exp, o, o2, o3Opt, o3)
              }
              rOpt = MSome(o3)
            }
          }
          if (assumptions.isEmpty) {
            unify(T, th, pattern.localPatternSet, ISZ(from), ISZ(o)) match {
              case Either.Left(m) => last(m)
              case _ =>
            }
          } else {
            var done = F
            val pces = provenClaims.elements
            def recAssumption(pendingApplications: PendingApplications,
                              substMap: HashMap[String, AST.Typed],
                              apcs: ISZ[AST.CoreExp.Base],
                              map: UnificationMap,
                              j: Z): Unit = {
              if (j >= assumptions.size) {
                val ems: MBox[UnificationErrorMessages] = MBox(ISZ())
                val pas = MBox(pendingApplications)
                val sm = MBox(substMap)
                val m = unifyExp(T, th, pattern.localPatternSet, from, o, map, pas, sm, ems)
                if (ems.value.isEmpty) {
                  unifyPendingApplications(T, th, pattern.localPatternSet, m, pas, sm, ems) match {
                    case Either.Left(m2) =>
                      for (k <- 0 until apcs.size) {
                        for (apc <- toCondEquiv(th, apcs(k))) {
                          patterns = patterns :+ Rewriter.Pattern(pattern.name :+ s"Assumption$k", pattern.rightToLeft,
                            isPermutative(apc), HashSSet.empty, apc)
                        }
                      }
                      last(m2)
                      done = T
                    case _ =>
                  }
                }
                return
              }
              val assumption = assumptions(j)
              var k = 0
              while (k < pces.size && !done) {
                val ems: MBox[UnificationErrorMessages] = MBox(ISZ())
                val pas = MBox(pendingApplications)
                val sm = MBox(substMap)
                val pc = pces(k)
                val m = unifyExp(T, th, pattern.localPatternSet, assumption, pc, map, pas, sm, ems)
                if (ems.value.isEmpty) {
                  recAssumption(pas.value, sm.value, apcs :+ pc, m, j + 1)
                }
                k = k + 1
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

    override def postCoreExpIf(o: AST.CoreExp.If): MOption[AST.CoreExp.Base] = {
      o.cond match {
        case cond: AST.CoreExp.LitB => return if (cond.value) MSome(o.tExp) else MSome(o.fExp)
        case _ => return MNone()
      }
    }
  }

  object Rewriter {
    @datatype class Pattern(val name: ISZ[String],
                            val rightToLeft: B,
                            val isPermutative: B,
                            val localPatternSet: LocalPatternSet,
                            val exp: AST.CoreExp)
  }

  @strictpure def paramId(n: String): String = s"_$n"

  @pure def translate(th: TypeHierarchy, isPattern: B, exp: AST.Exp): AST.CoreExp.Base = {
    @pure def recBody(body: AST.Body, funStack: FunStack, localMap: LocalMap): AST.CoreExp.Base = {
      val stmts = body.stmts
      var m = localMap
      for (i <- 0 until stmts.size - 2) {
        m = recStmt(stmts(i), funStack, m)._2
      }
      return recAssignExp(stmts(stmts.size - 1).asAssignExp, funStack, m)
    }
    @pure def recStmt(stmt: AST.Stmt, funStack: FunStack, localMap: LocalMap): (Option[AST.CoreExp.Base], LocalMap) = {
      stmt match {
        case stmt: AST.Stmt.Expr => return (Some(rec(stmt.exp, funStack, localMap)), localMap)
        case stmt: AST.Stmt.Var =>
          val res = stmt.attr.resOpt.get.asInstanceOf[AST.ResolvedInfo.LocalVar]
          return (None(), localMap + (res.context, res.id) ~>
            recAssignExp(stmt.initOpt.get, funStack, localMap))
        case stmt: AST.Stmt.Block =>
          return (Some(recBody(stmt.body, funStack, localMap)), localMap)
        case stmt: AST.Stmt.If =>
          val condExp = rec(stmt.cond, funStack, localMap)
          val tExp = recBody(stmt.thenBody, funStack, localMap)
          val fExp = recBody(stmt.elseBody, funStack, localMap)
          return (Some(AST.CoreExp.If(condExp, tExp, fExp, stmt.attr.typedOpt.get)), localMap)
        case stmt: AST.Stmt.VarPattern => halt(s"TODO: $stmt")
        case stmt: AST.Stmt.Match => halt(s"TODO: $stmt")
        case _ => halt(s"Infeasible: $stmt")
      }
    }
    @pure def recAssignExp(ae: AST.AssignExp, funStack: FunStack, localMap: LocalMap): AST.CoreExp.Base = {
      val (Some(r), _) = recStmt(ae.asStmt, funStack, localMap)
      return r
    }
    @pure def rec(e: AST.Exp, funStack: FunStack, localMap: LocalMap): AST.CoreExp.Base = {
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
          return if (e.args.size == 1) rec(e.args(0), funStack, localMap)
          else AST.CoreExp.Tuple(for (arg <- e.args) yield rec(arg, funStack, localMap))
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
                  case "T" => return AST.CoreExp.LitB(T)
                  case "F" => return AST.CoreExp.LitB(F)
                  case _ =>
                }
              }
              return AST.CoreExp.ObjectVarRef(res.owner, res.id, e.typedOpt.get)
            case res: AST.ResolvedInfo.Method => halt(s"TODO: $e")
            case _ => halt(s"Infeasible: $e")
          }
        case e: AST.Exp.Unary =>
          return AST.CoreExp.Unary(e.op, rec(e.exp, funStack, localMap))
        case e: AST.Exp.Binary =>
          e.attr.resOpt.get match {
            case res: AST.ResolvedInfo.BuiltIn =>
              val left = rec(e.left, funStack, localMap)
              val right = rec(e.right, funStack, localMap)
              val op: String = res.kind match {
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondAnd =>
                  return AST.CoreExp.If(left, right, AST.CoreExp.LitB(F), AST.Typed.b)
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondOr =>
                  return AST.CoreExp.If(left, AST.CoreExp.LitB(T), right, AST.Typed.b)
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryCondImply =>
                  return AST.CoreExp.If(left, right, AST.CoreExp.LitB(T), AST.Typed.b)
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryEquiv => AST.Exp.BinaryOp.EquivUni
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryEq if th.isSubstitutableWithoutSpecVars(left.tipe) => AST.Exp.BinaryOp.EquivUni
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryInequiv => AST.Exp.BinaryOp.InequivUni
                case AST.ResolvedInfo.BuiltIn.Kind.BinaryNe if th.isSubstitutableWithoutSpecVars(left.tipe) => AST.Exp.BinaryOp.InequivUni
                case _ => e.op
              }
              return AST.CoreExp.Binary(left, op, right)
            case _ => halt(s"TODO: $e")
          }
        case e: AST.Exp.If =>
          return AST.CoreExp.If(rec(e.cond, funStack, localMap), rec(e.elseExp, funStack, localMap),
            rec(e.elseExp, funStack, localMap), e.typedOpt.get)
        case e: AST.Exp.Fun =>
          val params: ISZ[(String, AST.Typed)] = for (p <- e.params) yield
            (p.idOpt.get.value, p.typedOpt.get)
          var stack = funStack
          for (p <- params) {
            stack = stack.push(p)
          }
          val last = params(params.size - 1)
          var r = AST.CoreExp.Fun(AST.CoreExp.Param(last._1, last._2), recAssignExp(e.exp, stack, localMap))
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
            recAssignExp(e.fun.exp, stack, localMap))
          for (i <- params.size - 2 to 0 by -1) {
            val p = params(i)
            r = AST.CoreExp.Quant(kind, AST.CoreExp.Param(p._1, p._2), r)
          }
          return r
        case e: AST.Exp.StrictPureBlock =>
          return recStmt(e.block, funStack, localMap)._1.get
        case e: AST.Exp.Invoke =>
          val args: ISZ[AST.CoreExp.Base] = for (arg <- e.args) yield rec(arg, funStack, localMap)
          e.receiverOpt match {
            case Some(receiver) =>
              return AST.CoreExp.Apply(
                AST.CoreExp.Select(rec(receiver, funStack, localMap), e.ident.id.value,
                  e.ident.typedOpt.get), args, e.typedOpt.get)
            case _ => return AST.CoreExp.Apply(rec(e.ident, funStack, localMap),
              args, e.typedOpt.get)
          }
        case e: AST.Exp.InvokeNamed =>
          val args = MS.create[Z, AST.CoreExp.Base](e.args.size, AST.CoreExp.LitB(F))
          for (arg <- e.args) {
            args(arg.index) = rec(arg.arg, funStack, localMap)
          }
          e.receiverOpt match {
            case Some(receiver) =>
              return AST.CoreExp.Apply(
                AST.CoreExp.Select(rec(receiver, funStack, localMap), e.ident.id.value,
                  e.ident.typedOpt.get),
                args.toISZ, e.typedOpt.get)
            case _ => return AST.CoreExp.Apply(rec(e.ident, funStack, localMap),
              args.toISZ, e.typedOpt.get)
          }
        case e => halt(s"TODO: $e")
      }
    }
    return rec(exp, Stack.empty, HashSMap.empty)
  }

  @pure def unifyExp(silent: B,
                     th: TypeHierarchy,
                     localPatterns: LocalPatternSet,
                     pattern: AST.CoreExp.Base,
                     exp: AST.CoreExp.Base,
                     init: UnificationMap,
                     pendingApplications: MBox[PendingApplications],
                     substMap: MBox[HashMap[String, AST.Typed]],
                     errorMessages: MBox[UnificationErrorMessages]): UnificationMap = {
    @pure def rootLocalPatternOpt(e: AST.CoreExp.Base, args: ISZ[AST.CoreExp.Base]): Option[(ISZ[String], String, AST.Typed, ISZ[AST.CoreExp.Base])] = {
      e match {
        case e: AST.CoreExp.LocalVarRef =>
          val p = (e.context, e.id)
          return if (localPatterns.contains(p)) Some((p._1, p._2, e.tipe, args)) else None()
        case e: AST.CoreExp.Apply => return rootLocalPatternOpt(e.exp, e.args ++ args)
        case _ => return None()
      }
    }
    var map = init
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
              if (t1 != prevType) {
                errType(t1, prevType)
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
        case (p: AST.CoreExp.Tuple, e: AST.CoreExp.Tuple) =>
          if (p.args.size != e.args.size) {
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
          rootLocalPatternOpt(p, ISZ()) match {
            case Some((context, id, f: AST.Typed.Fun, args)) =>
              @strictpure def getArgTypes(t: AST.Typed, acc: ISZ[AST.Typed]): ISZ[AST.Typed] = t match {
                case f: AST.Typed.Fun => getArgTypes(f.ret, acc :+ f.args(0))
                case _ => acc
              }
              val argTypes = getArgTypes(f.curried, ISZ())
              if (args.size == argTypes.size) {
                @pure def hasLocalPatternInArgs: B = {
                  val lpd = LocalPatternDetector(localPatterns, F)
                  for (arg <- args) {
                    lpd.transformCoreExp(arg)
                  }
                  return lpd.hasLocalPattern
                }
                if (hasLocalPatternInArgs) {
                  pendingApplications.value = pendingApplications.value :+ (context, id, args, e)
                } else {
                  var substitutions = HashMap.empty[AST.CoreExp, AST.CoreExp.ParamVarRef]
                  for (i <- 0 until args.size) {
                    val n = args.size - i
                    substitutions = substitutions + args(i) ~> AST.CoreExp.ParamVarRef(n, paramId(n.string), argTypes(i))
                  }
                  val se = Substitutor(substitutions).transformCoreExpBase(e).getOrElse(e)
                  var r: AST.CoreExp.Base = AST.CoreExp.Fun(AST.CoreExp.Param(paramId(1.string), argTypes(args.size - 1)), se)
                  for (i <- args.size - 2 to 0 by -1) {
                    r = AST.CoreExp.Fun(AST.CoreExp.Param(paramId((args.size - i).string), argTypes(i)), r)
                  }
                  val key = (context, id)
                  map.get(key) match {
                    case Some(f) => err2(id, f, r)
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
          evalBase(th, EvalConfig.funApplicationOnly, AST.CoreExp.Apply(f, args, e.tipe)) match {
            case Some(pattern) =>
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

  @strictpure def evalBinaryLit(lit1: AST.CoreExp.Lit, op: String, lit2: AST.CoreExp.Lit): AST.CoreExp.Lit =
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

  @pure def eval(th: TypeHierarchy, config: EvalConfig, exp: AST.CoreExp): Option[AST.CoreExp] = {
    exp match {
      case exp: AST.CoreExp.Arrow =>
        var changed = F
        val left: AST.CoreExp.Base = evalBase(th, config, exp.left) match {
          case Some(l) =>
            changed = T
            l
          case _ => exp.left
        }
        val right: AST.CoreExp = eval(th, config, exp.right) match {
          case Some(r) =>
            changed = T
            r
          case _ => exp.right
        }
        return if (changed) Some(AST.CoreExp.Arrow(left, right)) else None()
      case exp: AST.CoreExp.Base => evalBase(th, config, exp) match {
        case Some(e) => return Some(e)
        case _ => return None()
      }
    }
  }

  @pure def evalBase(th: TypeHierarchy, config: EvalConfig, exp: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
    @strictpure def incDeBruijnMap(deBruijnMap: HashMap[Z, AST.CoreExp.Base], inc: Z): HashMap[Z, AST.CoreExp.Base] =
      HashMap ++ (for (p <- deBruijnMap.entries) yield (p._1 + inc, p._2))
    @pure def rec(deBruijnMap: HashMap[Z, AST.CoreExp.Base], e: AST.CoreExp.Base): Option[AST.CoreExp.Base] = {
      e match {
        case _: AST.CoreExp.Lit => return None()
        case _: AST.CoreExp.LocalVarRef => return None()
        case e: AST.CoreExp.ParamVarRef =>
          deBruijnMap.get(e.deBruijn) match {
            case Some(e2) => return Some(rec(deBruijnMap, e2).getOrElse(e2))
            case _ => return None()
          }
        case _: AST.CoreExp.ObjectVarRef => return None()
        case e: AST.CoreExp.Binary =>
          var changed = F
          val left: AST.CoreExp.Base = rec(deBruijnMap, e.left) match {
            case Some(l) =>
              changed = T
              l
            case _ => e.left
          }
          val right: AST.CoreExp.Base = rec(deBruijnMap, e.right) match {
            case Some(r) =>
              changed = T
              r
            case _ => e.right
          }
          if (config.equality) {
            if (left == right) {
              e.op match {
                case AST.Exp.BinaryOp.EquivUni => return Some(AST.CoreExp.LitB(T))
                case AST.Exp.BinaryOp.InequivUni => return Some(AST.CoreExp.LitB(F))
                case AST.Exp.BinaryOp.Lt => return Some(AST.CoreExp.LitB(F))
                case AST.Exp.BinaryOp.Le => return Some(AST.CoreExp.LitB(T))
                case AST.Exp.BinaryOp.Gt => return Some(AST.CoreExp.LitB(F))
                case AST.Exp.BinaryOp.Ge => return Some(AST.CoreExp.LitB(T))
                case AST.Exp.BinaryOp.Eq => return Some(AST.CoreExp.LitB(T))
                case AST.Exp.BinaryOp.Ne => return Some(AST.CoreExp.LitB(F))
                case _ =>
              }
            }
          }
          if (config.constantPropagation) {
            (left, right) match {
              case (left: AST.CoreExp.Lit, right: AST.CoreExp.Lit) => return Some(evalBinaryLit(left, e.op, right))
              case _ =>
            }
          }
          return if (changed) Some(e(left = left, right = right)) else None()
        case e: AST.CoreExp.Unary =>
          var changed = F
          val ue: AST.CoreExp.Base = rec(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          if (config.constantPropagation) {
            ue match {
              case exp: AST.CoreExp.Lit => return Some(evalUnaryLit(e.op, exp))
              case _ =>
            }
          }
          return if (changed) Some(e(exp = ue)) else None()
        case e: AST.CoreExp.Select =>
          rec(deBruijnMap, e.exp) match {
            case Some(receiver) => return Some(e(exp = receiver))
            case _ => return None()
          }
        case e: AST.CoreExp.Update =>
          var changed = F
          val receiver: AST.CoreExp.Base = rec(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          val arg: AST.CoreExp.Base = rec(deBruijnMap, e.arg) match {
            case Some(arg2) =>
              changed = T
              arg2
            case _ => e.arg
          }
          return if (changed) Some(e(exp = receiver, arg = arg)) else None()
        case e: AST.CoreExp.Indexing =>
          var changed = F
          val receiver: AST.CoreExp.Base = rec(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          val index: AST.CoreExp.Base = rec(deBruijnMap, e.index) match {
            case Some(index2) =>
              changed = T
              index2
            case _ => e.index
          }
          return if (changed) Some(e(exp = receiver, index = index)) else None()
        case e: AST.CoreExp.IndexingUpdate =>
          var changed = F
          val receiver: AST.CoreExp.Base = rec(deBruijnMap, e.exp) match {
            case Some(exp2) =>
              changed = T
              exp2
            case _ => e.exp
          }
          val index: AST.CoreExp.Base = rec(deBruijnMap, e.index) match {
            case Some(index2) =>
              changed = T
              index2
            case _ => e.index
          }
          val arg: AST.CoreExp.Base = rec(deBruijnMap, e.arg) match {
            case Some(arg2) =>
              changed = T
              arg2
            case _ => e.arg
          }
          return if (changed) Some(e(exp = receiver, index = index, arg = arg)) else None()
        case e: AST.CoreExp.Tuple =>
          var changed = F
          var args = ISZ[AST.CoreExp.Base]()
          for (arg <- e.args) {
            rec(deBruijnMap, arg) match {
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
          val cond: AST.CoreExp.Base = rec(deBruijnMap, e.cond) match {
            case Some(AST.CoreExp.LitB(b)) if config.constantPropagation =>
              return if (b) rec(deBruijnMap, e.tExp) else rec(deBruijnMap, e.fExp)
            case Some(c) =>
              changed = T
              c
            case _ => e.cond
          }
          return if (changed) Some(e(cond = cond)) else None()
        case e: AST.CoreExp.Apply =>
          var op = e.exp
          var changed = F
          rec(deBruijnMap, e.exp) match {
            case Some(o) =>
              op = o
              changed = T
            case _ =>
          }
          var args = ISZ[AST.CoreExp.Base]()
          for (arg <- e.args) {
            rec(deBruijnMap, arg) match {
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
              def recParams(fe: AST.CoreExp.Base): AST.CoreExp.Base = {
                fe match {
                  case fe: AST.CoreExp.Fun if params.size < args.size =>
                    params = params :+ (fe.param.id, fe.param.tipe)
                    return recParams(fe.exp)
                  case _ => return fe
                }
              }
              val body = recParams(f)
              var map = incDeBruijnMap(deBruijnMap, params.size)
              for (i <- params.size - 1 to 0 by -1) {
                map = map + (i + 1) ~> args(i)
              }
              rec(map, body) match {
                case Some(body2) =>
                  if (args.size > params.size) {
                    return Some(e(exp = body2, args = ops.ISZOps(args).slice(params.size, args.size)))
                  } else {
                    return Some(body2)
                  }
                case _ =>
              }
            case q: AST.CoreExp.Quant if config.quantApplication => halt("TODO")
            case _ =>
          }
          return if (changed) Some(e(exp = op, args = args)) else None()
        case e: AST.CoreExp.Fun =>
          var changed = F
          val body: AST.CoreExp.Base = rec(incDeBruijnMap(deBruijnMap, 1), e.exp) match {
            case Some(b) =>
              changed = T
              b
            case _ => e.exp
          }
          return if (changed) Some(e(exp = body)) else None()
        case e: AST.CoreExp.Quant =>
          var changed = F
          val body: AST.CoreExp.Base = rec(incDeBruijnMap(deBruijnMap, 1), e.exp) match {
            case Some(b) =>
              changed = T
              b
            case _ => e.exp
          }
          return if (changed) Some(e(exp = body)) else None()
        case e: AST.CoreExp.InstanceOfExp =>
          var receiver = e.exp
          var changed = F
          rec(deBruijnMap, e.exp) match {
            case Some(r) =>
              receiver = r
              changed = T
            case _ =>
          }
          return if (changed) Some(e(exp = receiver)) else None()
      }
    }
    return rec(HashMap.empty, exp)
  }

  @pure def toCondEquiv(th: TypeHierarchy, exp: AST.CoreExp): ISZ[AST.CoreExp] = {
    @pure def toEquiv(e: AST.CoreExp.Base): AST.CoreExp.Base = {
      e match {
        case AST.CoreExp.Binary(_, AST.Exp.BinaryOp.EquivUni, _) => return e
        case _ => return AST.CoreExp.Binary(e, AST.Exp.BinaryOp.EquivUni, AST.CoreExp.LitB(T))
      }
    }
    @pure def toCondEquivH(e: AST.CoreExp.Base): ISZ[AST.CoreExp] = {
      e match {
        case e: AST.CoreExp.Unary if e.op == AST.Exp.UnaryOp.Not =>
          return ISZ(AST.CoreExp.Binary(e.exp, AST.Exp.BinaryOp.EquivUni, AST.CoreExp.LitB(F)))
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
          return toCondEquivH(evalBase(th, EvalConfig.quantApplicationOnly,
            AST.CoreExp.Apply(
              e,
              ISZ(AST.CoreExp.LocalVarRef(T, ISZ(), paramId(e.param.id), e.param.tipe)),
              AST.Typed.b)).get)
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

  def patternsOf(th: TypeHierarchy, cache: Logika.Cache, name: ISZ[String], rightToLeft: B): ISZ[Rewriter.Pattern] = {
    cache.getPatterns(th, name) match {
      case Some(r) => return if (rightToLeft) for (e <- r) yield e(rightToLeft = rightToLeft) else r
      case _ =>
    }
    var r = ISZ[Rewriter.Pattern]()
    th.nameMap.get(name).get match {
      case info: Info.Theorem =>
        var localPatternSet: RewritingSystem.LocalPatternSet = HashSSet.empty
        val claim: AST.CoreExp = info.ast.claim match {
          case AST.Exp.QuantType(true, AST.Exp.Fun(_, params, AST.Stmt.Expr(c))) =>
            for (p <- params) {
              localPatternSet = localPatternSet + (info.name, p.idOpt.get.value)
            }
            RewritingSystem.translate(th, T, c)
          case c => RewritingSystem.translate(th, T, c)
        }
        for (c <- RewritingSystem.toCondEquiv(th, claim)) {
          r = r :+ Rewriter.Pattern(name, F, isPermutative(c), localPatternSet, c)
        }
      case info: Info.Fact =>
        var localPatternSet: RewritingSystem.LocalPatternSet = HashSSet.empty
        for (factClaim <- info.ast.claims) {
          val claim: AST.CoreExp = factClaim match {
            case AST.Exp.QuantType(true, AST.Exp.Fun(_, params, AST.Stmt.Expr(c))) =>
              for (p <- params) {
                localPatternSet = localPatternSet + (info.name, p.idOpt.get.value)
              }
              RewritingSystem.translate(th, T, c)
            case c => RewritingSystem.translate(th, T, c)
          }
          for (c <- RewritingSystem.toCondEquiv(th, claim)) {
            r = r :+ Rewriter.Pattern(name, F, isPermutative(c), localPatternSet, c)
          }
        }
      case info: Info.RsVal => r = r ++ retrievePatterns(th, cache, info.ast.init)
      case info: Info.Method => halt("TODO")
      case _ => halt("Infeasible")
    }
    cache.setPatterns(th, name, r)
    return if (rightToLeft) for (e <- r) yield e(rightToLeft = rightToLeft) else r
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

  @strictpure def isPermutative(exp: AST.CoreExp): B =
    exp match {
      case exp: AST.CoreExp.Arrow => isPermutative(exp.right)
      case AST.CoreExp.Binary(left, AST.Exp.BinaryOp.EquivUni, right) =>
        left.numberPattern(0)._2 == right.numberPattern(0)._2
      case _ => F
    }
}
