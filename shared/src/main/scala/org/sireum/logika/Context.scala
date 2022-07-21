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
import org.sireum.lang.{ast => AST}
import org.sireum.message.Position

object Context {
  @datatype class Method(val owner: ISZ[String],
                         val id: String,
                         val receiverTypeOpt: Option[AST.Typed],
                         val params: ISZ[(AST.Id, AST.Typed)],
                         val retType: AST.Typed,
                         val reads: ISZ[AST.Exp.Ident],
                         val requires: ISZ[AST.Exp],
                         val modifies: ISZ[AST.Exp.Ident],
                         val ensures: ISZ[AST.Exp],
                         val objectVarInMap: HashMap[ISZ[String], State.Value.Sym],
                         val fieldVarInMap: HashMap[String, State.Value.Sym],
                         val localInMap: HashMap[String, State.Value.Sym],
                         val posOpt: Option[Position]) {

    @strictpure def isInObject: B = receiverTypeOpt.isEmpty

    @strictpure def name: ISZ[String] = owner :+ id

    @memoize def paramIds: HashSet[String] = {
      return HashSet.empty[String] ++ (for (p <- params) yield p._1.value)
    }

    @memoize def modLocalIds: HashSet[String] = {
      var r = HashSet.empty[String]
      for (m <- modifies) {
        m.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar => r = r + res.id
          case _ =>
        }
      }
      return r
    }

    def modObjectVarMap(sm: HashMap[String, AST.Typed]): HashSMap[ISZ[String], (AST.Typed, Option[Position])] = {
      var r = HashSMap.empty[ISZ[String], (AST.Typed, Option[Position])]
      for (x <- modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var if res.isInObject && !r.contains(res.owner :+ res.id) =>
            val ids = res.owner :+ res.id
            r = r + ids ~> ((x.typedOpt.get.subst(sm), x.attr.posOpt))
          case _ =>
        }
      }
      return r
    }

    def readObjectVarMap(sm: HashMap[String, AST.Typed]): HashSMap[ISZ[String], (AST.Typed, Option[Position])] = {
      var r = HashSMap.empty[ISZ[String], (AST.Typed, Option[Position])]
      for (x <- reads) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var if res.isInObject && !r.contains(res.owner :+ res.id) =>
            val ids = res.owner :+ res.id
            r = r + ids ~> ((x.typedOpt.get.subst(sm), x.attr.posOpt))
          case _ =>
        }
      }
      return r
    }

    def fieldVarMap(sm: HashMap[String, AST.Typed]): HashSMap[String, (AST.Typed, Option[Position])] = {
      var r = HashSMap.empty[String, (AST.Typed, Option[Position])]
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.Var if !res.isInObject && !r.contains(res.id) =>
            r = r + res.id ~> ((x.typedOpt.get.subst(sm), x.posOpt))
          case _ =>
        }
      }
      return r
    }

    def localMap(sm: HashMap[String, AST.Typed]): HashSMap[String, (ISZ[String], AST.Id, AST.Typed)] = {
      var r = HashSMap.empty[String, (ISZ[String], AST.Id, AST.Typed)]
      for (p <- params) {
        val (id, t) = p
        r = r + id.value ~> ((name, id, t.subst(sm)))
      }
      for (x <- reads ++ modifies) {
        x.attr.resOpt.get match {
          case res: AST.ResolvedInfo.LocalVar if !r.contains(x.id.value) =>
            r = r + x.id.value ~> ((res.context, x.id, x.typedOpt.get.subst(sm)))
          case _ =>
        }
      }
      return r
    }
  }

  @datatype class InvokeMethodInfo(val isHelper: B,
                                   val sig: AST.MethodSig,
                                   val contract: AST.MethodContract,
                                   val res: AST.ResolvedInfo.Method,
                                   val strictPureBodyOpt: Option[AST.AssignExp])

  @datatype class ContractCaseResult(val isPreOK: B,
                                     val state: State,
                                     val retVal: State.Value,
                                     val requiresClaim: State.Claim.Prop,
                                     val messages: ISZ[message.Message]) {
    @strictpure def isOK: B = state.status
  }

  @strictpure def empty: Context = Context(ISZ(), None(), ISZ(), None())
}

@datatype class Context(val typeParams: ISZ[AST.TypeParam],
                        val methodOpt: Option[Context.Method],
                        val caseLabels: ISZ[AST.Exp.LitString],
                        val implicitCheckTitlePosOpt: Option[(String, Position)]) {

  @pure def owner: ISZ[String] = {
    methodOpt match {
      case Some(m) => return m.owner
      case _ => return ISZ()
    }
  }

  @pure def methodName: ISZ[String] = {
    methodOpt match {
      case Some(m) => return m.name
      case _ => return ISZ()
    }
  }

  @pure def receiverTypeOpt: Option[AST.Typed] = {
    methodOpt match {
      case Some(cm) => return cm.receiverTypeOpt
      case _ => return None()
    }
  }

  @pure def receiverLocalTypeOpt: Option[(AST.ResolvedInfo.LocalVar, AST.Typed)] = {
    methodOpt match {
      case Some(cm) if cm.receiverTypeOpt.nonEmpty => return Some((AST.ResolvedInfo.LocalVar(cm.owner :+ cm.id,
        AST.ResolvedInfo.LocalVar.Scope.Current, F, T, "this"), cm.receiverTypeOpt.get))
      case _ => return None()
    }
  }

  @pure def returnTypeOpt: Option[AST.Typed] = {
    methodOpt match {
      case Some(cm) => return Some(cm.retType)
      case _ => return None()
    }
  }
}
