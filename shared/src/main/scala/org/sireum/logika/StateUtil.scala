// #Sireum
/*
 Copyright (c) 2020, Robby, Kansas State University
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

@record class ClaimSTs(var value: ISZ[ST]) {
  def add(st: ST): Unit = {
    value = value :+ st
  }
}

@record class ClaimDefs(var value: HashMap[Z, ISZ[State.Claim.Def]]) {
  def addDef(d: State.Claim.Def): Unit = {
    value.get(d.sym.num) match {
      case Some(s) => value = value + d.sym.num ~> (s :+ d)
      case _ => value = value + d.sym.num ~> ISZ(d)
    }
  }
  def hasDef(d: State.Claim.Def): B = {
    return value.contains(d.sym.num)
  }
}

object ClaimDefs {
  @strictpure def empty: ClaimDefs = ClaimDefs(HashMap.empty)

  def collectDefs(claim: State.Claim, defs: ClaimDefs): Unit = {
    def rec(c: State.Claim): Unit = {
      c match {
        case c: State.Claim.Let.CurrentId =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Let.CurrentName =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Let.Id =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Let.Name =>
          if (!defs.hasDef(c)) {
            defs.addDef(c)
          }
        case c: State.Claim.Def => defs.addDef(c)
        case _ =>
      }
      c match {
        case c: State.Claim.Composite =>
          for (cc <- c.claims) {
            rec(cc)
          }
        case _ =>
      }
    }
    rec(claim)
  }

}

@record class LetCollector(var value: HashMap[Z, HashSet[State.Claim.Let]]) extends MStateTransformer {

  override def preStateClaim(o: State.Claim): MStateTransformer.PreResult[State.Claim] = {
    o match {
      case o: State.Claim.Let.Binary if Smt2.imsOps.contains(o.op) => return super.preStateClaim(o)
      case o: State.Claim.Let.CurrentId if o.declId => return super.preStateClaim(o)
      case o: State.Claim.Let =>
        val key = o.sym.num
        val s = value.get(key).getOrElse(HashSet.empty) + o
        value = value + key ~> s
        return MStateTransformer.PreResult(F, MNone())
      case _ =>
        return super.preStateClaim(o)
    }
  }
}

@record class UsedSymsCurrentDeclIdCollector(var syms: HashSet[State.Value.Sym],
                                             var currentDeclIds: ISZ[State.Claim.Let.CurrentId]) extends MStateTransformer {
  override def preStateClaimLetQuant(o: State.Claim.Let.Quant): MStateTransformer.PreResult[State.Claim.Let] = {
    syms = syms + o.sym
    return MStateTransformer.PreResult(T, MNone())
  }

  override def preStateValueSym(o: State.Value.Sym): MStateTransformer.PreResult[State.Value] = {
    syms = syms + o
    return super.preStateValueSym(o)
  }

  override def preStateClaimLetCurrentId(o: State.Claim.Let.CurrentId): MStateTransformer.PreResult[State.Claim.Let] = {
    if (o.declId) {
      currentDeclIds = currentDeclIds :+ o
    }
    return super.preStateClaimLetCurrentId(o)
  }
}

object StateUtil {
  def collectLetClaims(enabled: B, claims: ISZ[State.Claim]): HashMap[Z, ISZ[State.Claim.Let]] = {
    if (enabled) {
      val lc = LetCollector(HashMap.empty)
      for (c <- claims) {
        lc.transformStateClaim(c)
      }
      return HashMap.empty[Z, ISZ[State.Claim.Let]] ++ (for (p <- lc.value.entries) yield (p._1, p._2.elements))
    } else {
      return HashMap.empty
    }
  }

  def value2ST(smt2: Smt2, lets: HashMap[Z, ISZ[State.Claim.Let]]): State.Value => ST = {
    if (lets.isEmpty) {
      return smt2.v2ST _
    }
    var cache = HashMap.empty[Z, ST]
    def sv2ST(v: State.Value): ST = {
      v match {
        case v: State.Value.Sym =>
          cache.get(v.num) match {
            case Some(r) => return r
            case _ =>
              val r: ST = lets.get(v.num) match {
                case Some(ls) if ls.size == 1 => smt2.l2RhsST(ls(0), sv2ST _, lets)
                case _ => smt2.v2ST(v)
              }
              cache = cache + v.num ~> r
              return r
          }
        case _ => return smt2.v2ST(v)
      }
    }
    return sv2ST _
  }
}