// #Sireum
// @formatter:off

/*
 Copyright (c) 2017-2021, Robby, Kansas State University
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

// This file is auto-generated from State.scala

package org.sireum.logika

import org.sireum._

object MStateTransformer {

  @record class PreResult[T](val continu: B,
                             val resultOpt: MOption[T])

  val PreResultState: PreResult[State] = PreResult(T, MNone())

  val PostResultState: MOption[State] = MNone()

  def transformISZ[T](s: IS[Z, T], f: T => MOption[T]): MOption[IS[Z, T]] = {
    val s2: MS[Z, T] = s.toMS
    var changed: B = F
    for (i <- s2.indices) {
      val e: T = s(i)
      val r: MOption[T] = f(e)
      changed = changed || r.nonEmpty
      s2(i) = r.getOrElse(e)
    }
    if (changed) {
      return MSome(s2.toIS)
    } else {
      return MNone()
    }
  }

  val PreResultStateIFun: PreResult[State.Fun] = PreResult(T, MNone())

  val PostResultStateIFun: MOption[State.Fun] = MNone()

  val PreResultStateOFun: PreResult[State.Fun] = PreResult(T, MNone())

  val PostResultStateOFun: MOption[State.Fun] = MNone()

  val PreResultStateValueUnit: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueUnit: MOption[State.Value] = MNone()

  val PreResultStateValueB: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueB: MOption[State.Value] = MNone()

  val PreResultStateValueZ: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueZ: MOption[State.Value] = MNone()

  val PreResultStateValueC: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueC: MOption[State.Value] = MNone()

  val PreResultStateValueF32: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueF32: MOption[State.Value] = MNone()

  val PreResultStateValueF64: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueF64: MOption[State.Value] = MNone()

  val PreResultStateValueR: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueR: MOption[State.Value] = MNone()

  val PreResultStateValueString: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueString: MOption[State.Value] = MNone()

  val PreResultStateValueRange: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueRange: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueS8: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueS8: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueS16: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueS16: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueS32: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueS32: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueS64: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueS64: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueU8: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueU8: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueU16: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueU16: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueU32: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueU32: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueU64: PreResult[State.Value.SubZ] = PreResult(T, MNone())

  val PostResultStateValueU64: MOption[State.Value.SubZ] = MNone()

  val PreResultStateValueEnum: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueEnum: MOption[State.Value] = MNone()

  val PreResultStateValueSym: PreResult[State.Value] = PreResult(T, MNone())

  val PostResultStateValueSym: MOption[State.Value] = MNone()

  val PreResultStateClaimLabel: PreResult[State.Claim] = PreResult(T, MNone())

  val PostResultStateClaimLabel: MOption[State.Claim] = MNone()

  val PreResultStateClaimProp: PreResult[State.Claim] = PreResult(T, MNone())

  val PostResultStateClaimProp: MOption[State.Claim] = MNone()

  val PreResultStateClaimAnd: PreResult[State.Claim.Composite] = PreResult(T, MNone())

  val PostResultStateClaimAnd: MOption[State.Claim.Composite] = MNone()

  val PreResultStateClaimOr: PreResult[State.Claim.Composite] = PreResult(T, MNone())

  val PostResultStateClaimOr: MOption[State.Claim.Composite] = MNone()

  val PreResultStateClaimImply: PreResult[State.Claim.Composite] = PreResult(T, MNone())

  val PostResultStateClaimImply: MOption[State.Claim.Composite] = MNone()

  val PreResultStateClaimIf: PreResult[State.Claim.Composite] = PreResult(T, MNone())

  val PostResultStateClaimIf: MOption[State.Claim.Composite] = MNone()

  val PreResultStateClaimDefSeqLit: PreResult[State.Claim.Def] = PreResult(T, MNone())

  val PostResultStateClaimDefSeqLit: MOption[State.Claim.Def] = MNone()

  val PreResultStateClaimDefSeqLitArg: PreResult[State.Claim.Def.SeqLit.Arg] = PreResult(T, MNone())

  val PostResultStateClaimDefSeqLitArg: MOption[State.Claim.Def.SeqLit.Arg] = MNone()

  val PreResultStateClaimDefSeqStore: PreResult[State.Claim.Def] = PreResult(T, MNone())

  val PostResultStateClaimDefSeqStore: MOption[State.Claim.Def] = MNone()

  val PreResultStateClaimDefFieldStore: PreResult[State.Claim.Def] = PreResult(T, MNone())

  val PostResultStateClaimDefFieldStore: MOption[State.Claim.Def] = MNone()

  val PreResultStateClaimDefAdtLit: PreResult[State.Claim.Def] = PreResult(T, MNone())

  val PostResultStateClaimDefAdtLit: MOption[State.Claim.Def] = MNone()

  val PreResultStateClaimDefRandom: PreResult[State.Claim.Def] = PreResult(T, MNone())

  val PostResultStateClaimDefRandom: MOption[State.Claim.Def] = MNone()

  val PreResultStateClaimLetCurrentName: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetCurrentName: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetName: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetName: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetCurrentId: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetCurrentId: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetId: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetId: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetEq: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetEq: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetTypeTest: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetTypeTest: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetQuantVarId: PreResult[State.Claim.Let.Quant.Var] = PreResult(T, MNone())

  val PostResultStateClaimLetQuantVarId: MOption[State.Claim.Let.Quant.Var] = MNone()

  val PreResultStateClaimLetQuantVarSym: PreResult[State.Claim.Let.Quant.Var] = PreResult(T, MNone())

  val PostResultStateClaimLetQuantVarSym: MOption[State.Claim.Let.Quant.Var] = MNone()

  val PreResultStateClaimLetQuant: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetQuant: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetIte: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetIte: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetBinary: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetBinary: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetUnary: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetUnary: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetSeqLookup: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetSeqLookup: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetSeqInBound: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetSeqInBound: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetFieldLookup: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetFieldLookup: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetProofFunApply: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetProofFunApply: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetApply: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetApply: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetIApply: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetIApply: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetTupleLit: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetTupleLit: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetAnd: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetAnd: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetOr: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetOr: MOption[State.Claim.Let] = MNone()

  val PreResultStateClaimLetImply: PreResult[State.Claim.Let] = PreResult(T, MNone())

  val PostResultStateClaimLetImply: MOption[State.Claim.Let] = MNone()

  val PreResultStateProofFun: PreResult[State.ProofFun] = PreResult(T, MNone())

  val PostResultStateProofFun: MOption[State.ProofFun] = MNone()

}

import MStateTransformer._

@msig trait MStateTransformer {

  def preState(o: State): PreResult[State] = {
    return PreResultState
  }

  def preStateValue(o: State.Value): PreResult[State.Value] = {
    o match {
      case o: State.Value.Unit => return preStateValueUnit(o)
      case o: State.Value.B => return preStateValueB(o)
      case o: State.Value.Z => return preStateValueZ(o)
      case o: State.Value.C => return preStateValueC(o)
      case o: State.Value.F32 => return preStateValueF32(o)
      case o: State.Value.F64 => return preStateValueF64(o)
      case o: State.Value.R => return preStateValueR(o)
      case o: State.Value.String => return preStateValueString(o)
      case o: State.Value.Range =>
        val r: PreResult[State.Value] = preStateValueRange(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.S8 =>
        val r: PreResult[State.Value] = preStateValueS8(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.S16 =>
        val r: PreResult[State.Value] = preStateValueS16(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.S32 =>
        val r: PreResult[State.Value] = preStateValueS32(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.S64 =>
        val r: PreResult[State.Value] = preStateValueS64(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.U8 =>
        val r: PreResult[State.Value] = preStateValueU8(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.U16 =>
        val r: PreResult[State.Value] = preStateValueU16(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.U32 =>
        val r: PreResult[State.Value] = preStateValueU32(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.U64 =>
        val r: PreResult[State.Value] = preStateValueU64(o) match {
         case PreResult(continu, MSome(r: State.Value)) => PreResult(continu, MSome[State.Value](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Value]())
        }
        return r
      case o: State.Value.Enum => return preStateValueEnum(o)
      case o: State.Value.Sym => return preStateValueSym(o)
    }
  }

  def preStateFun(o: State.Fun): PreResult[State.Fun] = {
    o match {
      case o: State.IFun => return preStateIFun(o)
      case o: State.OFun => return preStateOFun(o)
    }
  }

  def preStateIFun(o: State.IFun): PreResult[State.Fun] = {
    return PreResultStateIFun
  }

  def preStateOFun(o: State.OFun): PreResult[State.Fun] = {
    return PreResultStateOFun
  }

  def preStateValueUnit(o: State.Value.Unit): PreResult[State.Value] = {
    return PreResultStateValueUnit
  }

  def preStateValueB(o: State.Value.B): PreResult[State.Value] = {
    return PreResultStateValueB
  }

  def preStateValueZ(o: State.Value.Z): PreResult[State.Value] = {
    return PreResultStateValueZ
  }

  def preStateValueC(o: State.Value.C): PreResult[State.Value] = {
    return PreResultStateValueC
  }

  def preStateValueF32(o: State.Value.F32): PreResult[State.Value] = {
    return PreResultStateValueF32
  }

  def preStateValueF64(o: State.Value.F64): PreResult[State.Value] = {
    return PreResultStateValueF64
  }

  def preStateValueR(o: State.Value.R): PreResult[State.Value] = {
    return PreResultStateValueR
  }

  def preStateValueString(o: State.Value.String): PreResult[State.Value] = {
    return PreResultStateValueString
  }

  def preStateValueSubZ(o: State.Value.SubZ): PreResult[State.Value.SubZ] = {
    o match {
      case o: State.Value.Range => return preStateValueRange(o)
      case o: State.Value.S8 => return preStateValueS8(o)
      case o: State.Value.S16 => return preStateValueS16(o)
      case o: State.Value.S32 => return preStateValueS32(o)
      case o: State.Value.S64 => return preStateValueS64(o)
      case o: State.Value.U8 => return preStateValueU8(o)
      case o: State.Value.U16 => return preStateValueU16(o)
      case o: State.Value.U32 => return preStateValueU32(o)
      case o: State.Value.U64 => return preStateValueU64(o)
    }
  }

  def preStateValueRange(o: State.Value.Range): PreResult[State.Value.SubZ] = {
    return PreResultStateValueRange
  }

  def preStateValueS8(o: State.Value.S8): PreResult[State.Value.SubZ] = {
    return PreResultStateValueS8
  }

  def preStateValueS16(o: State.Value.S16): PreResult[State.Value.SubZ] = {
    return PreResultStateValueS16
  }

  def preStateValueS32(o: State.Value.S32): PreResult[State.Value.SubZ] = {
    return PreResultStateValueS32
  }

  def preStateValueS64(o: State.Value.S64): PreResult[State.Value.SubZ] = {
    return PreResultStateValueS64
  }

  def preStateValueU8(o: State.Value.U8): PreResult[State.Value.SubZ] = {
    return PreResultStateValueU8
  }

  def preStateValueU16(o: State.Value.U16): PreResult[State.Value.SubZ] = {
    return PreResultStateValueU16
  }

  def preStateValueU32(o: State.Value.U32): PreResult[State.Value.SubZ] = {
    return PreResultStateValueU32
  }

  def preStateValueU64(o: State.Value.U64): PreResult[State.Value.SubZ] = {
    return PreResultStateValueU64
  }

  def preStateValueEnum(o: State.Value.Enum): PreResult[State.Value] = {
    return PreResultStateValueEnum
  }

  def preStateValueSym(o: State.Value.Sym): PreResult[State.Value] = {
    return PreResultStateValueSym
  }

  def preStateClaim(o: State.Claim): PreResult[State.Claim] = {
    o match {
      case o: State.Claim.Label => return preStateClaimLabel(o)
      case o: State.Claim.Prop => return preStateClaimProp(o)
      case o: State.Claim.And =>
        val r: PreResult[State.Claim] = preStateClaimAnd(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Or =>
        val r: PreResult[State.Claim] = preStateClaimOr(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Imply =>
        val r: PreResult[State.Claim] = preStateClaimImply(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.If =>
        val r: PreResult[State.Claim] = preStateClaimIf(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Def.SeqLit =>
        val r: PreResult[State.Claim] = preStateClaimDefSeqLit(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Def.SeqStore =>
        val r: PreResult[State.Claim] = preStateClaimDefSeqStore(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Def.FieldStore =>
        val r: PreResult[State.Claim] = preStateClaimDefFieldStore(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Def.AdtLit =>
        val r: PreResult[State.Claim] = preStateClaimDefAdtLit(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Def.Random =>
        val r: PreResult[State.Claim] = preStateClaimDefRandom(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.CurrentName =>
        val r: PreResult[State.Claim] = preStateClaimLetCurrentName(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Name =>
        val r: PreResult[State.Claim] = preStateClaimLetName(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.CurrentId =>
        val r: PreResult[State.Claim] = preStateClaimLetCurrentId(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Id =>
        val r: PreResult[State.Claim] = preStateClaimLetId(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Eq =>
        val r: PreResult[State.Claim] = preStateClaimLetEq(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.TypeTest =>
        val r: PreResult[State.Claim] = preStateClaimLetTypeTest(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Quant =>
        val r: PreResult[State.Claim] = preStateClaimLetQuant(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Ite =>
        val r: PreResult[State.Claim] = preStateClaimLetIte(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Binary =>
        val r: PreResult[State.Claim] = preStateClaimLetBinary(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Unary =>
        val r: PreResult[State.Claim] = preStateClaimLetUnary(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.SeqLookup =>
        val r: PreResult[State.Claim] = preStateClaimLetSeqLookup(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.SeqInBound =>
        val r: PreResult[State.Claim] = preStateClaimLetSeqInBound(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.FieldLookup =>
        val r: PreResult[State.Claim] = preStateClaimLetFieldLookup(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.ProofFunApply =>
        val r: PreResult[State.Claim] = preStateClaimLetProofFunApply(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Apply =>
        val r: PreResult[State.Claim] = preStateClaimLetApply(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.IApply =>
        val r: PreResult[State.Claim] = preStateClaimLetIApply(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.TupleLit =>
        val r: PreResult[State.Claim] = preStateClaimLetTupleLit(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.And =>
        val r: PreResult[State.Claim] = preStateClaimLetAnd(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Or =>
        val r: PreResult[State.Claim] = preStateClaimLetOr(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
      case o: State.Claim.Let.Imply =>
        val r: PreResult[State.Claim] = preStateClaimLetImply(o) match {
         case PreResult(continu, MSome(r: State.Claim)) => PreResult(continu, MSome[State.Claim](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim]())
        }
        return r
    }
  }

  def preStateClaimLabel(o: State.Claim.Label): PreResult[State.Claim] = {
    return PreResultStateClaimLabel
  }

  def preStateClaimProp(o: State.Claim.Prop): PreResult[State.Claim] = {
    return PreResultStateClaimProp
  }

  def preStateClaimAnd(o: State.Claim.And): PreResult[State.Claim.Composite] = {
    return PreResultStateClaimAnd
  }

  def preStateClaimOr(o: State.Claim.Or): PreResult[State.Claim.Composite] = {
    return PreResultStateClaimOr
  }

  def preStateClaimImply(o: State.Claim.Imply): PreResult[State.Claim.Composite] = {
    return PreResultStateClaimImply
  }

  def preStateClaimIf(o: State.Claim.If): PreResult[State.Claim.Composite] = {
    return PreResultStateClaimIf
  }

  def preStateClaimDef(o: State.Claim.Def): PreResult[State.Claim.Def] = {
    o match {
      case o: State.Claim.Def.SeqLit => return preStateClaimDefSeqLit(o)
      case o: State.Claim.Def.SeqStore => return preStateClaimDefSeqStore(o)
      case o: State.Claim.Def.FieldStore => return preStateClaimDefFieldStore(o)
      case o: State.Claim.Def.AdtLit => return preStateClaimDefAdtLit(o)
      case o: State.Claim.Def.Random => return preStateClaimDefRandom(o)
      case o: State.Claim.Let.CurrentName =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetCurrentName(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Name =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetName(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.CurrentId =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetCurrentId(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Id =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetId(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Eq =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetEq(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.TypeTest =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetTypeTest(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Quant =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetQuant(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Ite =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetIte(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Binary =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetBinary(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Unary =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetUnary(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.SeqLookup =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetSeqLookup(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.SeqInBound =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetSeqInBound(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.FieldLookup =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetFieldLookup(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.ProofFunApply =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetProofFunApply(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Apply =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetApply(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.IApply =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetIApply(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.TupleLit =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetTupleLit(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.And =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetAnd(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Or =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetOr(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
      case o: State.Claim.Let.Imply =>
        val r: PreResult[State.Claim.Def] = preStateClaimLetImply(o) match {
         case PreResult(continu, MSome(r: State.Claim.Def)) => PreResult(continu, MSome[State.Claim.Def](r))
         case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Claim.Def")
         case PreResult(continu, _) => PreResult(continu, MNone[State.Claim.Def]())
        }
        return r
    }
  }

  def preStateClaimDefSeqLit(o: State.Claim.Def.SeqLit): PreResult[State.Claim.Def] = {
    return PreResultStateClaimDefSeqLit
  }

  def preStateClaimDefSeqLitArg(o: State.Claim.Def.SeqLit.Arg): PreResult[State.Claim.Def.SeqLit.Arg] = {
    return PreResultStateClaimDefSeqLitArg
  }

  def preStateClaimDefSeqStore(o: State.Claim.Def.SeqStore): PreResult[State.Claim.Def] = {
    return PreResultStateClaimDefSeqStore
  }

  def preStateClaimDefFieldStore(o: State.Claim.Def.FieldStore): PreResult[State.Claim.Def] = {
    return PreResultStateClaimDefFieldStore
  }

  def preStateClaimDefAdtLit(o: State.Claim.Def.AdtLit): PreResult[State.Claim.Def] = {
    return PreResultStateClaimDefAdtLit
  }

  def preStateClaimDefRandom(o: State.Claim.Def.Random): PreResult[State.Claim.Def] = {
    return PreResultStateClaimDefRandom
  }

  def preStateClaimLet(o: State.Claim.Let): PreResult[State.Claim.Let] = {
    o match {
      case o: State.Claim.Let.CurrentName => return preStateClaimLetCurrentName(o)
      case o: State.Claim.Let.Name => return preStateClaimLetName(o)
      case o: State.Claim.Let.CurrentId => return preStateClaimLetCurrentId(o)
      case o: State.Claim.Let.Id => return preStateClaimLetId(o)
      case o: State.Claim.Let.Eq => return preStateClaimLetEq(o)
      case o: State.Claim.Let.TypeTest => return preStateClaimLetTypeTest(o)
      case o: State.Claim.Let.Quant => return preStateClaimLetQuant(o)
      case o: State.Claim.Let.Ite => return preStateClaimLetIte(o)
      case o: State.Claim.Let.Binary => return preStateClaimLetBinary(o)
      case o: State.Claim.Let.Unary => return preStateClaimLetUnary(o)
      case o: State.Claim.Let.SeqLookup => return preStateClaimLetSeqLookup(o)
      case o: State.Claim.Let.SeqInBound => return preStateClaimLetSeqInBound(o)
      case o: State.Claim.Let.FieldLookup => return preStateClaimLetFieldLookup(o)
      case o: State.Claim.Let.ProofFunApply => return preStateClaimLetProofFunApply(o)
      case o: State.Claim.Let.Apply => return preStateClaimLetApply(o)
      case o: State.Claim.Let.IApply => return preStateClaimLetIApply(o)
      case o: State.Claim.Let.TupleLit => return preStateClaimLetTupleLit(o)
      case o: State.Claim.Let.And => return preStateClaimLetAnd(o)
      case o: State.Claim.Let.Or => return preStateClaimLetOr(o)
      case o: State.Claim.Let.Imply => return preStateClaimLetImply(o)
    }
  }

  def preStateClaimLetCurrentName(o: State.Claim.Let.CurrentName): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetCurrentName
  }

  def preStateClaimLetName(o: State.Claim.Let.Name): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetName
  }

  def preStateClaimLetCurrentId(o: State.Claim.Let.CurrentId): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetCurrentId
  }

  def preStateClaimLetId(o: State.Claim.Let.Id): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetId
  }

  def preStateClaimLetEq(o: State.Claim.Let.Eq): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetEq
  }

  def preStateClaimLetTypeTest(o: State.Claim.Let.TypeTest): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetTypeTest
  }

  def preStateClaimLetQuantVar(o: State.Claim.Let.Quant.Var): PreResult[State.Claim.Let.Quant.Var] = {
    o match {
      case o: State.Claim.Let.Quant.Var.Id => return preStateClaimLetQuantVarId(o)
      case o: State.Claim.Let.Quant.Var.Sym => return preStateClaimLetQuantVarSym(o)
    }
  }

  def preStateClaimLetQuantVarId(o: State.Claim.Let.Quant.Var.Id): PreResult[State.Claim.Let.Quant.Var] = {
    return PreResultStateClaimLetQuantVarId
  }

  def preStateClaimLetQuantVarSym(o: State.Claim.Let.Quant.Var.Sym): PreResult[State.Claim.Let.Quant.Var] = {
    return PreResultStateClaimLetQuantVarSym
  }

  def preStateClaimLetQuant(o: State.Claim.Let.Quant): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetQuant
  }

  def preStateClaimLetIte(o: State.Claim.Let.Ite): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetIte
  }

  def preStateClaimLetBinary(o: State.Claim.Let.Binary): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetBinary
  }

  def preStateClaimLetUnary(o: State.Claim.Let.Unary): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetUnary
  }

  def preStateClaimLetSeqLookup(o: State.Claim.Let.SeqLookup): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetSeqLookup
  }

  def preStateClaimLetSeqInBound(o: State.Claim.Let.SeqInBound): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetSeqInBound
  }

  def preStateClaimLetFieldLookup(o: State.Claim.Let.FieldLookup): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetFieldLookup
  }

  def preStateClaimLetProofFunApply(o: State.Claim.Let.ProofFunApply): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetProofFunApply
  }

  def preStateClaimLetApply(o: State.Claim.Let.Apply): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetApply
  }

  def preStateClaimLetIApply(o: State.Claim.Let.IApply): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetIApply
  }

  def preStateClaimLetTupleLit(o: State.Claim.Let.TupleLit): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetTupleLit
  }

  def preStateClaimLetAnd(o: State.Claim.Let.And): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetAnd
  }

  def preStateClaimLetOr(o: State.Claim.Let.Or): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetOr
  }

  def preStateClaimLetImply(o: State.Claim.Let.Imply): PreResult[State.Claim.Let] = {
    return PreResultStateClaimLetImply
  }

  def preStateProofFun(o: State.ProofFun): PreResult[State.ProofFun] = {
    return PreResultStateProofFun
  }

  def postState(o: State): MOption[State] = {
    return PostResultState
  }

  def postStateValue(o: State.Value): MOption[State.Value] = {
    o match {
      case o: State.Value.Unit => return postStateValueUnit(o)
      case o: State.Value.B => return postStateValueB(o)
      case o: State.Value.Z => return postStateValueZ(o)
      case o: State.Value.C => return postStateValueC(o)
      case o: State.Value.F32 => return postStateValueF32(o)
      case o: State.Value.F64 => return postStateValueF64(o)
      case o: State.Value.R => return postStateValueR(o)
      case o: State.Value.String => return postStateValueString(o)
      case o: State.Value.Range =>
        val r: MOption[State.Value] = postStateValueRange(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.S8 =>
        val r: MOption[State.Value] = postStateValueS8(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.S16 =>
        val r: MOption[State.Value] = postStateValueS16(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.S32 =>
        val r: MOption[State.Value] = postStateValueS32(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.S64 =>
        val r: MOption[State.Value] = postStateValueS64(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.U8 =>
        val r: MOption[State.Value] = postStateValueU8(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.U16 =>
        val r: MOption[State.Value] = postStateValueU16(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.U32 =>
        val r: MOption[State.Value] = postStateValueU32(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.U64 =>
        val r: MOption[State.Value] = postStateValueU64(o) match {
         case MSome(result: State.Value) => MSome[State.Value](result)
         case MSome(_) => halt("Can only produce object of type State.Value")
         case _ => MNone[State.Value]()
        }
        return r
      case o: State.Value.Enum => return postStateValueEnum(o)
      case o: State.Value.Sym => return postStateValueSym(o)
    }
  }

  def postStateFun(o: State.Fun): MOption[State.Fun] = {
    o match {
      case o: State.IFun => return postStateIFun(o)
      case o: State.OFun => return postStateOFun(o)
    }
  }

  def postStateIFun(o: State.IFun): MOption[State.Fun] = {
    return PostResultStateIFun
  }

  def postStateOFun(o: State.OFun): MOption[State.Fun] = {
    return PostResultStateOFun
  }

  def postStateValueUnit(o: State.Value.Unit): MOption[State.Value] = {
    return PostResultStateValueUnit
  }

  def postStateValueB(o: State.Value.B): MOption[State.Value] = {
    return PostResultStateValueB
  }

  def postStateValueZ(o: State.Value.Z): MOption[State.Value] = {
    return PostResultStateValueZ
  }

  def postStateValueC(o: State.Value.C): MOption[State.Value] = {
    return PostResultStateValueC
  }

  def postStateValueF32(o: State.Value.F32): MOption[State.Value] = {
    return PostResultStateValueF32
  }

  def postStateValueF64(o: State.Value.F64): MOption[State.Value] = {
    return PostResultStateValueF64
  }

  def postStateValueR(o: State.Value.R): MOption[State.Value] = {
    return PostResultStateValueR
  }

  def postStateValueString(o: State.Value.String): MOption[State.Value] = {
    return PostResultStateValueString
  }

  def postStateValueSubZ(o: State.Value.SubZ): MOption[State.Value.SubZ] = {
    o match {
      case o: State.Value.Range => return postStateValueRange(o)
      case o: State.Value.S8 => return postStateValueS8(o)
      case o: State.Value.S16 => return postStateValueS16(o)
      case o: State.Value.S32 => return postStateValueS32(o)
      case o: State.Value.S64 => return postStateValueS64(o)
      case o: State.Value.U8 => return postStateValueU8(o)
      case o: State.Value.U16 => return postStateValueU16(o)
      case o: State.Value.U32 => return postStateValueU32(o)
      case o: State.Value.U64 => return postStateValueU64(o)
    }
  }

  def postStateValueRange(o: State.Value.Range): MOption[State.Value.SubZ] = {
    return PostResultStateValueRange
  }

  def postStateValueS8(o: State.Value.S8): MOption[State.Value.SubZ] = {
    return PostResultStateValueS8
  }

  def postStateValueS16(o: State.Value.S16): MOption[State.Value.SubZ] = {
    return PostResultStateValueS16
  }

  def postStateValueS32(o: State.Value.S32): MOption[State.Value.SubZ] = {
    return PostResultStateValueS32
  }

  def postStateValueS64(o: State.Value.S64): MOption[State.Value.SubZ] = {
    return PostResultStateValueS64
  }

  def postStateValueU8(o: State.Value.U8): MOption[State.Value.SubZ] = {
    return PostResultStateValueU8
  }

  def postStateValueU16(o: State.Value.U16): MOption[State.Value.SubZ] = {
    return PostResultStateValueU16
  }

  def postStateValueU32(o: State.Value.U32): MOption[State.Value.SubZ] = {
    return PostResultStateValueU32
  }

  def postStateValueU64(o: State.Value.U64): MOption[State.Value.SubZ] = {
    return PostResultStateValueU64
  }

  def postStateValueEnum(o: State.Value.Enum): MOption[State.Value] = {
    return PostResultStateValueEnum
  }

  def postStateValueSym(o: State.Value.Sym): MOption[State.Value] = {
    return PostResultStateValueSym
  }

  def postStateClaim(o: State.Claim): MOption[State.Claim] = {
    o match {
      case o: State.Claim.Label => return postStateClaimLabel(o)
      case o: State.Claim.Prop => return postStateClaimProp(o)
      case o: State.Claim.And =>
        val r: MOption[State.Claim] = postStateClaimAnd(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Or =>
        val r: MOption[State.Claim] = postStateClaimOr(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Imply =>
        val r: MOption[State.Claim] = postStateClaimImply(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.If =>
        val r: MOption[State.Claim] = postStateClaimIf(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Def.SeqLit =>
        val r: MOption[State.Claim] = postStateClaimDefSeqLit(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Def.SeqStore =>
        val r: MOption[State.Claim] = postStateClaimDefSeqStore(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Def.FieldStore =>
        val r: MOption[State.Claim] = postStateClaimDefFieldStore(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Def.AdtLit =>
        val r: MOption[State.Claim] = postStateClaimDefAdtLit(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Def.Random =>
        val r: MOption[State.Claim] = postStateClaimDefRandom(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.CurrentName =>
        val r: MOption[State.Claim] = postStateClaimLetCurrentName(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Name =>
        val r: MOption[State.Claim] = postStateClaimLetName(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.CurrentId =>
        val r: MOption[State.Claim] = postStateClaimLetCurrentId(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Id =>
        val r: MOption[State.Claim] = postStateClaimLetId(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Eq =>
        val r: MOption[State.Claim] = postStateClaimLetEq(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.TypeTest =>
        val r: MOption[State.Claim] = postStateClaimLetTypeTest(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Quant =>
        val r: MOption[State.Claim] = postStateClaimLetQuant(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Ite =>
        val r: MOption[State.Claim] = postStateClaimLetIte(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Binary =>
        val r: MOption[State.Claim] = postStateClaimLetBinary(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Unary =>
        val r: MOption[State.Claim] = postStateClaimLetUnary(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.SeqLookup =>
        val r: MOption[State.Claim] = postStateClaimLetSeqLookup(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.SeqInBound =>
        val r: MOption[State.Claim] = postStateClaimLetSeqInBound(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.FieldLookup =>
        val r: MOption[State.Claim] = postStateClaimLetFieldLookup(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.ProofFunApply =>
        val r: MOption[State.Claim] = postStateClaimLetProofFunApply(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Apply =>
        val r: MOption[State.Claim] = postStateClaimLetApply(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.IApply =>
        val r: MOption[State.Claim] = postStateClaimLetIApply(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.TupleLit =>
        val r: MOption[State.Claim] = postStateClaimLetTupleLit(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.And =>
        val r: MOption[State.Claim] = postStateClaimLetAnd(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Or =>
        val r: MOption[State.Claim] = postStateClaimLetOr(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
      case o: State.Claim.Let.Imply =>
        val r: MOption[State.Claim] = postStateClaimLetImply(o) match {
         case MSome(result: State.Claim) => MSome[State.Claim](result)
         case MSome(_) => halt("Can only produce object of type State.Claim")
         case _ => MNone[State.Claim]()
        }
        return r
    }
  }

  def postStateClaimLabel(o: State.Claim.Label): MOption[State.Claim] = {
    return PostResultStateClaimLabel
  }

  def postStateClaimProp(o: State.Claim.Prop): MOption[State.Claim] = {
    return PostResultStateClaimProp
  }

  def postStateClaimAnd(o: State.Claim.And): MOption[State.Claim.Composite] = {
    return PostResultStateClaimAnd
  }

  def postStateClaimOr(o: State.Claim.Or): MOption[State.Claim.Composite] = {
    return PostResultStateClaimOr
  }

  def postStateClaimImply(o: State.Claim.Imply): MOption[State.Claim.Composite] = {
    return PostResultStateClaimImply
  }

  def postStateClaimIf(o: State.Claim.If): MOption[State.Claim.Composite] = {
    return PostResultStateClaimIf
  }

  def postStateClaimDef(o: State.Claim.Def): MOption[State.Claim.Def] = {
    o match {
      case o: State.Claim.Def.SeqLit => return postStateClaimDefSeqLit(o)
      case o: State.Claim.Def.SeqStore => return postStateClaimDefSeqStore(o)
      case o: State.Claim.Def.FieldStore => return postStateClaimDefFieldStore(o)
      case o: State.Claim.Def.AdtLit => return postStateClaimDefAdtLit(o)
      case o: State.Claim.Def.Random => return postStateClaimDefRandom(o)
      case o: State.Claim.Let.CurrentName =>
        val r: MOption[State.Claim.Def] = postStateClaimLetCurrentName(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Name =>
        val r: MOption[State.Claim.Def] = postStateClaimLetName(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.CurrentId =>
        val r: MOption[State.Claim.Def] = postStateClaimLetCurrentId(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Id =>
        val r: MOption[State.Claim.Def] = postStateClaimLetId(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Eq =>
        val r: MOption[State.Claim.Def] = postStateClaimLetEq(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.TypeTest =>
        val r: MOption[State.Claim.Def] = postStateClaimLetTypeTest(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Quant =>
        val r: MOption[State.Claim.Def] = postStateClaimLetQuant(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Ite =>
        val r: MOption[State.Claim.Def] = postStateClaimLetIte(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Binary =>
        val r: MOption[State.Claim.Def] = postStateClaimLetBinary(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Unary =>
        val r: MOption[State.Claim.Def] = postStateClaimLetUnary(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.SeqLookup =>
        val r: MOption[State.Claim.Def] = postStateClaimLetSeqLookup(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.SeqInBound =>
        val r: MOption[State.Claim.Def] = postStateClaimLetSeqInBound(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.FieldLookup =>
        val r: MOption[State.Claim.Def] = postStateClaimLetFieldLookup(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.ProofFunApply =>
        val r: MOption[State.Claim.Def] = postStateClaimLetProofFunApply(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Apply =>
        val r: MOption[State.Claim.Def] = postStateClaimLetApply(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.IApply =>
        val r: MOption[State.Claim.Def] = postStateClaimLetIApply(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.TupleLit =>
        val r: MOption[State.Claim.Def] = postStateClaimLetTupleLit(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.And =>
        val r: MOption[State.Claim.Def] = postStateClaimLetAnd(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Or =>
        val r: MOption[State.Claim.Def] = postStateClaimLetOr(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
      case o: State.Claim.Let.Imply =>
        val r: MOption[State.Claim.Def] = postStateClaimLetImply(o) match {
         case MSome(result: State.Claim.Def) => MSome[State.Claim.Def](result)
         case MSome(_) => halt("Can only produce object of type State.Claim.Def")
         case _ => MNone[State.Claim.Def]()
        }
        return r
    }
  }

  def postStateClaimDefSeqLit(o: State.Claim.Def.SeqLit): MOption[State.Claim.Def] = {
    return PostResultStateClaimDefSeqLit
  }

  def postStateClaimDefSeqLitArg(o: State.Claim.Def.SeqLit.Arg): MOption[State.Claim.Def.SeqLit.Arg] = {
    return PostResultStateClaimDefSeqLitArg
  }

  def postStateClaimDefSeqStore(o: State.Claim.Def.SeqStore): MOption[State.Claim.Def] = {
    return PostResultStateClaimDefSeqStore
  }

  def postStateClaimDefFieldStore(o: State.Claim.Def.FieldStore): MOption[State.Claim.Def] = {
    return PostResultStateClaimDefFieldStore
  }

  def postStateClaimDefAdtLit(o: State.Claim.Def.AdtLit): MOption[State.Claim.Def] = {
    return PostResultStateClaimDefAdtLit
  }

  def postStateClaimDefRandom(o: State.Claim.Def.Random): MOption[State.Claim.Def] = {
    return PostResultStateClaimDefRandom
  }

  def postStateClaimLet(o: State.Claim.Let): MOption[State.Claim.Let] = {
    o match {
      case o: State.Claim.Let.CurrentName => return postStateClaimLetCurrentName(o)
      case o: State.Claim.Let.Name => return postStateClaimLetName(o)
      case o: State.Claim.Let.CurrentId => return postStateClaimLetCurrentId(o)
      case o: State.Claim.Let.Id => return postStateClaimLetId(o)
      case o: State.Claim.Let.Eq => return postStateClaimLetEq(o)
      case o: State.Claim.Let.TypeTest => return postStateClaimLetTypeTest(o)
      case o: State.Claim.Let.Quant => return postStateClaimLetQuant(o)
      case o: State.Claim.Let.Ite => return postStateClaimLetIte(o)
      case o: State.Claim.Let.Binary => return postStateClaimLetBinary(o)
      case o: State.Claim.Let.Unary => return postStateClaimLetUnary(o)
      case o: State.Claim.Let.SeqLookup => return postStateClaimLetSeqLookup(o)
      case o: State.Claim.Let.SeqInBound => return postStateClaimLetSeqInBound(o)
      case o: State.Claim.Let.FieldLookup => return postStateClaimLetFieldLookup(o)
      case o: State.Claim.Let.ProofFunApply => return postStateClaimLetProofFunApply(o)
      case o: State.Claim.Let.Apply => return postStateClaimLetApply(o)
      case o: State.Claim.Let.IApply => return postStateClaimLetIApply(o)
      case o: State.Claim.Let.TupleLit => return postStateClaimLetTupleLit(o)
      case o: State.Claim.Let.And => return postStateClaimLetAnd(o)
      case o: State.Claim.Let.Or => return postStateClaimLetOr(o)
      case o: State.Claim.Let.Imply => return postStateClaimLetImply(o)
    }
  }

  def postStateClaimLetCurrentName(o: State.Claim.Let.CurrentName): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetCurrentName
  }

  def postStateClaimLetName(o: State.Claim.Let.Name): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetName
  }

  def postStateClaimLetCurrentId(o: State.Claim.Let.CurrentId): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetCurrentId
  }

  def postStateClaimLetId(o: State.Claim.Let.Id): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetId
  }

  def postStateClaimLetEq(o: State.Claim.Let.Eq): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetEq
  }

  def postStateClaimLetTypeTest(o: State.Claim.Let.TypeTest): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetTypeTest
  }

  def postStateClaimLetQuantVar(o: State.Claim.Let.Quant.Var): MOption[State.Claim.Let.Quant.Var] = {
    o match {
      case o: State.Claim.Let.Quant.Var.Id => return postStateClaimLetQuantVarId(o)
      case o: State.Claim.Let.Quant.Var.Sym => return postStateClaimLetQuantVarSym(o)
    }
  }

  def postStateClaimLetQuantVarId(o: State.Claim.Let.Quant.Var.Id): MOption[State.Claim.Let.Quant.Var] = {
    return PostResultStateClaimLetQuantVarId
  }

  def postStateClaimLetQuantVarSym(o: State.Claim.Let.Quant.Var.Sym): MOption[State.Claim.Let.Quant.Var] = {
    return PostResultStateClaimLetQuantVarSym
  }

  def postStateClaimLetQuant(o: State.Claim.Let.Quant): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetQuant
  }

  def postStateClaimLetIte(o: State.Claim.Let.Ite): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetIte
  }

  def postStateClaimLetBinary(o: State.Claim.Let.Binary): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetBinary
  }

  def postStateClaimLetUnary(o: State.Claim.Let.Unary): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetUnary
  }

  def postStateClaimLetSeqLookup(o: State.Claim.Let.SeqLookup): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetSeqLookup
  }

  def postStateClaimLetSeqInBound(o: State.Claim.Let.SeqInBound): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetSeqInBound
  }

  def postStateClaimLetFieldLookup(o: State.Claim.Let.FieldLookup): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetFieldLookup
  }

  def postStateClaimLetProofFunApply(o: State.Claim.Let.ProofFunApply): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetProofFunApply
  }

  def postStateClaimLetApply(o: State.Claim.Let.Apply): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetApply
  }

  def postStateClaimLetIApply(o: State.Claim.Let.IApply): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetIApply
  }

  def postStateClaimLetTupleLit(o: State.Claim.Let.TupleLit): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetTupleLit
  }

  def postStateClaimLetAnd(o: State.Claim.Let.And): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetAnd
  }

  def postStateClaimLetOr(o: State.Claim.Let.Or): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetOr
  }

  def postStateClaimLetImply(o: State.Claim.Let.Imply): MOption[State.Claim.Let] = {
    return PostResultStateClaimLetImply
  }

  def postStateProofFun(o: State.ProofFun): MOption[State.ProofFun] = {
    return PostResultStateProofFun
  }

  def transformState(o: State): MOption[State] = {
    val preR: PreResult[State] = preState(o)
    val r: MOption[State] = if (preR.continu) {
      val o2: State = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[IS[Z, State.Claim]] = transformISZ(o2.claims, transformStateClaim _)
      if (hasChanged || r0.nonEmpty)
        MSome(o2(claims = r0.getOrElse(o2.claims)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State = r.getOrElse(o)
    val postR: MOption[State] = postState(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateValue(o: State.Value): MOption[State.Value] = {
    val preR: PreResult[State.Value] = preStateValue(o)
    val r: MOption[State.Value] = if (preR.continu) {
      val o2: State.Value = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[State.Value] = o2 match {
        case o2: State.Value.Unit =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.B =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.Z =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.C =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.F32 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.F64 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.R =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.String =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.Range =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S8 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S16 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S32 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S64 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U8 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U16 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U32 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U64 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.Enum =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.Sym =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Value = r.getOrElse(o)
    val postR: MOption[State.Value] = postStateValue(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateFun(o: State.Fun): MOption[State.Fun] = {
    val preR: PreResult[State.Fun] = preStateFun(o)
    val r: MOption[State.Fun] = if (preR.continu) {
      val o2: State.Fun = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[State.Fun] = o2 match {
        case o2: State.IFun =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.OFun =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Fun = r.getOrElse(o)
    val postR: MOption[State.Fun] = postStateFun(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateValueSubZ(o: State.Value.SubZ): MOption[State.Value.SubZ] = {
    val preR: PreResult[State.Value.SubZ] = preStateValueSubZ(o)
    val r: MOption[State.Value.SubZ] = if (preR.continu) {
      val o2: State.Value.SubZ = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[State.Value.SubZ] = o2 match {
        case o2: State.Value.Range =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S8 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S16 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S32 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.S64 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U8 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U16 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U32 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Value.U64 =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Value.SubZ = r.getOrElse(o)
    val postR: MOption[State.Value.SubZ] = postStateValueSubZ(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateClaim(o: State.Claim): MOption[State.Claim] = {
    val preR: PreResult[State.Claim] = preStateClaim(o)
    val r: MOption[State.Claim] = if (preR.continu) {
      val o2: State.Claim = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[State.Claim] = o2 match {
        case o2: State.Claim.Label =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Claim.Prop =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.value)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(value = r0.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.And =>
          val r0: MOption[IS[Z, State.Claim]] = transformISZ(o2.claims, transformStateClaim _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(claims = r0.getOrElse(o2.claims)))
          else
            MNone()
        case o2: State.Claim.Or =>
          val r0: MOption[IS[Z, State.Claim]] = transformISZ(o2.claims, transformStateClaim _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(claims = r0.getOrElse(o2.claims)))
          else
            MNone()
        case o2: State.Claim.Imply =>
          val r0: MOption[IS[Z, State.Claim]] = transformISZ(o2.claims, transformStateClaim _)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(claims = r0.getOrElse(o2.claims)))
          else
            MNone()
        case o2: State.Claim.If =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.cond)
          val r1: MOption[IS[Z, State.Claim]] = transformISZ(o2.tClaims, transformStateClaim _)
          val r2: MOption[IS[Z, State.Claim]] = transformISZ(o2.fClaims, transformStateClaim _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(cond = r0.getOrElse(o2.cond), tClaims = r1.getOrElse(o2.tClaims), fClaims = r2.getOrElse(o2.fClaims)))
          else
            MNone()
        case o2: State.Claim.Def.SeqLit =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Claim.Def.SeqLit.Arg]] = transformISZ(o2.args, transformStateClaimDefSeqLitArg _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Def.SeqStore =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          val r3: MOption[State.Value] = transformStateValue(o2.element)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty || r3.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index), element = r3.getOrElse(o2.element)))
          else
            MNone()
        case o2: State.Claim.Def.FieldStore =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.adt)
          val r2: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), adt = r1.getOrElse(o2.adt), value = r2.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Def.AdtLit =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Def.Random =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.CurrentName =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Name =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.CurrentId =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Id =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Eq =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.TypeTest =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.Quant =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Claim.Let.Quant.Var]] = transformISZ(o2.vars, transformStateClaimLetQuantVar _)
          val r2: MOption[IS[Z, State.Claim]] = transformISZ(o2.claims, transformStateClaim _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), vars = r1.getOrElse(o2.vars), claims = r2.getOrElse(o2.claims)))
          else
            MNone()
        case o2: State.Claim.Let.Ite =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.cond)
          val r2: MOption[State.Value] = transformStateValue(o2.left)
          val r3: MOption[State.Value] = transformStateValue(o2.right)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty || r3.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), cond = r1.getOrElse(o2.cond), left = r2.getOrElse(o2.left), right = r3.getOrElse(o2.right)))
          else
            MNone()
        case o2: State.Claim.Let.Binary =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.left)
          val r2: MOption[State.Value] = transformStateValue(o2.right)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), left = r1.getOrElse(o2.left), right = r2.getOrElse(o2.right)))
          else
            MNone()
        case o2: State.Claim.Let.Unary =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.SeqLookup =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index)))
          else
            MNone()
        case o2: State.Claim.Let.SeqInBound =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index)))
          else
            MNone()
        case o2: State.Claim.Let.FieldLookup =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.adt)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), adt = r1.getOrElse(o2.adt)))
          else
            MNone()
        case o2: State.Claim.Let.ProofFunApply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.ProofFun] = transformStateProofFun(o2.pf)
          val r2: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), pf = r1.getOrElse(o2.pf), args = r2.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Apply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.IApply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.o)
          val r2: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), o = r1.getOrElse(o2.o), args = r2.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.TupleLit =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.And =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Or =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Imply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Claim = r.getOrElse(o)
    val postR: MOption[State.Claim] = postStateClaim(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateClaimDef(o: State.Claim.Def): MOption[State.Claim.Def] = {
    val preR: PreResult[State.Claim.Def] = preStateClaimDef(o)
    val r: MOption[State.Claim.Def] = if (preR.continu) {
      val o2: State.Claim.Def = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[State.Claim.Def] = o2 match {
        case o2: State.Claim.Def.SeqLit =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Claim.Def.SeqLit.Arg]] = transformISZ(o2.args, transformStateClaimDefSeqLitArg _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Def.SeqStore =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          val r3: MOption[State.Value] = transformStateValue(o2.element)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty || r3.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index), element = r3.getOrElse(o2.element)))
          else
            MNone()
        case o2: State.Claim.Def.FieldStore =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.adt)
          val r2: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), adt = r1.getOrElse(o2.adt), value = r2.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Def.AdtLit =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Def.Random =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.CurrentName =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Name =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.CurrentId =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Id =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Eq =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.TypeTest =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.Quant =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Claim.Let.Quant.Var]] = transformISZ(o2.vars, transformStateClaimLetQuantVar _)
          val r2: MOption[IS[Z, State.Claim]] = transformISZ(o2.claims, transformStateClaim _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), vars = r1.getOrElse(o2.vars), claims = r2.getOrElse(o2.claims)))
          else
            MNone()
        case o2: State.Claim.Let.Ite =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.cond)
          val r2: MOption[State.Value] = transformStateValue(o2.left)
          val r3: MOption[State.Value] = transformStateValue(o2.right)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty || r3.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), cond = r1.getOrElse(o2.cond), left = r2.getOrElse(o2.left), right = r3.getOrElse(o2.right)))
          else
            MNone()
        case o2: State.Claim.Let.Binary =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.left)
          val r2: MOption[State.Value] = transformStateValue(o2.right)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), left = r1.getOrElse(o2.left), right = r2.getOrElse(o2.right)))
          else
            MNone()
        case o2: State.Claim.Let.Unary =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.SeqLookup =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index)))
          else
            MNone()
        case o2: State.Claim.Let.SeqInBound =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index)))
          else
            MNone()
        case o2: State.Claim.Let.FieldLookup =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.adt)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), adt = r1.getOrElse(o2.adt)))
          else
            MNone()
        case o2: State.Claim.Let.ProofFunApply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.ProofFun] = transformStateProofFun(o2.pf)
          val r2: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), pf = r1.getOrElse(o2.pf), args = r2.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Apply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.IApply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.o)
          val r2: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), o = r1.getOrElse(o2.o), args = r2.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.TupleLit =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.And =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Or =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Imply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Claim.Def = r.getOrElse(o)
    val postR: MOption[State.Claim.Def] = postStateClaimDef(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateClaimDefSeqLitArg(o: State.Claim.Def.SeqLit.Arg): MOption[State.Claim.Def.SeqLit.Arg] = {
    val preR: PreResult[State.Claim.Def.SeqLit.Arg] = preStateClaimDefSeqLitArg(o)
    val r: MOption[State.Claim.Def.SeqLit.Arg] = if (preR.continu) {
      val o2: State.Claim.Def.SeqLit.Arg = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: MOption[State.Value] = transformStateValue(o2.index)
      val r1: MOption[State.Value] = transformStateValue(o2.value)
      if (hasChanged || r0.nonEmpty || r1.nonEmpty)
        MSome(o2(index = r0.getOrElse(o2.index), value = r1.getOrElse(o2.value)))
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Claim.Def.SeqLit.Arg = r.getOrElse(o)
    val postR: MOption[State.Claim.Def.SeqLit.Arg] = postStateClaimDefSeqLitArg(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateClaimLet(o: State.Claim.Let): MOption[State.Claim.Let] = {
    val preR: PreResult[State.Claim.Let] = preStateClaimLet(o)
    val r: MOption[State.Claim.Let] = if (preR.continu) {
      val o2: State.Claim.Let = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[State.Claim.Let] = o2 match {
        case o2: State.Claim.Let.CurrentName =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Name =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.CurrentId =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Id =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
        case o2: State.Claim.Let.Eq =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.TypeTest =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.Quant =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Claim.Let.Quant.Var]] = transformISZ(o2.vars, transformStateClaimLetQuantVar _)
          val r2: MOption[IS[Z, State.Claim]] = transformISZ(o2.claims, transformStateClaim _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), vars = r1.getOrElse(o2.vars), claims = r2.getOrElse(o2.claims)))
          else
            MNone()
        case o2: State.Claim.Let.Ite =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.cond)
          val r2: MOption[State.Value] = transformStateValue(o2.left)
          val r3: MOption[State.Value] = transformStateValue(o2.right)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty || r3.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), cond = r1.getOrElse(o2.cond), left = r2.getOrElse(o2.left), right = r3.getOrElse(o2.right)))
          else
            MNone()
        case o2: State.Claim.Let.Binary =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.left)
          val r2: MOption[State.Value] = transformStateValue(o2.right)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), left = r1.getOrElse(o2.left), right = r2.getOrElse(o2.right)))
          else
            MNone()
        case o2: State.Claim.Let.Unary =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.value)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), value = r1.getOrElse(o2.value)))
          else
            MNone()
        case o2: State.Claim.Let.SeqLookup =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index)))
          else
            MNone()
        case o2: State.Claim.Let.SeqInBound =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.seq)
          val r2: MOption[State.Value] = transformStateValue(o2.index)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), seq = r1.getOrElse(o2.seq), index = r2.getOrElse(o2.index)))
          else
            MNone()
        case o2: State.Claim.Let.FieldLookup =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.adt)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), adt = r1.getOrElse(o2.adt)))
          else
            MNone()
        case o2: State.Claim.Let.ProofFunApply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.ProofFun] = transformStateProofFun(o2.pf)
          val r2: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), pf = r1.getOrElse(o2.pf), args = r2.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Apply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.IApply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[State.Value] = transformStateValue(o2.o)
          val r2: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty || r2.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), o = r1.getOrElse(o2.o), args = r2.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.TupleLit =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.And =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Or =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
        case o2: State.Claim.Let.Imply =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          val r1: MOption[IS[Z, State.Value]] = transformISZ(o2.args, transformStateValue _)
          if (hasChanged || r0.nonEmpty || r1.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym), args = r1.getOrElse(o2.args)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Claim.Let = r.getOrElse(o)
    val postR: MOption[State.Claim.Let] = postStateClaimLet(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateClaimLetQuantVar(o: State.Claim.Let.Quant.Var): MOption[State.Claim.Let.Quant.Var] = {
    val preR: PreResult[State.Claim.Let.Quant.Var] = preStateClaimLetQuantVar(o)
    val r: MOption[State.Claim.Let.Quant.Var] = if (preR.continu) {
      val o2: State.Claim.Let.Quant.Var = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: MOption[State.Claim.Let.Quant.Var] = o2 match {
        case o2: State.Claim.Let.Quant.Var.Id =>
          if (hasChanged)
            MSome(o2)
          else
            MNone()
        case o2: State.Claim.Let.Quant.Var.Sym =>
          val r0: MOption[State.Value.Sym] = transformStateValueSym(o2.sym)
          if (hasChanged || r0.nonEmpty)
            MSome(o2(sym = r0.getOrElse(o2.sym)))
          else
            MNone()
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Claim.Let.Quant.Var = r.getOrElse(o)
    val postR: MOption[State.Claim.Let.Quant.Var] = postStateClaimLetQuantVar(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateProofFun(o: State.ProofFun): MOption[State.ProofFun] = {
    val preR: PreResult[State.ProofFun] = preStateProofFun(o)
    val r: MOption[State.ProofFun] = if (preR.continu) {
      val o2: State.ProofFun = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.ProofFun = r.getOrElse(o)
    val postR: MOption[State.ProofFun] = postStateProofFun(o2)
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

  def transformStateValueSym(o: State.Value.Sym): MOption[State.Value.Sym] = {
    val preR: PreResult[State.Value.Sym] = preStateValueSym(o) match {
     case PreResult(continu, MSome(r: State.Value.Sym)) => PreResult(continu, MSome[State.Value.Sym](r))
     case PreResult(_, MSome(_)) => halt("Can only produce object of type State.Value.Sym")
     case PreResult(continu, _) => PreResult(continu, MNone[State.Value.Sym]())
    }
    val r: MOption[State.Value.Sym] = if (preR.continu) {
      val o2: State.Value.Sym = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        MSome(o2)
      else
        MNone()
    } else if (preR.resultOpt.nonEmpty) {
      MSome(preR.resultOpt.getOrElse(o))
    } else {
      MNone()
    }
    val hasChanged: B = r.nonEmpty
    val o2: State.Value.Sym = r.getOrElse(o)
    val postR: MOption[State.Value.Sym] = postStateValueSym(o2) match {
     case MSome(result: State.Value.Sym) => MSome[State.Value.Sym](result)
     case MSome(_) => halt("Can only produce object of type State.Value.Sym")
     case _ => MNone[State.Value.Sym]()
    }
    if (postR.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return MSome(o2)
    } else {
      return MNone()
    }
  }

}