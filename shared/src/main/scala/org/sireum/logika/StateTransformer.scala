// #Sireum
// @formatter:off

/*
 Copyright (c) 2017-2025, Robby, Kansas State University
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

object StateTransformer {

  @datatype class PreResult[Context, T](val ctx: Context,
                                        val continu: B,
                                        val resultOpt: Option[T])

  @datatype class TPostResult[Context, T](val ctx: Context,
                                          val resultOpt: Option[T])

  @sig trait PrePost[Context] {

    @pure def preState(ctx: Context, o: State): PreResult[Context, State] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValue(ctx: Context, o: State.Value): PreResult[Context, State.Value] = {
      o match {
        case o: State.Value.Unit => return preStateValueUnit(ctx, o)
        case o: State.Value.B => return preStateValueB(ctx, o)
        case o: State.Value.Z => return preStateValueZ(ctx, o)
        case o: State.Value.C => return preStateValueC(ctx, o)
        case o: State.Value.F32 => return preStateValueF32(ctx, o)
        case o: State.Value.F64 => return preStateValueF64(ctx, o)
        case o: State.Value.R => return preStateValueR(ctx, o)
        case o: State.Value.String => return preStateValueString(ctx, o)
        case o: State.Value.Range =>
          val r: PreResult[Context, State.Value] = preStateValueRange(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.S8 =>
          val r: PreResult[Context, State.Value] = preStateValueS8(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.S16 =>
          val r: PreResult[Context, State.Value] = preStateValueS16(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.S32 =>
          val r: PreResult[Context, State.Value] = preStateValueS32(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.S64 =>
          val r: PreResult[Context, State.Value] = preStateValueS64(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.U8 =>
          val r: PreResult[Context, State.Value] = preStateValueU8(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.U16 =>
          val r: PreResult[Context, State.Value] = preStateValueU16(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.U32 =>
          val r: PreResult[Context, State.Value] = preStateValueU32(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.U64 =>
          val r: PreResult[Context, State.Value] = preStateValueU64(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Value)) => PreResult(preCtx, continu, Some[State.Value](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value]())
          }
          return r
        case o: State.Value.Enum => return preStateValueEnum(ctx, o)
        case o: State.Value.Sym => return preStateValueSym(ctx, o)
      }
    }

    @pure def preStateFun(ctx: Context, o: State.Fun): PreResult[Context, State.Fun] = {
      o match {
        case o: State.IFun => return preStateIFun(ctx, o)
        case o: State.OFun => return preStateOFun(ctx, o)
      }
    }

    @pure def preStateIFun(ctx: Context, o: State.IFun): PreResult[Context, State.Fun] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateOFun(ctx: Context, o: State.OFun): PreResult[Context, State.Fun] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueUnit(ctx: Context, o: State.Value.Unit): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueB(ctx: Context, o: State.Value.B): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueZ(ctx: Context, o: State.Value.Z): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueC(ctx: Context, o: State.Value.C): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueF32(ctx: Context, o: State.Value.F32): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueF64(ctx: Context, o: State.Value.F64): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueR(ctx: Context, o: State.Value.R): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueString(ctx: Context, o: State.Value.String): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueSubZ(ctx: Context, o: State.Value.SubZ): PreResult[Context, State.Value.SubZ] = {
      o match {
        case o: State.Value.Range => return preStateValueRange(ctx, o)
        case o: State.Value.S8 => return preStateValueS8(ctx, o)
        case o: State.Value.S16 => return preStateValueS16(ctx, o)
        case o: State.Value.S32 => return preStateValueS32(ctx, o)
        case o: State.Value.S64 => return preStateValueS64(ctx, o)
        case o: State.Value.U8 => return preStateValueU8(ctx, o)
        case o: State.Value.U16 => return preStateValueU16(ctx, o)
        case o: State.Value.U32 => return preStateValueU32(ctx, o)
        case o: State.Value.U64 => return preStateValueU64(ctx, o)
      }
    }

    @pure def preStateValueRange(ctx: Context, o: State.Value.Range): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueS8(ctx: Context, o: State.Value.S8): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueS16(ctx: Context, o: State.Value.S16): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueS32(ctx: Context, o: State.Value.S32): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueS64(ctx: Context, o: State.Value.S64): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueU8(ctx: Context, o: State.Value.U8): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueU16(ctx: Context, o: State.Value.U16): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueU32(ctx: Context, o: State.Value.U32): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueU64(ctx: Context, o: State.Value.U64): PreResult[Context, State.Value.SubZ] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueEnum(ctx: Context, o: State.Value.Enum): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValueSym(ctx: Context, o: State.Value.Sym): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaim(ctx: Context, o: State.Claim): PreResult[Context, State.Claim] = {
      o match {
        case o: State.Claim.Label => return preStateClaimLabel(ctx, o)
        case o: State.Claim.Old => return preStateClaimOld(ctx, o)
        case o: State.Claim.Input => return preStateClaimInput(ctx, o)
        case o: State.Claim.Prop => return preStateClaimProp(ctx, o)
        case o: State.Claim.Eq => return preStateClaimEq(ctx, o)
        case o: State.Claim.And =>
          val r: PreResult[Context, State.Claim] = preStateClaimAnd(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Or =>
          val r: PreResult[Context, State.Claim] = preStateClaimOr(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Imply =>
          val r: PreResult[Context, State.Claim] = preStateClaimImply(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.If =>
          val r: PreResult[Context, State.Claim] = preStateClaimIf(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.AdtLit =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetAdtLit(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqLit =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetSeqLit(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.CurrentName =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetCurrentName(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqStore =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetSeqStore(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.FieldStore =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetFieldStore(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Random =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetRandom(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Name =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetName(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.CurrentId =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetCurrentId(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Id =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetId(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Def =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetDef(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.TypeTest =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetTypeTest(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Quant =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetQuant(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Ite =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetIte(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Binary =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetBinary(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Unary =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetUnary(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqLookup =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetSeqLookup(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqInBound =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetSeqInBound(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.FieldLookup =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetFieldLookup(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.ProofFunApply =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetProofFunApply(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Apply =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetApply(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.TupleLit =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetTupleLit(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.And =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetAnd(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Or =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetOr(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Imply =>
          val r: PreResult[Context, State.Claim] = preStateClaimLetImply(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Custom => return preStateClaimCustom(ctx, o)
      }
    }

    @pure def preStateClaimLabel(ctx: Context, o: State.Claim.Label): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimOld(ctx: Context, o: State.Claim.Old): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimInput(ctx: Context, o: State.Claim.Input): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimProp(ctx: Context, o: State.Claim.Prop): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimEq(ctx: Context, o: State.Claim.Eq): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimAnd(ctx: Context, o: State.Claim.And): PreResult[Context, State.Claim.Composite] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimOr(ctx: Context, o: State.Claim.Or): PreResult[Context, State.Claim.Composite] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimImply(ctx: Context, o: State.Claim.Imply): PreResult[Context, State.Claim.Composite] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimIf(ctx: Context, o: State.Claim.If): PreResult[Context, State.Claim.Composite] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLet(ctx: Context, o: State.Claim.Let): PreResult[Context, State.Claim.Let] = {
      o match {
        case o: State.Claim.Let.AdtLit => return preStateClaimLetAdtLit(ctx, o)
        case o: State.Claim.Let.SeqLit => return preStateClaimLetSeqLit(ctx, o)
        case o: State.Claim.Let.CurrentName => return preStateClaimLetCurrentName(ctx, o)
        case o: State.Claim.Let.SeqStore => return preStateClaimLetSeqStore(ctx, o)
        case o: State.Claim.Let.FieldStore => return preStateClaimLetFieldStore(ctx, o)
        case o: State.Claim.Let.Random => return preStateClaimLetRandom(ctx, o)
        case o: State.Claim.Let.Name => return preStateClaimLetName(ctx, o)
        case o: State.Claim.Let.CurrentId => return preStateClaimLetCurrentId(ctx, o)
        case o: State.Claim.Let.Id => return preStateClaimLetId(ctx, o)
        case o: State.Claim.Let.Def => return preStateClaimLetDef(ctx, o)
        case o: State.Claim.Let.TypeTest => return preStateClaimLetTypeTest(ctx, o)
        case o: State.Claim.Let.Quant => return preStateClaimLetQuant(ctx, o)
        case o: State.Claim.Let.Ite => return preStateClaimLetIte(ctx, o)
        case o: State.Claim.Let.Binary => return preStateClaimLetBinary(ctx, o)
        case o: State.Claim.Let.Unary => return preStateClaimLetUnary(ctx, o)
        case o: State.Claim.Let.SeqLookup => return preStateClaimLetSeqLookup(ctx, o)
        case o: State.Claim.Let.SeqInBound => return preStateClaimLetSeqInBound(ctx, o)
        case o: State.Claim.Let.FieldLookup => return preStateClaimLetFieldLookup(ctx, o)
        case o: State.Claim.Let.ProofFunApply => return preStateClaimLetProofFunApply(ctx, o)
        case o: State.Claim.Let.Apply => return preStateClaimLetApply(ctx, o)
        case o: State.Claim.Let.TupleLit => return preStateClaimLetTupleLit(ctx, o)
        case o: State.Claim.Let.And => return preStateClaimLetAnd(ctx, o)
        case o: State.Claim.Let.Or => return preStateClaimLetOr(ctx, o)
        case o: State.Claim.Let.Imply => return preStateClaimLetImply(ctx, o)
      }
    }

    @pure def preStateClaimLetAdtLit(ctx: Context, o: State.Claim.Let.AdtLit): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetSeqLit(ctx: Context, o: State.Claim.Let.SeqLit): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetSeqLitArg(ctx: Context, o: State.Claim.Let.SeqLit.Arg): PreResult[Context, State.Claim.Let.SeqLit.Arg] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetCurrentName(ctx: Context, o: State.Claim.Let.CurrentName): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetSeqStore(ctx: Context, o: State.Claim.Let.SeqStore): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetFieldStore(ctx: Context, o: State.Claim.Let.FieldStore): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetRandom(ctx: Context, o: State.Claim.Let.Random): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetName(ctx: Context, o: State.Claim.Let.Name): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetCurrentId(ctx: Context, o: State.Claim.Let.CurrentId): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetId(ctx: Context, o: State.Claim.Let.Id): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetDef(ctx: Context, o: State.Claim.Let.Def): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetTypeTest(ctx: Context, o: State.Claim.Let.TypeTest): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetQuantVar(ctx: Context, o: State.Claim.Let.Quant.Var): PreResult[Context, State.Claim.Let.Quant.Var] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetQuant(ctx: Context, o: State.Claim.Let.Quant): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetIte(ctx: Context, o: State.Claim.Let.Ite): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetBinary(ctx: Context, o: State.Claim.Let.Binary): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetUnary(ctx: Context, o: State.Claim.Let.Unary): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetSeqLookup(ctx: Context, o: State.Claim.Let.SeqLookup): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetSeqInBound(ctx: Context, o: State.Claim.Let.SeqInBound): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetFieldLookup(ctx: Context, o: State.Claim.Let.FieldLookup): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetProofFunApply(ctx: Context, o: State.Claim.Let.ProofFunApply): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetApply(ctx: Context, o: State.Claim.Let.Apply): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetTupleLit(ctx: Context, o: State.Claim.Let.TupleLit): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetAnd(ctx: Context, o: State.Claim.Let.And): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetOr(ctx: Context, o: State.Claim.Let.Or): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimLetImply(ctx: Context, o: State.Claim.Let.Imply): PreResult[Context, State.Claim.Let] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimCustom(ctx: Context, o: State.Claim.Custom): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimData(ctx: Context, o: State.Claim.Data): PreResult[Context, State.Claim.Data] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateProofFun(ctx: Context, o: State.ProofFun): PreResult[Context, State.ProofFun] = {
      return PreResult(ctx, T, None())
    }

    @pure def postState(ctx: Context, o: State): TPostResult[Context, State] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValue(ctx: Context, o: State.Value): TPostResult[Context, State.Value] = {
      o match {
        case o: State.Value.Unit => return postStateValueUnit(ctx, o)
        case o: State.Value.B => return postStateValueB(ctx, o)
        case o: State.Value.Z => return postStateValueZ(ctx, o)
        case o: State.Value.C => return postStateValueC(ctx, o)
        case o: State.Value.F32 => return postStateValueF32(ctx, o)
        case o: State.Value.F64 => return postStateValueF64(ctx, o)
        case o: State.Value.R => return postStateValueR(ctx, o)
        case o: State.Value.String => return postStateValueString(ctx, o)
        case o: State.Value.Range =>
          val r: TPostResult[Context, State.Value] = postStateValueRange(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.S8 =>
          val r: TPostResult[Context, State.Value] = postStateValueS8(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.S16 =>
          val r: TPostResult[Context, State.Value] = postStateValueS16(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.S32 =>
          val r: TPostResult[Context, State.Value] = postStateValueS32(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.S64 =>
          val r: TPostResult[Context, State.Value] = postStateValueS64(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.U8 =>
          val r: TPostResult[Context, State.Value] = postStateValueU8(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.U16 =>
          val r: TPostResult[Context, State.Value] = postStateValueU16(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.U32 =>
          val r: TPostResult[Context, State.Value] = postStateValueU32(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.U64 =>
          val r: TPostResult[Context, State.Value] = postStateValueU64(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Value)) => TPostResult(postCtx, Some[State.Value](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value]())
          }
          return r
        case o: State.Value.Enum => return postStateValueEnum(ctx, o)
        case o: State.Value.Sym => return postStateValueSym(ctx, o)
      }
    }

    @pure def postStateFun(ctx: Context, o: State.Fun): TPostResult[Context, State.Fun] = {
      o match {
        case o: State.IFun => return postStateIFun(ctx, o)
        case o: State.OFun => return postStateOFun(ctx, o)
      }
    }

    @pure def postStateIFun(ctx: Context, o: State.IFun): TPostResult[Context, State.Fun] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateOFun(ctx: Context, o: State.OFun): TPostResult[Context, State.Fun] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueUnit(ctx: Context, o: State.Value.Unit): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueB(ctx: Context, o: State.Value.B): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueZ(ctx: Context, o: State.Value.Z): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueC(ctx: Context, o: State.Value.C): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueF32(ctx: Context, o: State.Value.F32): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueF64(ctx: Context, o: State.Value.F64): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueR(ctx: Context, o: State.Value.R): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueString(ctx: Context, o: State.Value.String): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueSubZ(ctx: Context, o: State.Value.SubZ): TPostResult[Context, State.Value.SubZ] = {
      o match {
        case o: State.Value.Range => return postStateValueRange(ctx, o)
        case o: State.Value.S8 => return postStateValueS8(ctx, o)
        case o: State.Value.S16 => return postStateValueS16(ctx, o)
        case o: State.Value.S32 => return postStateValueS32(ctx, o)
        case o: State.Value.S64 => return postStateValueS64(ctx, o)
        case o: State.Value.U8 => return postStateValueU8(ctx, o)
        case o: State.Value.U16 => return postStateValueU16(ctx, o)
        case o: State.Value.U32 => return postStateValueU32(ctx, o)
        case o: State.Value.U64 => return postStateValueU64(ctx, o)
      }
    }

    @pure def postStateValueRange(ctx: Context, o: State.Value.Range): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueS8(ctx: Context, o: State.Value.S8): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueS16(ctx: Context, o: State.Value.S16): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueS32(ctx: Context, o: State.Value.S32): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueS64(ctx: Context, o: State.Value.S64): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueU8(ctx: Context, o: State.Value.U8): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueU16(ctx: Context, o: State.Value.U16): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueU32(ctx: Context, o: State.Value.U32): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueU64(ctx: Context, o: State.Value.U64): TPostResult[Context, State.Value.SubZ] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueEnum(ctx: Context, o: State.Value.Enum): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValueSym(ctx: Context, o: State.Value.Sym): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaim(ctx: Context, o: State.Claim): TPostResult[Context, State.Claim] = {
      o match {
        case o: State.Claim.Label => return postStateClaimLabel(ctx, o)
        case o: State.Claim.Old => return postStateClaimOld(ctx, o)
        case o: State.Claim.Input => return postStateClaimInput(ctx, o)
        case o: State.Claim.Prop => return postStateClaimProp(ctx, o)
        case o: State.Claim.Eq => return postStateClaimEq(ctx, o)
        case o: State.Claim.And =>
          val r: TPostResult[Context, State.Claim] = postStateClaimAnd(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Or =>
          val r: TPostResult[Context, State.Claim] = postStateClaimOr(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Imply =>
          val r: TPostResult[Context, State.Claim] = postStateClaimImply(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.If =>
          val r: TPostResult[Context, State.Claim] = postStateClaimIf(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.AdtLit =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetAdtLit(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqLit =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetSeqLit(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.CurrentName =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetCurrentName(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqStore =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetSeqStore(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.FieldStore =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetFieldStore(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Random =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetRandom(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Name =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetName(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.CurrentId =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetCurrentId(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Id =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetId(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Def =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetDef(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.TypeTest =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetTypeTest(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Quant =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetQuant(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Ite =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetIte(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Binary =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetBinary(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Unary =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetUnary(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqLookup =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetSeqLookup(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.SeqInBound =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetSeqInBound(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.FieldLookup =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetFieldLookup(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.ProofFunApply =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetProofFunApply(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Apply =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetApply(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.TupleLit =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetTupleLit(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.And =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetAnd(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Or =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetOr(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Let.Imply =>
          val r: TPostResult[Context, State.Claim] = postStateClaimLetImply(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Custom => return postStateClaimCustom(ctx, o)
      }
    }

    @pure def postStateClaimLabel(ctx: Context, o: State.Claim.Label): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimOld(ctx: Context, o: State.Claim.Old): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimInput(ctx: Context, o: State.Claim.Input): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimProp(ctx: Context, o: State.Claim.Prop): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimEq(ctx: Context, o: State.Claim.Eq): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimAnd(ctx: Context, o: State.Claim.And): TPostResult[Context, State.Claim.Composite] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimOr(ctx: Context, o: State.Claim.Or): TPostResult[Context, State.Claim.Composite] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimImply(ctx: Context, o: State.Claim.Imply): TPostResult[Context, State.Claim.Composite] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimIf(ctx: Context, o: State.Claim.If): TPostResult[Context, State.Claim.Composite] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLet(ctx: Context, o: State.Claim.Let): TPostResult[Context, State.Claim.Let] = {
      o match {
        case o: State.Claim.Let.AdtLit => return postStateClaimLetAdtLit(ctx, o)
        case o: State.Claim.Let.SeqLit => return postStateClaimLetSeqLit(ctx, o)
        case o: State.Claim.Let.CurrentName => return postStateClaimLetCurrentName(ctx, o)
        case o: State.Claim.Let.SeqStore => return postStateClaimLetSeqStore(ctx, o)
        case o: State.Claim.Let.FieldStore => return postStateClaimLetFieldStore(ctx, o)
        case o: State.Claim.Let.Random => return postStateClaimLetRandom(ctx, o)
        case o: State.Claim.Let.Name => return postStateClaimLetName(ctx, o)
        case o: State.Claim.Let.CurrentId => return postStateClaimLetCurrentId(ctx, o)
        case o: State.Claim.Let.Id => return postStateClaimLetId(ctx, o)
        case o: State.Claim.Let.Def => return postStateClaimLetDef(ctx, o)
        case o: State.Claim.Let.TypeTest => return postStateClaimLetTypeTest(ctx, o)
        case o: State.Claim.Let.Quant => return postStateClaimLetQuant(ctx, o)
        case o: State.Claim.Let.Ite => return postStateClaimLetIte(ctx, o)
        case o: State.Claim.Let.Binary => return postStateClaimLetBinary(ctx, o)
        case o: State.Claim.Let.Unary => return postStateClaimLetUnary(ctx, o)
        case o: State.Claim.Let.SeqLookup => return postStateClaimLetSeqLookup(ctx, o)
        case o: State.Claim.Let.SeqInBound => return postStateClaimLetSeqInBound(ctx, o)
        case o: State.Claim.Let.FieldLookup => return postStateClaimLetFieldLookup(ctx, o)
        case o: State.Claim.Let.ProofFunApply => return postStateClaimLetProofFunApply(ctx, o)
        case o: State.Claim.Let.Apply => return postStateClaimLetApply(ctx, o)
        case o: State.Claim.Let.TupleLit => return postStateClaimLetTupleLit(ctx, o)
        case o: State.Claim.Let.And => return postStateClaimLetAnd(ctx, o)
        case o: State.Claim.Let.Or => return postStateClaimLetOr(ctx, o)
        case o: State.Claim.Let.Imply => return postStateClaimLetImply(ctx, o)
      }
    }

    @pure def postStateClaimLetAdtLit(ctx: Context, o: State.Claim.Let.AdtLit): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetSeqLit(ctx: Context, o: State.Claim.Let.SeqLit): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetSeqLitArg(ctx: Context, o: State.Claim.Let.SeqLit.Arg): TPostResult[Context, State.Claim.Let.SeqLit.Arg] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetCurrentName(ctx: Context, o: State.Claim.Let.CurrentName): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetSeqStore(ctx: Context, o: State.Claim.Let.SeqStore): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetFieldStore(ctx: Context, o: State.Claim.Let.FieldStore): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetRandom(ctx: Context, o: State.Claim.Let.Random): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetName(ctx: Context, o: State.Claim.Let.Name): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetCurrentId(ctx: Context, o: State.Claim.Let.CurrentId): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetId(ctx: Context, o: State.Claim.Let.Id): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetDef(ctx: Context, o: State.Claim.Let.Def): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetTypeTest(ctx: Context, o: State.Claim.Let.TypeTest): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetQuantVar(ctx: Context, o: State.Claim.Let.Quant.Var): TPostResult[Context, State.Claim.Let.Quant.Var] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetQuant(ctx: Context, o: State.Claim.Let.Quant): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetIte(ctx: Context, o: State.Claim.Let.Ite): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetBinary(ctx: Context, o: State.Claim.Let.Binary): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetUnary(ctx: Context, o: State.Claim.Let.Unary): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetSeqLookup(ctx: Context, o: State.Claim.Let.SeqLookup): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetSeqInBound(ctx: Context, o: State.Claim.Let.SeqInBound): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetFieldLookup(ctx: Context, o: State.Claim.Let.FieldLookup): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetProofFunApply(ctx: Context, o: State.Claim.Let.ProofFunApply): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetApply(ctx: Context, o: State.Claim.Let.Apply): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetTupleLit(ctx: Context, o: State.Claim.Let.TupleLit): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetAnd(ctx: Context, o: State.Claim.Let.And): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetOr(ctx: Context, o: State.Claim.Let.Or): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimLetImply(ctx: Context, o: State.Claim.Let.Imply): TPostResult[Context, State.Claim.Let] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimCustom(ctx: Context, o: State.Claim.Custom): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimData(ctx: Context, o: State.Claim.Data): TPostResult[Context, State.Claim.Data] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateProofFun(ctx: Context, o: State.ProofFun): TPostResult[Context, State.ProofFun] = {
      return TPostResult(ctx, None())
    }

  }

  @pure def transformISZ[Context, T](ctx: Context, s: IS[Z, T], f: (Context, T) => TPostResult[Context, T] @pure): TPostResult[Context, IS[Z, T]] = {
    val s2: MS[Z, T] = s.toMS
    var changed: B = F
    var ctxi = ctx
    for (i <- s2.indices) {
      val e: T = s(i)
      val r: TPostResult[Context, T] = f(ctxi, e)
      ctxi = r.ctx
      changed = changed || r.resultOpt.nonEmpty
      s2(i) = r.resultOpt.getOrElse(e)
    }
    if (changed) {
      return TPostResult(ctxi, Some(s2.toIS))
    } else {
      return TPostResult[Context, IS[Z, T]](ctxi, None[IS[Z, T]]())
    }
  }

}

import StateTransformer._

@datatype class StateTransformer[Context](val pp: PrePost[Context]) {

  @pure def transformState(ctx: Context, o: State): TPostResult[Context, State] = {
    val preR: PreResult[Context, State] = pp.preState(ctx, o)
    val r: TPostResult[Context, State] = if (preR.continu) {
      val o2: State = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(preR.ctx, o2.claims, transformStateClaim _)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(claims = r0.resultOpt.getOrElse(o2.claims))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State] = pp.postState(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateValue(ctx: Context, o: State.Value): TPostResult[Context, State.Value] = {
    val preR: PreResult[Context, State.Value] = pp.preStateValue(ctx, o)
    val r: TPostResult[Context, State.Value] = if (preR.continu) {
      val o2: State.Value = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, State.Value] = o2 match {
        case o2: State.Value.Unit =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.B =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.Z =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.C =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.F32 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.F64 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.R =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.String =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.Range =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S8 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S16 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S32 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S64 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U8 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U16 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U32 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U64 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.Enum =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.Sym =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Value = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Value] = pp.postStateValue(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateFun(ctx: Context, o: State.Fun): TPostResult[Context, State.Fun] = {
    val preR: PreResult[Context, State.Fun] = pp.preStateFun(ctx, o)
    val r: TPostResult[Context, State.Fun] = if (preR.continu) {
      val o2: State.Fun = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, State.Fun] = o2 match {
        case o2: State.IFun =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.OFun =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Fun = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Fun] = pp.postStateFun(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateValueSubZ(ctx: Context, o: State.Value.SubZ): TPostResult[Context, State.Value.SubZ] = {
    val preR: PreResult[Context, State.Value.SubZ] = pp.preStateValueSubZ(ctx, o)
    val r: TPostResult[Context, State.Value.SubZ] = if (preR.continu) {
      val o2: State.Value.SubZ = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, State.Value.SubZ] = o2 match {
        case o2: State.Value.Range =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S8 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S16 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S32 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.S64 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U8 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U16 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U32 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Value.U64 =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Value.SubZ = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Value.SubZ] = pp.postStateValueSubZ(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateClaim(ctx: Context, o: State.Claim): TPostResult[Context, State.Claim] = {
    val preR: PreResult[Context, State.Claim] = pp.preStateClaim(ctx, o)
    val r: TPostResult[Context, State.Claim] = if (preR.continu) {
      val o2: State.Claim = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, State.Claim] = o2 match {
        case o2: State.Claim.Label =>
          if (hasChanged)
            TPostResult(preR.ctx, Some(o2))
          else
            TPostResult(preR.ctx, None())
        case o2: State.Claim.Old =>
          val r0: TPostResult[Context, State.Value] = transformStateValue(preR.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(value = r0.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Input =>
          val r0: TPostResult[Context, State.Value] = transformStateValue(preR.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(value = r0.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Prop =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(value = r0.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Eq =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.v1)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.v2)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(v1 = r0.resultOpt.getOrElse(o2.v1), v2 = r1.resultOpt.getOrElse(o2.v2))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.And =>
          val r0: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(preR.ctx, o2.claims, transformStateClaim _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(claims = r0.resultOpt.getOrElse(o2.claims))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Or =>
          val r0: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(preR.ctx, o2.claims, transformStateClaim _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(claims = r0.resultOpt.getOrElse(o2.claims))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Imply =>
          val r0: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(preR.ctx, o2.claims, transformStateClaim _)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(claims = r0.resultOpt.getOrElse(o2.claims))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.If =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.cond)
          val r1: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(r0.ctx, o2.tClaims, transformStateClaim _)
          val r2: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(r1.ctx, o2.fClaims, transformStateClaim _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(cond = r0.resultOpt.getOrElse(o2.cond), tClaims = r1.resultOpt.getOrElse(o2.tClaims), fClaims = r2.resultOpt.getOrElse(o2.fClaims))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.AdtLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.SeqLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Claim.Let.SeqLit.Arg]] = transformISZ(r0.ctx, o2.args, transformStateClaimLetSeqLitArg _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.CurrentName =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.SeqStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          val r3: TPostResult[Context, State.Value] = transformStateValue(r2.ctx, o2.element)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty || r3.resultOpt.nonEmpty)
            TPostResult(r3.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index), element = r3.resultOpt.getOrElse(o2.element))))
          else
            TPostResult(r3.ctx, None())
        case o2: State.Claim.Let.FieldStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt), value = r2.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Random =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.Name =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.CurrentId =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.Id =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.Def =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.TypeTest =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.Quant =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Claim.Let.Quant.Var]] = transformISZ(r0.ctx, o2.vars, transformStateClaimLetQuantVar _)
          val r2: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(r1.ctx, o2.claims, transformStateClaim _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), vars = r1.resultOpt.getOrElse(o2.vars), claims = r2.resultOpt.getOrElse(o2.claims))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Ite =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.cond)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.left)
          val r3: TPostResult[Context, State.Value] = transformStateValue(r2.ctx, o2.right)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty || r3.resultOpt.nonEmpty)
            TPostResult(r3.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), cond = r1.resultOpt.getOrElse(o2.cond), left = r2.resultOpt.getOrElse(o2.left), right = r3.resultOpt.getOrElse(o2.right))))
          else
            TPostResult(r3.ctx, None())
        case o2: State.Claim.Let.Binary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.left)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.right)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), left = r1.resultOpt.getOrElse(o2.left), right = r2.resultOpt.getOrElse(o2.right))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Unary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.SeqLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.SeqInBound =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.FieldLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.ProofFunApply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.ProofFun] = transformStateProofFun(r0.ctx, o2.pf)
          val r2: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r1.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), pf = r1.resultOpt.getOrElse(o2.pf), args = r2.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Apply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.TupleLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.And =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.Or =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.Imply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Custom =>
          val r0: TPostResult[Context, State.Claim.Data] = transformStateClaimData(preR.ctx, o2.data)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(data = r0.resultOpt.getOrElse(o2.data))))
          else
            TPostResult(r0.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Claim = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Claim] = pp.postStateClaim(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateClaimLet(ctx: Context, o: State.Claim.Let): TPostResult[Context, State.Claim.Let] = {
    val preR: PreResult[Context, State.Claim.Let] = pp.preStateClaimLet(ctx, o)
    val r: TPostResult[Context, State.Claim.Let] = if (preR.continu) {
      val o2: State.Claim.Let = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, State.Claim.Let] = o2 match {
        case o2: State.Claim.Let.AdtLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.SeqLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Claim.Let.SeqLit.Arg]] = transformISZ(r0.ctx, o2.args, transformStateClaimLetSeqLitArg _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.CurrentName =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.SeqStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          val r3: TPostResult[Context, State.Value] = transformStateValue(r2.ctx, o2.element)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty || r3.resultOpt.nonEmpty)
            TPostResult(r3.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index), element = r3.resultOpt.getOrElse(o2.element))))
          else
            TPostResult(r3.ctx, None())
        case o2: State.Claim.Let.FieldStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt), value = r2.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Random =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.Name =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.CurrentId =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.Id =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Let.Def =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.TypeTest =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.Quant =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Claim.Let.Quant.Var]] = transformISZ(r0.ctx, o2.vars, transformStateClaimLetQuantVar _)
          val r2: TPostResult[Context, IS[Z, State.Claim]] = transformISZ(r1.ctx, o2.claims, transformStateClaim _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), vars = r1.resultOpt.getOrElse(o2.vars), claims = r2.resultOpt.getOrElse(o2.claims))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Ite =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.cond)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.left)
          val r3: TPostResult[Context, State.Value] = transformStateValue(r2.ctx, o2.right)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty || r3.resultOpt.nonEmpty)
            TPostResult(r3.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), cond = r1.resultOpt.getOrElse(o2.cond), left = r2.resultOpt.getOrElse(o2.left), right = r3.resultOpt.getOrElse(o2.right))))
          else
            TPostResult(r3.ctx, None())
        case o2: State.Claim.Let.Binary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.left)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.right)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), left = r1.resultOpt.getOrElse(o2.left), right = r2.resultOpt.getOrElse(o2.right))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Unary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.SeqLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.SeqInBound =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.FieldLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.ProofFunApply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.ProofFun] = transformStateProofFun(r0.ctx, o2.pf)
          val r2: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r1.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), pf = r1.resultOpt.getOrElse(o2.pf), args = r2.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Let.Apply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.TupleLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.And =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.Or =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Let.Imply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
      }
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Claim.Let = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Claim.Let] = pp.postStateClaimLet(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateClaimLetSeqLitArg(ctx: Context, o: State.Claim.Let.SeqLit.Arg): TPostResult[Context, State.Claim.Let.SeqLit.Arg] = {
    val preR: PreResult[Context, State.Claim.Let.SeqLit.Arg] = pp.preStateClaimLetSeqLitArg(ctx, o)
    val r: TPostResult[Context, State.Claim.Let.SeqLit.Arg] = if (preR.continu) {
      val o2: State.Claim.Let.SeqLit.Arg = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, State.Value] = transformStateValue(preR.ctx, o2.index)
      val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
      if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
        TPostResult(r1.ctx, Some(o2(index = r0.resultOpt.getOrElse(o2.index), value = r1.resultOpt.getOrElse(o2.value))))
      else
        TPostResult(r1.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Claim.Let.SeqLit.Arg = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Claim.Let.SeqLit.Arg] = pp.postStateClaimLetSeqLitArg(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateClaimLetQuantVar(ctx: Context, o: State.Claim.Let.Quant.Var): TPostResult[Context, State.Claim.Let.Quant.Var] = {
    val preR: PreResult[Context, State.Claim.Let.Quant.Var] = pp.preStateClaimLetQuantVar(ctx, o)
    val r: TPostResult[Context, State.Claim.Let.Quant.Var] = if (preR.continu) {
      val o2: State.Claim.Let.Quant.Var = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Claim.Let.Quant.Var = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Claim.Let.Quant.Var] = pp.postStateClaimLetQuantVar(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateClaimData(ctx: Context, o: State.Claim.Data): TPostResult[Context, State.Claim.Data] = {
    val preR: PreResult[Context, State.Claim.Data] = pp.preStateClaimData(ctx, o)
    val r: TPostResult[Context, State.Claim.Data] = if (preR.continu) {
      val o2: State.Claim.Data = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, State.Claim.Data] = TPostResult(ctx, None())
      rOpt
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Claim.Data = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Claim.Data] = pp.postStateClaimData(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateProofFun(ctx: Context, o: State.ProofFun): TPostResult[Context, State.ProofFun] = {
    val preR: PreResult[Context, State.ProofFun] = pp.preStateProofFun(ctx, o)
    val r: TPostResult[Context, State.ProofFun] = if (preR.continu) {
      val o2: State.ProofFun = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.ProofFun = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.ProofFun] = pp.postStateProofFun(r.ctx, o2)
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

  @pure def transformStateValueSym(ctx: Context, o: State.Value.Sym): TPostResult[Context, State.Value.Sym] = {
    val preR: PreResult[Context, State.Value.Sym] = pp.preStateValueSym(ctx, o) match {
     case PreResult(preCtx, continu, Some(r: State.Value.Sym)) => PreResult(preCtx, continu, Some[State.Value.Sym](r))
     case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Value.Sym")
     case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Value.Sym]())
    }
    val r: TPostResult[Context, State.Value.Sym] = if (preR.continu) {
      val o2: State.Value.Sym = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      if (hasChanged)
        TPostResult(preR.ctx, Some(o2))
      else
        TPostResult(preR.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Value.Sym = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Value.Sym] = pp.postStateValueSym(r.ctx, o2) match {
     case TPostResult(postCtx, Some(result: State.Value.Sym)) => TPostResult(postCtx, Some[State.Value.Sym](result))
     case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Value.Sym")
     case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Value.Sym]())
    }
    if (postR.resultOpt.nonEmpty) {
      return postR
    } else if (hasChanged) {
      return TPostResult(postR.ctx, Some(o2))
    } else {
      return TPostResult(postR.ctx, None())
    }
  }

}