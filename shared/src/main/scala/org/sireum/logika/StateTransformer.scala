// #Sireum
// @formatter:off

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

// This file is auto-generated from State.scala

package org.sireum.logika

import org.sireum._

object StateTransformer {

  @datatype class PreResult[Context, T](ctx: Context,
                                        continu: B,
                                        resultOpt: Option[T])

  @datatype class TPostResult[Context, T](ctx: Context,
                                     resultOpt: Option[T])

  @sig trait PrePost[Context] {

    @pure def preState(ctx: Context, o: State): PreResult[Context, State] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateValue(ctx: Context, o: State.Value): PreResult[Context, State.Value] = {
      o match {
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

    @pure def preStateValueSym(ctx: Context, o: State.Value.Sym): PreResult[Context, State.Value] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaim(ctx: Context, o: State.Claim): PreResult[Context, State.Claim] = {
      o match {
        case o: State.Claim.And => return preStateClaimAnd(ctx, o)
        case o: State.Claim.Or => return preStateClaimOr(ctx, o)
        case o: State.Claim.Imply => return preStateClaimImply(ctx, o)
        case o: State.Claim.Quant => return preStateClaimQuant(ctx, o)
        case o: State.Claim.Neg => return preStateClaimNeg(ctx, o)
        case o: State.Claim.Prop => return preStateClaimProp(ctx, o)
        case o: State.Claim.If => return preStateClaimIf(ctx, o)
        case o: State.Claim.Def.CurrentName =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefCurrentName(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Name =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefName(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.CurrentId =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefCurrentId(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Id =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefId(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Eq =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefEq(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Binary =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefBinary(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Unary =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefUnary(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.SeqStore =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefSeqStore(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.SeqLookup =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefSeqLookup(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.FieldStore =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefFieldStore(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.FieldLookup =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefFieldLookup(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Apply =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefApply(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.IApply =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefIApply(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.AdtLit =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefAdtLit(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.SeqLit =>
          val r: PreResult[Context, State.Claim] = preStateClaimDefSeqLit(ctx, o) match {
           case PreResult(preCtx, continu, Some(r: State.Claim)) => PreResult(preCtx, continu, Some[State.Claim](r))
           case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim")
           case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim]())
          }
          return r
      }
    }

    @pure def preStateClaimAnd(ctx: Context, o: State.Claim.And): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimOr(ctx: Context, o: State.Claim.Or): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimImply(ctx: Context, o: State.Claim.Imply): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimQuant(ctx: Context, o: State.Claim.Quant): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimNeg(ctx: Context, o: State.Claim.Neg): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimProp(ctx: Context, o: State.Claim.Prop): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimIf(ctx: Context, o: State.Claim.If): PreResult[Context, State.Claim] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDef(ctx: Context, o: State.Claim.Def): PreResult[Context, State.Claim.Def] = {
      o match {
        case o: State.Claim.Def.CurrentName => return preStateClaimDefCurrentName(ctx, o)
        case o: State.Claim.Def.Name => return preStateClaimDefName(ctx, o)
        case o: State.Claim.Def.CurrentId => return preStateClaimDefCurrentId(ctx, o)
        case o: State.Claim.Def.Id => return preStateClaimDefId(ctx, o)
        case o: State.Claim.Def.Eq => return preStateClaimDefEq(ctx, o)
        case o: State.Claim.Def.Binary => return preStateClaimDefBinary(ctx, o)
        case o: State.Claim.Def.Unary => return preStateClaimDefUnary(ctx, o)
        case o: State.Claim.Def.SeqStore => return preStateClaimDefSeqStore(ctx, o)
        case o: State.Claim.Def.SeqLookup => return preStateClaimDefSeqLookup(ctx, o)
        case o: State.Claim.Def.FieldStore => return preStateClaimDefFieldStore(ctx, o)
        case o: State.Claim.Def.FieldLookup => return preStateClaimDefFieldLookup(ctx, o)
        case o: State.Claim.Def.Apply => return preStateClaimDefApply(ctx, o)
        case o: State.Claim.Def.IApply => return preStateClaimDefIApply(ctx, o)
        case o: State.Claim.Def.AdtLit => return preStateClaimDefAdtLit(ctx, o)
        case o: State.Claim.Def.SeqLit => return preStateClaimDefSeqLit(ctx, o)
      }
    }

    @pure def preStateClaimDefCurrentName(ctx: Context, o: State.Claim.Def.CurrentName): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefName(ctx: Context, o: State.Claim.Def.Name): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefCurrentId(ctx: Context, o: State.Claim.Def.CurrentId): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefId(ctx: Context, o: State.Claim.Def.Id): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefEq(ctx: Context, o: State.Claim.Def.Eq): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefBinary(ctx: Context, o: State.Claim.Def.Binary): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefUnary(ctx: Context, o: State.Claim.Def.Unary): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefSeqStore(ctx: Context, o: State.Claim.Def.SeqStore): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefSeqLookup(ctx: Context, o: State.Claim.Def.SeqLookup): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefFieldStore(ctx: Context, o: State.Claim.Def.FieldStore): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefFieldLookup(ctx: Context, o: State.Claim.Def.FieldLookup): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefApply(ctx: Context, o: State.Claim.Def.Apply): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefIApply(ctx: Context, o: State.Claim.Def.IApply): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefAdtLit(ctx: Context, o: State.Claim.Def.AdtLit): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def preStateClaimDefSeqLit(ctx: Context, o: State.Claim.Def.SeqLit): PreResult[Context, State.Claim.Def] = {
      return PreResult(ctx, T, None())
    }

    @pure def postState(ctx: Context, o: State): TPostResult[Context, State] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateValue(ctx: Context, o: State.Value): TPostResult[Context, State.Value] = {
      o match {
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

    @pure def postStateValueSym(ctx: Context, o: State.Value.Sym): TPostResult[Context, State.Value] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaim(ctx: Context, o: State.Claim): TPostResult[Context, State.Claim] = {
      o match {
        case o: State.Claim.And => return postStateClaimAnd(ctx, o)
        case o: State.Claim.Or => return postStateClaimOr(ctx, o)
        case o: State.Claim.Imply => return postStateClaimImply(ctx, o)
        case o: State.Claim.Quant => return postStateClaimQuant(ctx, o)
        case o: State.Claim.Neg => return postStateClaimNeg(ctx, o)
        case o: State.Claim.Prop => return postStateClaimProp(ctx, o)
        case o: State.Claim.If => return postStateClaimIf(ctx, o)
        case o: State.Claim.Def.CurrentName =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefCurrentName(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Name =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefName(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.CurrentId =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefCurrentId(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Id =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefId(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Eq =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefEq(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Binary =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefBinary(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Unary =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefUnary(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.SeqStore =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefSeqStore(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.SeqLookup =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefSeqLookup(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.FieldStore =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefFieldStore(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.FieldLookup =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefFieldLookup(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.Apply =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefApply(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.IApply =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefIApply(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.AdtLit =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefAdtLit(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
        case o: State.Claim.Def.SeqLit =>
          val r: TPostResult[Context, State.Claim] = postStateClaimDefSeqLit(ctx, o) match {
           case TPostResult(postCtx, Some(result: State.Claim)) => TPostResult(postCtx, Some[State.Claim](result))
           case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim")
           case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim]())
          }
          return r
      }
    }

    @pure def postStateClaimAnd(ctx: Context, o: State.Claim.And): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimOr(ctx: Context, o: State.Claim.Or): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimImply(ctx: Context, o: State.Claim.Imply): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimQuant(ctx: Context, o: State.Claim.Quant): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimNeg(ctx: Context, o: State.Claim.Neg): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimProp(ctx: Context, o: State.Claim.Prop): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimIf(ctx: Context, o: State.Claim.If): TPostResult[Context, State.Claim] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDef(ctx: Context, o: State.Claim.Def): TPostResult[Context, State.Claim.Def] = {
      o match {
        case o: State.Claim.Def.CurrentName => return postStateClaimDefCurrentName(ctx, o)
        case o: State.Claim.Def.Name => return postStateClaimDefName(ctx, o)
        case o: State.Claim.Def.CurrentId => return postStateClaimDefCurrentId(ctx, o)
        case o: State.Claim.Def.Id => return postStateClaimDefId(ctx, o)
        case o: State.Claim.Def.Eq => return postStateClaimDefEq(ctx, o)
        case o: State.Claim.Def.Binary => return postStateClaimDefBinary(ctx, o)
        case o: State.Claim.Def.Unary => return postStateClaimDefUnary(ctx, o)
        case o: State.Claim.Def.SeqStore => return postStateClaimDefSeqStore(ctx, o)
        case o: State.Claim.Def.SeqLookup => return postStateClaimDefSeqLookup(ctx, o)
        case o: State.Claim.Def.FieldStore => return postStateClaimDefFieldStore(ctx, o)
        case o: State.Claim.Def.FieldLookup => return postStateClaimDefFieldLookup(ctx, o)
        case o: State.Claim.Def.Apply => return postStateClaimDefApply(ctx, o)
        case o: State.Claim.Def.IApply => return postStateClaimDefIApply(ctx, o)
        case o: State.Claim.Def.AdtLit => return postStateClaimDefAdtLit(ctx, o)
        case o: State.Claim.Def.SeqLit => return postStateClaimDefSeqLit(ctx, o)
      }
    }

    @pure def postStateClaimDefCurrentName(ctx: Context, o: State.Claim.Def.CurrentName): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefName(ctx: Context, o: State.Claim.Def.Name): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefCurrentId(ctx: Context, o: State.Claim.Def.CurrentId): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefId(ctx: Context, o: State.Claim.Def.Id): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefEq(ctx: Context, o: State.Claim.Def.Eq): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefBinary(ctx: Context, o: State.Claim.Def.Binary): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefUnary(ctx: Context, o: State.Claim.Def.Unary): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefSeqStore(ctx: Context, o: State.Claim.Def.SeqStore): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefSeqLookup(ctx: Context, o: State.Claim.Def.SeqLookup): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefFieldStore(ctx: Context, o: State.Claim.Def.FieldStore): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefFieldLookup(ctx: Context, o: State.Claim.Def.FieldLookup): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefApply(ctx: Context, o: State.Claim.Def.Apply): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefIApply(ctx: Context, o: State.Claim.Def.IApply): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefAdtLit(ctx: Context, o: State.Claim.Def.AdtLit): TPostResult[Context, State.Claim.Def] = {
      return TPostResult(ctx, None())
    }

    @pure def postStateClaimDefSeqLit(ctx: Context, o: State.Claim.Def.SeqLit): TPostResult[Context, State.Claim.Def] = {
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

@datatype class StateTransformer[Context](pp: PrePost[Context]) {

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
        case o2: State.Claim.Quant =>
          val r0: TPostResult[Context, IS[Z, State.Claim.Def.CurrentId]] = transformISZ(preR.ctx, o2.ids, transformStateClaimDefCurrentId _)
          val r1: TPostResult[Context, State.Claim] = transformStateClaim(r0.ctx, o2.claim)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(ids = r0.resultOpt.getOrElse(o2.ids), claim = r1.resultOpt.getOrElse(o2.claim))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Neg =>
          val r0: TPostResult[Context, State.Claim] = transformStateClaim(preR.ctx, o2.claim)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(claim = r0.resultOpt.getOrElse(o2.claim))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Prop =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(value = r0.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.If =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Claim] = transformStateClaim(r0.ctx, o2.tClaim)
          val r2: TPostResult[Context, State.Claim] = transformStateClaim(r1.ctx, o2.fClaim)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), tClaim = r1.resultOpt.getOrElse(o2.tClaim), fClaim = r2.resultOpt.getOrElse(o2.fClaim))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.CurrentName =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.Name =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.CurrentId =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.Id =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.Eq =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.Binary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.left)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.right)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), left = r1.resultOpt.getOrElse(o2.left), right = r2.resultOpt.getOrElse(o2.right))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.Unary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.SeqStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          val r3: TPostResult[Context, State.Value] = transformStateValue(r2.ctx, o2.element)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty || r3.resultOpt.nonEmpty)
            TPostResult(r3.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index), element = r3.resultOpt.getOrElse(o2.element))))
          else
            TPostResult(r3.ctx, None())
        case o2: State.Claim.Def.SeqLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.FieldStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt), value = r2.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.FieldLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.Apply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.IApply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.o)
          val r2: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r1.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), o = r1.resultOpt.getOrElse(o2.o), args = r2.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.AdtLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.SeqLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
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

  @pure def transformStateClaimDef(ctx: Context, o: State.Claim.Def): TPostResult[Context, State.Claim.Def] = {
    val preR: PreResult[Context, State.Claim.Def] = pp.preStateClaimDef(ctx, o)
    val r: TPostResult[Context, State.Claim.Def] = if (preR.continu) {
      val o2: State.Claim.Def = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val rOpt: TPostResult[Context, State.Claim.Def] = o2 match {
        case o2: State.Claim.Def.CurrentName =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.Name =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.CurrentId =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.Id =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
          else
            TPostResult(r0.ctx, None())
        case o2: State.Claim.Def.Eq =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.Binary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.left)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.right)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), left = r1.resultOpt.getOrElse(o2.left), right = r2.resultOpt.getOrElse(o2.right))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.Unary =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), value = r1.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.SeqStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          val r3: TPostResult[Context, State.Value] = transformStateValue(r2.ctx, o2.element)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty || r3.resultOpt.nonEmpty)
            TPostResult(r3.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index), element = r3.resultOpt.getOrElse(o2.element))))
          else
            TPostResult(r3.ctx, None())
        case o2: State.Claim.Def.SeqLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.seq)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.index)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), seq = r1.resultOpt.getOrElse(o2.seq), index = r2.resultOpt.getOrElse(o2.index))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.FieldStore =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          val r2: TPostResult[Context, State.Value] = transformStateValue(r1.ctx, o2.value)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt), value = r2.resultOpt.getOrElse(o2.value))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.FieldLookup =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.adt)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), adt = r1.resultOpt.getOrElse(o2.adt))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.Apply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.IApply =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, State.Value] = transformStateValue(r0.ctx, o2.o)
          val r2: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r1.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty || r2.resultOpt.nonEmpty)
            TPostResult(r2.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), o = r1.resultOpt.getOrElse(o2.o), args = r2.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r2.ctx, None())
        case o2: State.Claim.Def.AdtLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          val r1: TPostResult[Context, IS[Z, State.Value]] = transformISZ(r0.ctx, o2.args, transformStateValue _)
          if (hasChanged || r0.resultOpt.nonEmpty || r1.resultOpt.nonEmpty)
            TPostResult(r1.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym), args = r1.resultOpt.getOrElse(o2.args))))
          else
            TPostResult(r1.ctx, None())
        case o2: State.Claim.Def.SeqLit =>
          val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
          if (hasChanged || r0.resultOpt.nonEmpty)
            TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
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
    val o2: State.Claim.Def = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Claim.Def] = pp.postStateClaimDef(r.ctx, o2)
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

  @pure def transformStateClaimDefCurrentId(ctx: Context, o: State.Claim.Def.CurrentId): TPostResult[Context, State.Claim.Def.CurrentId] = {
    val preR: PreResult[Context, State.Claim.Def.CurrentId] = pp.preStateClaimDefCurrentId(ctx, o) match {
     case PreResult(preCtx, continu, Some(r: State.Claim.Def.CurrentId)) => PreResult(preCtx, continu, Some[State.Claim.Def.CurrentId](r))
     case PreResult(_, _, Some(_)) => halt("Can only produce object of type State.Claim.Def.CurrentId")
     case PreResult(preCtx, continu, _) => PreResult(preCtx, continu, None[State.Claim.Def.CurrentId]())
    }
    val r: TPostResult[Context, State.Claim.Def.CurrentId] = if (preR.continu) {
      val o2: State.Claim.Def.CurrentId = preR.resultOpt.getOrElse(o)
      val hasChanged: B = preR.resultOpt.nonEmpty
      val r0: TPostResult[Context, State.Value.Sym] = transformStateValueSym(preR.ctx, o2.sym)
      if (hasChanged || r0.resultOpt.nonEmpty)
        TPostResult(r0.ctx, Some(o2(sym = r0.resultOpt.getOrElse(o2.sym))))
      else
        TPostResult(r0.ctx, None())
    } else if (preR.resultOpt.nonEmpty) {
      TPostResult(preR.ctx, Some(preR.resultOpt.getOrElse(o)))
    } else {
      TPostResult(preR.ctx, None())
    }
    val hasChanged: B = r.resultOpt.nonEmpty
    val o2: State.Claim.Def.CurrentId = r.resultOpt.getOrElse(o)
    val postR: TPostResult[Context, State.Claim.Def.CurrentId] = pp.postStateClaimDefCurrentId(r.ctx, o2) match {
     case TPostResult(postCtx, Some(result: State.Claim.Def.CurrentId)) => TPostResult(postCtx, Some[State.Claim.Def.CurrentId](result))
     case TPostResult(_, Some(_)) => halt("Can only produce object of type State.Claim.Def.CurrentId")
     case TPostResult(postCtx, _) => TPostResult(postCtx, None[State.Claim.Def.CurrentId]())
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