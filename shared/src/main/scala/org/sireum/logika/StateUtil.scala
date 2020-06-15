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

