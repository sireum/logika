/*
 Copyright (c) 2017-2023, Robby, Kansas State University
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
import org.sireum.message._
import org.sireum.lang.tipe.TypeHierarchy

object ReporterImpl {
  def create: ReporterImpl = new ReporterImpl(F, ISZ(), F, 0, 0, 0, 0)
}

final class ReporterImpl(var _ignore: B,
                         var _messages: ISZ[Message],
                         var collectStats: B,
                         var numOfVCs: Z,
                         var numOfSats: Z,
                         var vcMillis: Z,
                         var satMillis: Z) extends Logika.Reporter {
  var clonable: Boolean = T
  var owned: Boolean = F

  override def $clonable: Boolean = clonable

  override def $clonable_=(b: Boolean): this.type = {
    clonable = b
    this
  }

  override def $owned: Boolean = owned

  override def $owned_=(b: Boolean): this.type = {
    owned = b
    this
  }

  override def $clone: ReporterImpl = new ReporterImpl(_ignore, _messages, collectStats, numOfVCs, numOfSats,
    vcMillis, satMillis)

  override def state(plugins: ISZ[logika.plugin.ClaimPlugin], posOpt: Option[Position], context: ISZ[String],
                     th: TypeHierarchy, s: State, atLinesFresh: B): Unit = {
  }

  override def query(pos: Position, title: String, isSat: B, time: Z, forceReport: B, detailElided: B,
                     r: Smt2Query.Result): Unit = if (collectStats) synchronized {
    if (isSat) {
      numOfSats = numOfSats + 1
      satMillis = satMillis + time
    } else {
      numOfVCs = numOfVCs + 1
      vcMillis = vcMillis + time
    }
  }

  override def inform(pos: Position, kind: Logika.Reporter.Info.Kind.Type, message: String): Unit = {
  }

  override def illFormed(): Unit = {
  }

  override def coverage(setCache: B, cached: U64, pos: Position): Unit = {
  }

  override def empty: Logika.Reporter = {
    return new ReporterImpl(F, ISZ(), collectStats, 0, 0, 0, 0)
  }

  override def messages: ISZ[Message] = {
    return _messages
  }

  override def ignore: B = {
    return _ignore
  }

  override def setIgnore(newIgnore: B): Unit = {
    _ignore = newIgnore
  }

  override def setMessages(newMessages: ISZ[Message]): Unit = {
    _messages = newMessages
  }

  override def timing(desc: String, timeInMs: Z): Unit = {}

  override def combine(other: Logika.Reporter): Logika.Reporter = {
    _messages = _messages ++ other.messages
    if (collectStats) synchronized {
      numOfVCs = numOfVCs + other.numOfVCs
      numOfSats = numOfSats + other.numOfSats
      vcMillis = vcMillis + other.vcMillis
      satMillis = satMillis + other.satMillis
    }
    return this
  }

  override def string: String = "ReporterImpl"
}
