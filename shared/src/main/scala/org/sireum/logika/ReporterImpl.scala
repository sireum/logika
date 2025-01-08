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

package org.sireum.logika

import org.sireum._
import org.sireum.message._
import org.sireum.lang.tipe.TypeHierarchy

import java.util.concurrent.atomic.AtomicLong

object ReporterImpl {
  def create(logPc: B, logPcRaw: B, logVc: B, logDetailedInfo: B): ReporterImpl =
    new ReporterImpl(logPc, logPcRaw, logVc, logDetailedInfo, F, ISZ(), F,
      new AtomicLong(0), new AtomicLong(0), new AtomicLong(0), new AtomicLong(0))
}

class ReporterImpl(val logPc: B,
                         val logPcRaw: B,
                         val logVc: B,
                         val logDetailedInfo: B,
                         var _ignore: B,
                         var _messages: ISZ[Message],
                         var collectStats: B,
                         val _numOfVCs: AtomicLong,
                         val _numOfSats: AtomicLong,
                         val _vcMillis: AtomicLong,
                         val _satMillis: AtomicLong) extends Logika.Reporter {
  var clonable: Boolean = T
  var owned: Boolean = F

  override def numOfVCs: Z = _numOfVCs.get
  override def numOfSats: Z = _numOfSats.get
  override def vcMillis: Z = _vcMillis.get
  override def satMillis: Z = _satMillis.get

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

  override def $clone: ReporterImpl = new ReporterImpl(logPc, logPcRaw, logVc, logDetailedInfo, _ignore, _messages,
    collectStats, _numOfVCs, _numOfSats, _vcMillis, _satMillis)

  override def state(plugins: ISZ[logika.plugin.ClaimPlugin], posOpt: Option[Position], context: ISZ[String],
                     th: TypeHierarchy, s: State, atLinesFresh: B, atRewrite: B): Unit = {
    if (logPc || logPcRaw) {
      val sts: ISZ[ST] =
        if (logPcRaw) {
          State.Claim.claimsRawSTs(s.claims)
        } else {
          val (es, _) = Util.claimsToExps(plugins,posOpt.get, context, s.claims, th, atLinesFresh, atRewrite)
          for (e <- es) yield e.prettyST
        }
      if (sts.isEmpty) {
        info(posOpt, Logika.kind, "Path conditions = {}")
      } else {
        info(posOpt, Logika.kind,
          st"""Path conditions = {
              |  ${(sts, ",\n")}
              |}""".
            render
        )
      }
    }
  }

  override def query(pos: Position, title: String, isSat: B, time: Z, forceReport: B, detailElided: B,
                     r: Smt2Query.Result): Unit = {
    if (collectStats) {
      if (isSat) {
        _numOfSats.incrementAndGet
        _satMillis.addAndGet(time.toLong)
      } else {
        _numOfVCs.incrementAndGet
        _vcMillis.addAndGet(time.toLong)
      }
    }
    if (logVc) {
      info(Some(pos), Logika.kind, r.query)
    }
  }

  override def inform(pos: Position, kind: Logika.Reporter.Info.Kind.Type, message: String): Unit = kind match {
    case Logika.Reporter.Info.Kind.Verified =>
      if (logDetailedInfo) {
        info(Some(pos), Logika.kind, message)
      }
    case Logika.Reporter.Info.Kind.Error => error(Some(pos), Logika.kind, message)
  }

  override def illFormed(): Unit = {
  }

  override def coverage(setCache: B, cached: U64, pos: Position): Unit = {
  }

  override def empty: Logika.Reporter = {
    return new ReporterImpl(logPc, logPcRaw, logVc, logDetailedInfo, F, ISZ(), collectStats, _numOfVCs, _numOfSats,
      _vcMillis, _satMillis)
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

  override def combine(other: Logika.Reporter): Logika.Reporter = synchronized {
    _messages = _messages ++ other.messages
    return this
  }

  override def string: String = "ReporterImpl"
}
