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
import org.sireum.lang.tipe.TypeHierarchy
import org.sireum.lang.{ast => AST}
import org.sireum.logika.Logika.Cache
import org.sireum.U64._

object NoTransitionSmt2Cache_Ext {
  def create: Logika.Cache = new NoTransitionSmt2CacheImpl()
}

trait CacheProperties extends Cache {
  def persistentCache: java.util.concurrent.ConcurrentHashMap[Cache.Key, Cache.Value]
  def taskCache: java.util.concurrent.ConcurrentHashMap[Cache.Key, Cache.Value]

  def keys: ISZ[Cache.Key] = {
    import org.sireum.$internal.CollectionCompat.Converters._
    var r = ISZ[Cache.Key]()
    for (key <- persistentCache.keys.asScala) {
      r = r :+ key
    }
    return r
  }

  def getValue(key: Cache.Key): Option[Cache.Value] = {
    val r = persistentCache.get(key)
    return if (r == null) None() else Some(r)
  }

  def setValue(key: Cache.Key, value: Cache.Value): Unit = {
    persistentCache.put(key, value)
  }

  def clearValue(key: Cache.Key): Unit = {
    persistentCache.remove(key)
  }

  def taskKeys: ISZ[Cache.Key] = {
    import org.sireum.$internal.CollectionCompat.Converters._
    val tid = System.identityHashCode(java.lang.Thread.currentThread)
    var r = ISZ[Cache.Key]()
    for (p <- taskCache.keys.asScala) {
      r = r :+ p
    }
    return r
  }

  def getTaskValue(key: Cache.Key): Option[Cache.Value] = {
    val tid = System.identityHashCode(java.lang.Thread.currentThread)
    val r = taskCache.get((tid, key))
    return if (r == null) None() else Some(r)
  }

  def setTaskValue(key: Cache.Key, value: Cache.Value): Unit = {
    taskCache.put(key, value)
  }

  def clearTaskValue(key: Cache.Key): Unit = {
    taskCache.remove(key)
  }

  def clearTaskCache(): Unit
}

final class NoTransitionSmt2CacheImpl(val persistentCache: java.util.concurrent.ConcurrentHashMap[Cache.Key, Cache.Value] =
                                      new java.util.concurrent.ConcurrentHashMap,
                                      val taskCache: java.util.concurrent.ConcurrentHashMap[Cache.Key, Cache.Value] =
                                      new java.util.concurrent.ConcurrentHashMap) extends CacheProperties {

  private var owned: Boolean = false

  override def clearTransition(): Unit = {}

  def getTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, transition: Cache.Transition, context: ISZ[String], state: State,
                                 smt2: Smt2): Option[(ISZ[State], U64, HashSet[String])] = None()

  def setTransition(th: TypeHierarchy, config: Config, transition: Cache.Transition, context: ISZ[String], state: State,
                    nextStates: ISZ[State], smt2: Smt2, modifiables: HashSet[String]): U64 = u64"0"

  def getAssignExpTransitionAndUpdateSmt2(th: TypeHierarchy, config: Config, exp: AST.AssignExp, context: ISZ[String], state: State,
                                          smt2: Smt2): Option[(ISZ[(State, State.Value)], U64)] = None()

  def setAssignExpTransition(th: TypeHierarchy, config: Config, exp: AST.AssignExp, context: ISZ[String], state: State,
                             nextStatesValues: ISZ[(State, State.Value)], smt2: Smt2): U64 = u64"0"

  def getSmt2(isSat: B, th: TypeHierarchy, config: Config, timeoutInMs: Z, claims: ISZ[State.Claim]): Option[Smt2Query.Result] = None()

  def setSmt2(isSat: B, th: TypeHierarchy, config: Config, timeoutInMs: Z, claims: ISZ[State.Claim], result: Smt2Query.Result): Unit = {}

  def getPatterns(th: TypeHierarchy, isInObject: B, name: ISZ[String]): Option[ISZ[RewritingSystem.Rewriter.Pattern]] = None()

  def setPatterns(th: TypeHierarchy, isInObject: B, name: ISZ[String], patterns: ISZ[RewritingSystem.Rewriter.Pattern]): Unit = {}

  def clearTaskCache(): Unit = {}

  override def $clonable: Boolean = false

  override def $clonable_=(b: Boolean): this.type = halt("Cannot update NoSmt2CacheImpl clonable status")

  override def $owned: Boolean = owned

  override def $owned_=(b: Boolean): this.type = {
    owned = true
    this
  }

  override def $clone: this.type = halt("Cannot clone NoSmt2CacheImpl")

  override def string: String = "NoSmt2CacheImpl"
}

