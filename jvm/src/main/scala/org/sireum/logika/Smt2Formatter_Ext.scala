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
import java.lang.{String => JString, Float => JFloat, Double => JDouble, Integer => JInteger, Long => JLong}
import java.util.concurrent.TimeUnit

object Smt2Formatter_Ext {

  def formatVal(width: Z, n: Z): ST = width.toInt match {
    case 0 =>
      var r = st"${n.toBigInt.abs}"
      if (n < 0) {
        r = st"(- $r)"
      }
      r
    case 8 => st"${JString.format("#x%02X", n.toBigInt.toByte)}"
    case 16 => st"${JString.format("#x%04X", n.toBigInt.toShort)}"
    case 32 => st"${JString.format("#x%08X", n.toBigInt.toInt)}"
    case 64 => st"${JString.format("#x%016X", n.toBigInt.toLong)}"
  }

  def formatF32(useReal: B, value: F32): ST = {
    val f = value.value
    if (JFloat.isNaN(f)) {
      return st"|F32.NaN|"
    } else if (JFloat.NEGATIVE_INFINITY == f) {
      return st"|F32.PInf|"
    } else if (JFloat.POSITIVE_INFINITY == f) {
      return st"|F32.NInf|"
    } else if (useReal) {
      return formatR(new R(new java.math.BigDecimal(f)))
    } else {
      val bits = JFloat.floatToRawIntBits(f)
      val sign = if ((bits & 0x80000000) != 0) 1 else 0
      var eb = JInteger.toHexString((bits & 0x7f800000) >>> 23)
      eb = "#x" + (0 until (2 - eb.length)).map(_ => '0').mkString + eb
      var sb = JInteger.toBinaryString(bits & 0x007fffff)
      sb = "#b" + (0 until (23 - sb.length)).map(_ => '0').mkString + sb
      return st"(fp #b$sign $eb $sb)"
    }
  }

  def formatF64(useReal: B, value: F64): ST = {
    val d = value.value
    if (JDouble.isNaN(d)) {
      return st"|F64.NaN|"
    } else if (JDouble.NEGATIVE_INFINITY == d) {
      return st"|F64.PInf|"
    } else if (JDouble.POSITIVE_INFINITY == d) {
      return st"|F64.NInf|"
    } else if (useReal) {
      return formatR(new R(new java.math.BigDecimal(d)))
    } else {
      val bits = JDouble.doubleToRawLongBits(d)
      val sign = if ((bits & 0x8000000000000000L) != 0) 1 else 0
      var eb = JLong.toBinaryString((bits & 0x7ff0000000000000L) >>> 52)
      eb = "#b" + (0 until (11 - eb.length)).map(_ => '0').mkString + eb
      var sb = JLong.toHexString(bits & 0x000fffffffffffffL)
      sb = "#x" + (0 until (13 - sb.length)).map(_ => '0').mkString + sb
      return st"(fp #b$sign $eb $sb)"
    }
  }

  def formatR(n: R): ST = {
    val (isNeg, value) = if (n < new R(new java.math.BigDecimal(0))) (T, -n) else (F, n)
    val r = if (value.toString.contains(".")) st"$value" else st"$value.0"
    return if (isNeg) st"(- $r)" else r
  }

  def formatFilename(filename: String): String = {
    val fname = for (c <- filename.value) yield if (('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')) c else '-'
    return fname + '.' + extension.Time.currentNanos
  }

  def formatTime(milis: Z): ST = {
    val l = milis.toLong
    val hr = TimeUnit.MILLISECONDS.toHours(l)
    val min = TimeUnit.MILLISECONDS.toMinutes(l - TimeUnit.HOURS.toMillis(hr))
    val sec = TimeUnit.MILLISECONDS.toSeconds(l - TimeUnit.HOURS.toMillis(hr) - TimeUnit.MINUTES.toMillis(min))
    val ms = TimeUnit.MILLISECONDS.toMillis(l - TimeUnit.HOURS.toMillis(hr) - TimeUnit.MINUTES.toMillis(min) - TimeUnit.SECONDS.toMillis(sec))
    if (hr > 0) {
      return st"${JString.format("%d:%02d:%02d.%03d", hr, min, sec, ms)}"
    } else if (min > 0) {
      return st"${JString.format("%d:%02d.%03d", min, sec, ms)}"
    } else if (sec > 0) {
      return st"${JString.format("%d.%03ds", sec, ms)}"
    } else {
      return st"${JString.format("0.%03ds", ms)}"
    }
  }

}
