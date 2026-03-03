/*
 Copyright (c) 2017-2026,Robby, Kansas State University
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
import org.sireum.WasmServer

import java.nio.charset.StandardCharsets

import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

object Smt2WasmInvoke_Ext {

  /** Delegate to WasmServer.hasJvmci to avoid duplicating the JVMCI detection logic. */
  val hasJvmci: B = WasmServer.hasJvmci

  /**
   * Persistent GraalWasm cvc5 server. Extends WasmServer for lifecycle management,
   * FastPipe I/O, and protocol helpers (writeU32/readU32).
   */
  private class Cvc5Server(wasmPath: Predef.String) extends WasmServer(
    java.nio.file.Files.readAllBytes(java.nio.file.Path.of(wasmPath)),
    "cvc5_server",
    Array("cvc5_server"),
    _.option("wasm.WasiConstantRandomGet", "true")
  ) {
    start() // auto-start on construction (matching original behavior)

    def query(optsBytes: Array[Byte], queryBytes: Array[Byte]): Predef.String = {
      // Send options
      writeU32(stdinStream, optsBytes.length)
      stdinStream.write(optsBytes)
      stdinStream.flush()

      // Send query
      writeU32(stdinStream, queryBytes.length)
      stdinStream.write(queryBytes)
      stdinStream.flush()

      // Read response
      val len = readU32(stdoutStream)
      if (len <= 0) return ""
      val result = new Array[Byte](len)
      var n = 0
      while (n < len) {
        val r = stdoutStream.read(result, n, len - n)
        if (r < 0) return new Predef.String(result, 0, n, StandardCharsets.UTF_8)
        n += r
      }
      new Predef.String(result, StandardCharsets.UTF_8)
    }

    override def shutdown(): Unit = {
      try {
        // Send shutdown (zero-length options message)
        writeU32(stdinStream, 0)
        stdinStream.flush()
      } catch { case _: Throwable => }
      super.shutdown()
    }
  }

  /** Thread-local Cvc5Server instance (one per thread per WASM path). */
  private val servers = new ThreadLocal[java.util.HashMap[Predef.String, Cvc5Server]] {
    override def initialValue(): java.util.HashMap[Predef.String, Cvc5Server] =
      new java.util.HashMap()
  }

  private def getServer(wasmPath: Predef.String): Cvc5Server = {
    val map = servers.get()
    var server = map.get(wasmPath)
    if (server == null || !server.isAlive) {
      if (server != null) server.restart()
      else {
        server = new Cvc5Server(wasmPath)
        map.put(wasmPath, server)
      }
    }
    server
  }

  def querySingle(config: Smt2Config,
                  isSat: B,
                  queryString: String,
                  timeoutInMs: Z,
                  rlimit: Z): Either[Smt2Query.Result, (String, ISZ[String], Smt2Query.Result.Kind.Type, Z)] = {
    val start = extension.Time.currentMillis

    // Build per-query opts from config.opts (e.g., ISZ("--full-saturate-quant"))
    val queryOpts = config.opts.elements.map(_.value).mkString(" ")
    val wasmPath = config.exe.value

    // Prepend per-query rlimit/tlimit as SMT-LIB set-option
    val prefix = s"(set-option :rlimit ${rlimit.toBigInt})\n(set-option :tlimit ${timeoutInMs.toBigInt})\n"
    val fullQuery = prefix + queryString.value
    val optsBytes = queryOpts.getBytes(StandardCharsets.UTF_8)
    val queryBytes = fullQuery.getBytes(StandardCharsets.UTF_8)

    try {
      val server = getServer(wasmPath)
      if (!server.isAlive) {
        server.restart()
        if (!server.isAlive) {
          val time = extension.Time.currentMillis - start
          return Either.Right((config.exe, ISZ(), Smt2Query.Result.Kind.Error, time))
        }
      }

      val timeoutMs = timeoutInMs.toInt * Runtime.getRuntime.availableProcessors() * 2
      val resultStr: Predef.String = Await.result(Future { server.query(optsBytes, queryBytes) }, timeoutMs.millis)

      val pout = String(resultStr)
      val time = extension.Time.currentMillis - start

      // Parse output using plain Scala string operations to avoid C/Char type mismatch
      val outLines = resultStr.split('\n')

      // Find first non-comment, non-empty line
      var firstLine = ""
      var idx = 0
      while (idx < outLines.length) {
        val l = outLines(idx).trim
        if (l.nonEmpty && !l.startsWith(";")) {
          firstLine = l.split(' ')(0).trim
          idx = outLines.length
        }
        idx += 1
      }

      val args = ISZ[String]()
      val outputLines: ISZ[ST] = {
        var r = ISZ[ST]()
        for (l <- outLines) { r = r :+ st"; ${String(l)}" }
        r
      }
      String(firstLine) match {
        case string"sat" => Either.Left(Smt2Query.Result(
          kind = Smt2Query.Result.Kind.Sat,
          solverName = config.name,
          query = queryString,
          info = st"""; Result: ${if (isSat) "Sat" else "Invalid"}
                     |; Solver: ${config.exe} (WASM)
                     |; Options: $queryOpts""".render,
          output = pout,
          timeMillis = time,
          totalTimeMillis = 0,
          cached = F))
        case string"unsat" => Either.Left(Smt2Query.Result(
          kind = Smt2Query.Result.Kind.Unsat,
          solverName = config.name,
          query = queryString,
          info = st"""; Result: ${if (isSat) "Unsat" else "Valid"}
                     |; Solver: ${config.exe} (WASM)
                     |; Options: $queryOpts""".render,
          output = pout,
          timeMillis = time,
          totalTimeMillis = 0,
          cached = F))
        case string"timeout" => Either.Right((config.exe, args, Smt2Query.Result.Kind.Timeout, time))
        case string"unknown" => Either.Right((config.exe, args, Smt2Query.Result.Kind.Unknown, time))
        case _ => Either.Left(Smt2Query.Result(
          kind = Smt2Query.Result.Kind.Error,
          solverName = config.name,
          query = queryString,
          info = st"""; Result: Error
                     |; Solver: ${config.exe} (WASM)
                     |; Options: $queryOpts
                     |; Output:
                     |${(outputLines, "\n")}
                     |$queryString""".render,
          output = pout,
          timeMillis = time,
          totalTimeMillis = 0,
          cached = F))
      }
    } catch {
      case _: java.util.concurrent.TimeoutException =>
        val time = extension.Time.currentMillis - start
        Either.Right((config.exe, ISZ(), Smt2Query.Result.Kind.Timeout, time))
      case e: Throwable =>
        val time = extension.Time.currentMillis - start
        Either.Left(Smt2Query.Result(
          kind = Smt2Query.Result.Kind.Error,
          solverName = config.name,
          query = queryString,
          info = st"""; Result: Error (WASM exception: ${e.getMessage})
                     |; Solver: ${config.exe} (WASM)
                     |; Options: $queryOpts""".render,
          output = String(e.getMessage),
          timeMillis = time,
          totalTimeMillis = 0,
          cached = F))
    }
  }
}
