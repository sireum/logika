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

import java.io.{InputStream, OutputStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import java.util.concurrent.locks.ReentrantLock

import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

object Smt2WasmInvoke_Ext {

  /** Check if GraalVM Polyglot (WASM) is available and JVMCI compiler is active. */
  val hasJvmci: B = {
    try {
      Class.forName("org.graalvm.polyglot.Context")
      val args = java.lang.management.ManagementFactory.getRuntimeMXBean.getInputArguments
      var jvmciEnabled = false
      val it = args.iterator()
      while (it.hasNext) {
        val arg = it.next()
        if (arg.contains("EnableJVMCI") || arg.contains("upgrade-module-path")) {
          jvmciEnabled = true
        }
      }
      jvmciEnabled
    } catch {
      case _: ClassNotFoundException => false
    }
  }

  /**
   * Ring buffer with ReentrantLock + Condition, replacing Java's PipedInputStream
   * which has a 1-second polling delay.
   */
  private class FastPipe(capacity: Int = 1024 * 1024) {
    private val buf = new Array[Byte](capacity)
    private var readPos = 0
    private var writePos = 0
    private var count = 0
    private var closed = false
    private val lock = new ReentrantLock()
    private val notEmpty = lock.newCondition()
    private val notFull = lock.newCondition()

    val inputStream: InputStream = new InputStream {
      override def read(): Int = {
        lock.lock()
        try {
          while (count == 0 && !closed) notEmpty.await()
          if (count == 0) return -1
          val b = buf(readPos) & 0xFF
          readPos = (readPos + 1) % capacity
          count -= 1
          notFull.signal()
          b
        } finally {
          lock.unlock()
        }
      }

      override def read(b: Array[Byte], off: Int, len: Int): Int = {
        if (len == 0) return 0
        lock.lock()
        try {
          while (count == 0 && !closed) notEmpty.await()
          if (count == 0) return -1
          val n = math.min(len, count)
          var i = 0
          while (i < n) {
            b(off + i) = buf(readPos)
            readPos = (readPos + 1) % capacity
            i += 1
          }
          count -= n
          notFull.signal()
          n
        } finally {
          lock.unlock()
        }
      }
    }

    val outputStream: OutputStream = new OutputStream {
      override def write(b: Int): Unit = {
        lock.lock()
        try {
          while (count == capacity && !closed) notFull.await()
          if (closed) throw new java.io.IOException("Pipe closed")
          buf(writePos) = b.toByte
          writePos = (writePos + 1) % capacity
          count += 1
          notEmpty.signal()
        } finally {
          lock.unlock()
        }
      }

      override def write(b: Array[Byte], off: Int, len: Int): Unit = {
        if (len == 0) return
        lock.lock()
        try {
          var written = 0
          while (written < len) {
            while (count == capacity && !closed) notFull.await()
            if (closed) throw new java.io.IOException("Pipe closed")
            val space = capacity - count
            val n = math.min(len - written, space)
            var i = 0
            while (i < n) {
              buf(writePos) = b(off + written + i)
              writePos = (writePos + 1) % capacity
              i += 1
            }
            count += n
            written += n
            notEmpty.signal()
          }
        } finally {
          lock.unlock()
        }
      }

      override def flush(): Unit = {}
    }

    def close(): Unit = {
      lock.lock()
      try {
        closed = true
        notEmpty.signalAll()
        notFull.signalAll()
      } finally {
        lock.unlock()
      }
    }

    def reset(): Unit = {
      lock.lock()
      try {
        readPos = 0
        writePos = 0
        count = 0
        closed = false
      } finally {
        lock.unlock()
      }
    }
  }

  /**
   * Persistent GraalWasm cvc5 instance. Loads the WASM binary, creates a GraalVM
   * Context, and runs _start in a daemon thread communicating via FastPipe stdin/stdout.
   * Options are sent before each query (per-query protocol).
   */
  private class Cvc5WasmServer(wasmPath: Predef.String) {
    private val wasmBytes = Files.readAllBytes(Path.of(wasmPath))
    private val stdinPipe = new FastPipe()
    private val stdoutPipe = new FastPipe()
    @volatile private var alive = false
    @volatile private var error: Predef.String = _
    private var thread: Thread = _

    start()

    private def start(): Unit = {
      stdinPipe.reset()
      stdoutPipe.reset()
      alive = false
      error = null

      thread = new Thread(() => {
        var context: org.graalvm.polyglot.Context = null
        try {
          val source = org.graalvm.polyglot.Source.newBuilder(
            "wasm",
            org.graalvm.polyglot.io.ByteSequence.create(wasmBytes),
            "cvc5_server"
          ).build()

          context = org.graalvm.polyglot.Context.newBuilder("wasm")
            .option("wasm.Builtins", "wasi_snapshot_preview1")
            .option("wasm.WasiConstantRandomGet", "true")
            .option("engine.WarnInterpreterOnly", "false")
            .arguments("wasm", Array("cvc5_server"))
            .in(stdinPipe.inputStream)
            .out(stdoutPipe.outputStream)
            .err(System.err)
            .allowAllAccess(true)
            .build()

          alive = true

          val module = context.eval(source)
          val instance = module.newInstance()
          val exports = instance.getMember("exports")
          val startFn = exports.getMember("_start")
          try {
            startFn.executeVoid()
          } catch {
            case e: org.graalvm.polyglot.PolyglotException if e.isExit && e.getExitStatus == 0 => // normal shutdown
            case e: org.graalvm.polyglot.PolyglotException if e.isExit =>
              error = s"cvc5 exited with code ${e.getExitStatus}"
            case e: Throwable =>
              error = s"WASM error: ${e.getMessage}"
          }
        } catch {
          case e: Throwable =>
            error = s"Context error: ${e.getMessage}"
        } finally {
          alive = false
          try { stdoutPipe.close() } catch { case _: Throwable => }
          if (context != null) {
            try { context.close() } catch { case _: Throwable => }
          }
        }
      })
      thread.setDaemon(true)
      thread.setName(s"cvc5-wasm-${thread.getId}")
      thread.start()

      // Wait for the WASM server to initialize
      val deadline = System.currentTimeMillis() + 10000
      while (!alive && error == null && System.currentTimeMillis() < deadline) {
        Thread.sleep(50)
      }
    }

    def isAlive: Boolean = alive && error == null

    def restart(): Unit = {
      shutdown()
      start()
    }

    def shutdown(): Unit = {
      if (thread != null) {
        try {
          // Send shutdown (zero-length options message)
          writeU32(stdinPipe.outputStream, 0)
          stdinPipe.outputStream.flush()
        } catch { case _: Throwable => }
        stdinPipe.close()
        stdoutPipe.close()
        try { thread.join(5000) } catch { case _: Throwable => }
        if (thread.isAlive) thread.interrupt()
      }
    }

    def query(optsBytes: Array[Byte], queryBytes: Array[Byte]): Predef.String = {
      // Send options
      writeU32(stdinPipe.outputStream, optsBytes.length)
      stdinPipe.outputStream.write(optsBytes)
      stdinPipe.outputStream.flush()

      // Send query
      writeU32(stdinPipe.outputStream, queryBytes.length)
      stdinPipe.outputStream.write(queryBytes)
      stdinPipe.outputStream.flush()

      // Read response
      val len = readU32(stdoutPipe.inputStream)
      if (len <= 0) return ""
      val result = new Array[Byte](len)
      var n = 0
      while (n < len) {
        val r = stdoutPipe.inputStream.read(result, n, len - n)
        if (r < 0) return new Predef.String(result, 0, n, StandardCharsets.UTF_8)
        n += r
      }
      new Predef.String(result, StandardCharsets.UTF_8)
    }
  }

  private def writeU32(os: OutputStream, v: Int): Unit = {
    os.write((v >> 24) & 0xFF)
    os.write((v >> 16) & 0xFF)
    os.write((v >> 8) & 0xFF)
    os.write(v & 0xFF)
    os.flush()
  }

  private def readU32(is: InputStream): Int = {
    val buf = new Array[Byte](4)
    var n = 0
    while (n < 4) {
      val r = is.read(buf, n, 4 - n)
      if (r < 0) return -1
      n += r
    }
    ((buf(0) & 0xFF) << 24) | ((buf(1) & 0xFF) << 16) |
      ((buf(2) & 0xFF) << 8) | (buf(3) & 0xFF)
  }

  /** Thread-local Cvc5WasmServer instance (one per thread per WASM path). */
  private val servers = new ThreadLocal[java.util.HashMap[Predef.String, Cvc5WasmServer]] {
    override def initialValue(): java.util.HashMap[Predef.String, Cvc5WasmServer] =
      new java.util.HashMap()
  }

  private def getServer(wasmPath: Predef.String): Cvc5WasmServer = {
    val map = servers.get()
    var server = map.get(wasmPath)
    if (server == null || !server.isAlive) {
      if (server != null) server.restart()
      else {
        server = new Cvc5WasmServer(wasmPath)
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
