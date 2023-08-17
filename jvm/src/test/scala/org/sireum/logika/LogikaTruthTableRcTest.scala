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
import org.sireum.parser._
import org.sireum.test._
import org.antlr.runtime._
import org.sireum.lang.parser.{SlangTruthTableLexer, SlangTruthTableParser, TruthTableParser}

class LogikaTruthTableRcTest extends SireumRcSpec {

  def shouldIgnore(name: Predef.String, isSimplified: Boolean): Boolean = name match {
    case _ => false
  }

  def textResources: scala.collection.SortedMap[scala.Vector[Predef.String], Predef.String] = {
    val m = $internal.RC.text(Vector("example/truthtable")) { (p, f) => p.last.endsWith(".logika") && !p.last.startsWith("wip-") }
    implicit val ordering: Ordering[Vector[Predef.String]] = m.ordering
    for ((k, v) <- m; pair <- {
      var r = Vector[(Vector[Predef.String], Predef.String)]()
      if (!shouldIgnore(k.last, F)) {
        r = r :+ (k, v)
      }
      r
    }) yield pair
  }

  def parseTable(uriOpt: Option[String],
                 input: String,
                 reporter: message.Reporter): Option[ParseTree] = {
    val docInfo = message.DocInfo.create(uriOpt, input)

    val lex = new SlangTruthTableLexer(new ANTLRStringStream(input.value)) {
      override def displayRecognitionError(tokenNames: Array[Predef.String], e: RecognitionException): Unit = {
        val msg = getErrorMessage(e, tokenNames)
        val line = e.line
        val column = org.sireum.U32(e.charPositionInLine)
        val offsetLength = (conversions.U32.toU64(docInfo.lineOffsets(line - 1) + column) << org.sireum.U64(32)) | org.sireum.U64(1)
        reporter.error(Some(message.PosInfo(docInfo, offsetLength)), "SlangTruthTableLexer", msg)
      }
    }
    val cts = new CommonTokenStream(lex)
    val r = new SlangTruthTableParser(cts) {
      override def displayRecognitionError(tokenNames: Array[Predef.String], e: RecognitionException): Unit = {
        val msg = getErrorMessage(e, tokenNames)
        val line = e.line
        val column = org.sireum.U32(e.charPositionInLine)
        val offsetLength = (conversions.U32.toU64(docInfo.lineOffsets(line - 1) + column) << org.sireum.U64(32)) | org.sireum.U64(e.token.getText.length)
        reporter.error(Some(message.PosInfo(docInfo, offsetLength)), "SlangTruthTableParser", msg)
      }
    }
    r.setTreeAdaptor(new Antlr3Util.Adaptor(SlangTruthTableParser.tokenNames, docInfo))
    val tree = r.file().getTree.asInstanceOf[ParseTree]
    return Some(tree)
  }


  def check(path: scala.Vector[Predef.String], content: Predef.String): scala.Boolean = {
    val uriOpt = Option.some[String](path.mkString("/"))
    val reporter = ReporterImpl.create(F, F, F, F)
    parseTable(uriOpt, content, reporter) match {
      case Some(tree) =>
        TruthTableParser.buildTruthTable(uriOpt, content, tree, reporter) match {
          case Some(tt) => Logika.checkTruthTable(tt, reporter)
          case _ =>
        }
      case _ =>
    }
    reporter.printMessages()
    return !reporter.hasError
  }

}
