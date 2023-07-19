package org.sireum.logika.modelparser

import org.sireum._
import org.antlr.v4.runtime._
import org.antlr.v4.runtime.tree._
import org.sireum.logika.modelparser.SMTLIBv2Parser._

import scala.collection.mutable

class GetVariablesListener extends SMTLIBv2BaseListener {
  val nameToValue: mutable.Map[String, String] = mutable.Map[String, String]()
  val nameToType: mutable.Map[String, String] = mutable.Map[String, String]()

  override def enterFunction_def(ctx: SMTLIBv2Parser.Function_defContext): Unit = {
    if(ctx.getText.startsWith("|l:")) {
      val v = ctx.symbol.getText
      val argTyp = ctx.sort.identifier.symbol.simpleSymbol.getText
      val argValue = ctx.term().getText

      print()
    }
  }
}

object ResponseParser_Ext {
  def parseResponse(response: String): Map[String, String] = {
    val lexer = new SMTLIBv2Lexer(CharStreams.fromString(response.native))
    val tokens = new CommonTokenStream(lexer)
    val parser = new SMTLIBv2Parser(tokens)

    val tree = parser.response()
    val walker = new ParseTreeWalker()
    val listener = new GetVariablesListener()

    walker.walk(listener, tree)

    halt("Not Implemented")
  }
}
