// #Sireum
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
import org.sireum._
import org.sireum.cli.CliOpt._

val options = Tool(
  name = "logika",
  command = "logika",
  description = "Logika verifier options",
  header = "Logika Verifier Options",
  usage = "<option>*",
  usageDescOpt = None(),
  opts = ISZ(
    Opt(name = "background", longKey = "background", shortKey = None(),
      tpe = Type.Choice(name = "background", sep = None(), elements = ISZ("type", "save", "disabled")),
      description = "Background verification mode"),
    logika.cli.modeOpt,
    Opt(name = "smt2Caching", longKey = "smt2-caching", shortKey = None(),
      tpe = Type.Flag(T),
      description = "Disable SMT2 query caching"),
    Opt(name = "transitionCaching", longKey = "transition-caching", shortKey = None(),
      tpe = Type.Flag(T),
      description = "Disable transition caching")
  ),
  groups = logika.cli.logikaVerifier.groups
)

println(org.sireum.cli.JSON.fromCliOpt(options, true))