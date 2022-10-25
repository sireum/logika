// #Sireum #Logika

import org.sireum._

var a_in: Z = 0
var a_out: Z = 0
var b_in: Z = 0
var b_out: Z = 0

def simple_2chan_buffer__inline_leak(): Unit = {
  Contract(
    Modifies(a_out, b_out),
    InfoFlows(
      Flow("a", // should hold
        InAgree(a_in),
        OutAgree(a_out)),
      Flow("b", // should hold
        InAgree(b_in),
        OutAgree(b_out)))
  )
  a_out = a_in;
  b_out = a_in // b_in << leak here
  Deduce( |- ( InlineAgree("b") ))
  b_out = b_in // << override/mask the leak
  Deduce( |- ( InlineAgree() ))
  assert(T)
}
