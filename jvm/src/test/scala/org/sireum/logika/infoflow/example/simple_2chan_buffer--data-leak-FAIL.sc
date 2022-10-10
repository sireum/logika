// #Sireum #Logika

import org.sireum._

var a_in: Z = 0
var a_out: Z = 0
var b_in: Z = 0
var b_out: Z = 0

def simple_2chan_buffer_LogikaImpl(): Unit = {
  Contract(
    Modifies(a_out, b_out),
    InfoFlows(
      Flow("a_indOf_b", // should hold
        InAgree(a_in),
        OutAgree(a_out)),
      Flow("b_indOf_a", // should fail
        InAgree(b_in),
        OutAgree(b_out)))
  )
  a_out = a_in
  //b_out = b_in
  b_out = a_in // b_in << leak here
  a_out = b_out
  assert(T)
}
