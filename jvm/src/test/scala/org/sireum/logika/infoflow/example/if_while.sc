// #Sireum #Logika

import org.sireum._

var num: Z = 0

var s: Z = 0

var result: Z = 0

var b_in: Z = 0
var b_acc: Z = 0


def if_while(): Unit = {
  Contract(
    Modifies(result),
    InfoFlows(
      Flow("num",
        InAgree(num, s),
        OutAgree(result)
      )
    )
  )

  var _result: Z = 0

  if(s > 0) {
    // multiply
    var num_accMult: Z = num
    var counter: Z = s
    while(counter > 0) {
      Invariant(
        Modifies(num_accMult, counter),
        InfoFlowInvariant(
          Flow("num",
            InAgree(num_accMult, num),
            OutAgree(num_accMult)
          )
        )
      )
      num_accMult = num_accMult + num
      counter = counter - 1
    }
    // num -> {cx!30 == num_accMult}
    _result = num_accMult
    assert(T)
  } else {
    // divide
    var num_accDiv: Z = num
    var counter: Z = s
    while(counter < 0) {
      Invariant(
        Modifies(num_accDiv, counter),
        InfoFlowInvariant(
          Flow("num",
            InAgree(num_accDiv, num),
            OutAgree(num_accDiv)
          )
        )
      )
      num_accDiv = num_accDiv - num
      counter = counter + 1
    }
    // num -> {cx!56 == num_accDiv}
    _result = num_accDiv
    assert(T)
  }

  result = _result
  assert(T)
}