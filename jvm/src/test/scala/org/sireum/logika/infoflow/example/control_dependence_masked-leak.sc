// #Sireum #Logika
import org.sireum._

;var a_in : Z = 0
;var a_out : Z = 0
;var b_in : Z = 0
;var b_out: Z = 0

def control_dependence_masked_leak(): Unit = {
  Contract(
    Modifies(b_out),
    InfoFlows(
      Flow("b_indOf_a",
        InAgree(b_in),
        OutAgree(b_out)))
  )
  if (a_in > 0) { // same "agreed" value assigned in either branch so no leak
    b_out = b_in
  } else {
    b_out = b_in
  }
  assert(T)
}
