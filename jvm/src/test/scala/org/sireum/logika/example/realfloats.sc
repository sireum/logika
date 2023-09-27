// #Sireum #Logika
//@Logika: --background save
import org.sireum._

assert(F32.NaN.isNaN)
assert(F32.PInf.isInfinite)
assert(F32.NInf.isInfinite)

assert(F64.NaN.isNaN)
assert(F64.PInf.isInfinite)
assert(F64.NInf.isInfinite)

assert(F32.NaN !~ F32.NaN)
assert(F64.NaN !~ F64.NaN)

assert(F32.NaN == F32.NaN)
assert(F64.NaN == F64.NaN)

assert(1f * 1.5f / 1.1f < 2f)
assert(1d * 1.5d / 1.1d < 2d)
assert(r"1" * r"1.5" / r"1.1" < r"2")


var c: F32 = 0f
var l: F32 = 0f
var u: F32 = 0f

def foo(): Unit = {
  Contract(
    Requires(
      c != F32.NaN,
      l != F32.NaN,
      u != F32.NaN
    ),
    Ensures(T)
  )
  if (c < l | c > u) {
    assert(T)
  } else if ((c >= l & c < l + 0.5f) | (c > (u - 0.5f) & c <= u)) {
    assert(T)
  } else if (c >= (l + 0.5f) & c <= (u - 0.5f)) {
    assert(T)
  } else {
    assert(F)
  }
}

def bar(): Unit = {
  Contract(
    Requires(
      c != F32.NaN,
      l != F32.NaN,
      u != F32.NaN
    ),
    Ensures(T)
  )
  setOptions("Logika", """--par --par-branch --rlimit 500000 --timeout 7 --sat-timeout --solver-sat cvc4""")
  if (c < l || c > u) {
    assert(T)
  } else if ((c >= l && c < l + 0.5f) || (c > (u - 0.5f) && c <= u)) {
    assert(T)
  } else if (c >= (l + 0.5f) && c <= (u - 0.5f)) {
    assert(T)
  } else {
    assert(F)
  }
}