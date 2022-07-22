// #Sireum #Logika
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