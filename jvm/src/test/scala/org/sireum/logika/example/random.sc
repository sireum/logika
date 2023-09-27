// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.U64._

val n = Z.random

println(B.random)
assert(B.randomSeed(n) == B.randomSeed(n))

println(ops.COps(C.random).escapeString)
assert(C.randomSeed(n) == C.randomSeed(n))
assert(C.randomBetween('b', 'z') > 'a')
assert(C.randomSeedBetween(n, 'b', 'z') > 'a')
assert(C.randomSeedBetween(n, 'b', 'z') == C.randomSeedBetween(n, 'b', 'z'))

assert(Z.randomSeed(n) == Z.randomSeed(n))
assert(Z.randomBetween(1, 10) > 0)
assert(Z.randomSeedBetween(n, 1, 10) > 0)
assert(Z.randomSeedBetween(n, 1, 10) == Z.randomSeedBetween(n, 1, 10))

assert(R.randomSeed(n) == R.randomSeed(n))
assert(R.randomBetween(r"1", r"10") > r"0")
assert(R.randomSeedBetween(n, r"1", r"10") > r"0")
assert(R.randomSeedBetween(n, r"1", r"10") == R.randomSeedBetween(n, r"1", r"10"))

assert(F32.randomSeed(n) == F32.randomSeed(n))
assert(F32.randomBetween(1f, 10f) > 0f)
assert(F32.randomSeedBetween(n, 1f, 10f) > 0f)
assert(F32.randomSeedBetween(n, 1f, 10f) == F32.randomSeedBetween(n, 1f, 10f))

assert(F64.randomSeed(n) == F64.randomSeed(n))
assert(F64.randomBetween(1d, 10d) > 0d)
assert(F64.randomSeedBetween(n, 1d, 10d) > 0d)
assert(F64.randomSeedBetween(n, 1d, 10d) == F64.randomSeedBetween(n, 1d, 10d))

assert(U64.randomSeed(n) == U64.randomSeed(n))
assert(U64.randomBetween(u64"1", u64"10") > u64"0")
assert(U64.randomSeedBetween(n, u64"1", u64"10") > u64"0")
assert(U64.randomSeedBetween(n, u64"1", u64"10") == U64.randomSeedBetween(n, u64"1", u64"10"))

@enum object Day {
  "Sunday"
  "Monday"
  "Tuesday"
  "Wednesday"
  "Thursday"
  "Friday"
  "Saturday"
}

println(Day.random)
assert(Day.randomSeed(n) == Day.randomSeed(n))
assert(Day.randomBetween(Day.Tuesday, Day.Friday).ordinal > Day.Monday.ordinal)
assert(Day.randomSeedBetween(n, Day.Tuesday, Day.Friday).ordinal > Day.Monday.ordinal)
assert(Day.randomSeedBetween(n, Day.Tuesday, Day.Friday) == Day.randomSeedBetween(n, Day.Tuesday, Day.Friday))
