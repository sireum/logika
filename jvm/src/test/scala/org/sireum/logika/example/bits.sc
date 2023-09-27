// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.S8._
import org.sireum.S16._
import org.sireum.S32._
import org.sireum.S64._
import org.sireum.U8._
import org.sireum.U16._
import org.sireum.U32._
import org.sireum.U64._

assert(u8"1" << u8"1" == u8"2")
assert(u16"1" << u16"1" == u16"2")
assert(u32"1" << u32"1" == u32"2")
assert(u64"1" << u64"1" == u64"2")
assert(s8"1" << s8"1" == s8"2")
assert(s16"1" << s16"1" == s16"2")
assert(s32"1" << s32"1" == s32"2")
assert(s64"1" << s64"1" == s64"2")
println(S8.random)
assert(s32"-1" < s32"0")
assert(u32"-1" > u32"0")
assert(u32"1".toZ == 1)
assert(s16"-1".toZ == -1)
assert(U64.fromZ(u32"1".toZ) == u64"1")
assert(U8.fromZ(u8"1".toZ) == u8"1")