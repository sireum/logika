// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@range(min = 0 , max = 4, index = T) class I

val a1: IS[I, Z] = IS(1,2,3,4,5)

var a2: IS[I, Z] = IS(1,2,3)
a2 = a2 :+
  6 :+
  7

@range(min = 1, max = 5, index = T) class I2

val b: IS[I2, Z] = IS(1,2,3,4,5)
assert (b.nonEmpty)

assert (I2.Min <= I2.Max)

def d(a3: IS[I, Z]): Unit = {
  val I_Max = I.fromZ(4)

  val isFull: B = a3.size - 1 == I_Max.toZ

  val safe_size = I.fromZ(a3.size - (if (isFull) 1 else 0))
}