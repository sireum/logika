// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@datatype class Temperature_f32(degrees : F32) {
  @spec def AbsZero = Invariant(  degrees >= -459.67f  )
}

val badF32 = Temperature_f32(-500f)