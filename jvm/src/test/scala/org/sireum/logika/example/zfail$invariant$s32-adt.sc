// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.S32._

@datatype class Temperature_s32(degrees : S32) {
  @spec def AtLeastM460 = Invariant(  degrees >= s32"-460"  )
}

val badS32 = Temperature_s32(s32"-500")