// #Sireum #Logika
//@Logika: --background save
import org.sireum._

@pure def inc(x: Z): Z = {
  Contract(
    Ensures(Res == x + 1)
  )
  return x + 1
}