// #Sireum

import org.sireum._

@record class Foo(var x: Z)

@datatype class Bar(y: Z)

@record class Baz(foo: Foo, var bar: Bar, z: Z)


val baz = Baz(Foo(0), Bar(10), 100)
baz.foo.x = 1
baz.bar = Bar(2)
assert(baz.foo.x == 1 & baz.bar.y == 2 & baz.z == 100)

