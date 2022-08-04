import unchained, measuremancer

import macros
import arraymancer
import datamancer # / [column, value]

#patchColumn(Tensor[Measurement[float]])
import tables, sets # not needed if not called from here `patchDataFrame`


{.experimental: "overloadableEnums".}

proc `%~`[T: SomeUnit](m: T): Value =
  result = newVObject()
  result[$T] = (%~ m.float)

proc makeCol[T](s: seq[T]) =
  var c = toColumn(s.toTensor)
  echo pretty(c)

#var t = toTensor(@[2.kg])
genColumn(KiloGram)
genColumn(Measurement[float])
block:
  let ti = @[1.kg, 2.kg].toTensor
  var c = toColumn(ti)
  echo pretty(c)

  echo c[0, KiloGram] # `c[0, kg]` is broken right now!
  c[0] = 1.5.kg
  echo c

  echo c[0, Value]

block:
  var c = toColumn(@[1.0 ± 0.1, 2.0 ± 0.5].toTensor)
  echo pretty(c)
  echo c[0, Measurement[float]]
  c[0] = 1.5 ± 0.2
  echo c

# good, also works in a generic
let x = @[1.0 ± 0.1, 2.0 ± 0.5]
makeCol(x)

echo "================================================================================"
#patchDataFrame(Tensor[KiloGram])
let df = seqsToDf({"x" : [1,2,3]})
let fn = dfFn(df, f{float -> KiloGram: "y" ~ (`x` * `x`).kg})
echo typeof(fn)

defUnit(kg²)
#genTypeEnum(KiloGram²)
#type kg2Col = patchColumn(KiloGram²)
genColumn(Meter)
#genTypeEnum(Meter)
#type mCol = patchColumn(Meter)

# needs multi generics. to be impl'd next
#let dfNM = dfN.mutate(f{KiloGram -> KiloGram²: "kg2" ~ `kg` * `kg`})


let dfN = extendDataFrame(df, "kg", @[3.kg, 1.kg, 2.kg])
echo dfN.pretty(precision = 10)

echo dfN.arrange("kg", SortOrder.Descending).pretty(precision = 10)
echo dfN.arrange("kg", SortOrder.Ascending).pretty(precision = 10)

genColumn(KiloGram, KiloGram²)
let fn2 = dfFn(dfN, f{KiloGram -> KiloGram²: "kg2" ~ `kg` * `kg`})
echo typeof(fn2)
#
genColumn(KiloGram, Meter)
##genTypeEnum(KiloGram, Meter)
##type ttCol = patchColumn(KiloGram, Meter)
let dfNM = extendDataFrame(dfN, "meter", @[1.m, 2.m, 3.m])
echo dfNM.pretty(precision = 10)

echo df.mutate2(f{float -> KiloGram: "Kg" ~ `x`.kg}).pretty(precision = 10)

echo dfNM.mutate(dfFn(dfNM, f{float: "kgtofoat" ~ idx(`kg`, KiloGram).float}))

echo dfNM.mutate2(f{float: "kgtofoat" ~ idx(`kg`, KiloGram).float})


type
  Foo = object
    x: string
    val: float
proc `<`(f1, f2: Foo): bool = f1.val < f2.val
genColumn(Foo)
# accumulating types works to call mutate w/o df arg
var dFoo = colType(Foo).newDataTable()
dFoo["bar"] = @[Foo(x: "hello", val: 1.1), Foo(x: "world", val: 100.5)]
dFoo = dFoo.mutate(f{Foo -> float: "values" ~ `bar`.val})
echo dFoo.pretty(precision = 30)

# extend simply by accumulating types
## WARNING: generating a column for a type that is an alias may cause problems!
genColumn(KiloGram²)
let df2 = df.mutate(f{int: "kg²" ~ `x`.kg²})
echo df2
