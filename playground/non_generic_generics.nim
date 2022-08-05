import macros
import arraymancer
import datamancer


# for testing here
import unchained, measuremancer


## Put the overloadable enums into your `nim.cfg`!
{.experimental: "overloadableEnums".}

proc `%~`[T](x: Measurement[T]): Value =
  result = %~ ($x)
  # or
  #result = newVobject()
  #result["val"] = %~ x.value
  #result["uncer"] = %~ x.error
  # depending on if one wants it only for printing or more. Former
  # is better to parse back

defColumn(KiloGram)
defColumn(Measurement[float])
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


# to test type logic works in a generic:
proc makeCol[T](s: seq[T]) =
  var c = toColumn(s.toTensor)
  echo pretty(c)

# good, also works in a generic
let x = @[1.0 ± 0.1, 2.0 ± 0.5]
makeCol(x)

echo "================================================================================"

# define a function using the `dfFn` macro that takes a `DF` to deduce the
# required input / return type of the formula
let df = seqsToDf({"x" : [1,2,3]})
let fn = dfFn(df, f{float -> KiloGram: "y" ~ (`x` * `x`).kg})
echo typeof(fn)

defUnit(kg²)
defColumn(Meter)

# more examples of what's possible
let dfN = extendDataFrame(df, "kg", @[3.kg, 1.kg, 2.kg])
echo dfN.pretty(precision = 10)

# sorting works
echo dfN.arrange("kg", SortOrder.Descending).pretty(precision = 10)
echo dfN.arrange("kg", SortOrder.Ascending).pretty(precision = 10)

defColumn(KiloGram, KiloGram²)
let fn2 = dfFn(dfN, f{KiloGram -> KiloGram²: "kg2" ~ `kg` * `kg`})
echo typeof(fn2)
#
defColumn(KiloGram, Meter)
let dfNM = extendDataFrame(dfN, "meter", @[1.m, 2.m, 3.m])
echo dfNM.pretty(precision = 10)

echo df.mutate2(f{float -> KiloGram: "Kg" ~ `x`.kg}).pretty(precision = 10)

echo dfNM.mutate(dfFn(dfNM, f{float: "kgtofoat" ~ idx(`kg`, KiloGram).float}))

echo dfNM.mutate2(f{float: "kgtofoat" ~ idx(`kg`, KiloGram).float})


block:
  # `to` can be used to change DF type
  doAssert df is DataFrame
  let dfAsKg = df.to(DataTable[colType(KiloGram)])
  doAssert type(dfAsKg) is DataTable[colType(KiloGram)]
  # or
  let dfAsKg2 = df.to(colType(KiloGram))
  doAssert type(dfAsKg2) is DataTable[colType(KiloGram)]

# complex types work (as long as they have simple fields, nothing
# further needed)
type
  Foo = object
    x: string
    val: float
proc `<`(f1, f2: Foo): bool = f1.val < f2.val
defColumn(Foo)
# accumulating types works to call mutate w/o df arg
let fooSeq = @[Foo(x: "hello", val: 1.1), Foo(x: "world", val: 100.5)]

block:
  var dFoo = colType(Foo).newDataTable()
  dFoo["bar"] = fooSeq
  dFoo = dFoo.mutate(f{Foo -> float: "values" ~ `bar`.val})
  echo dFoo.pretty(precision = 30)

# extend simply by accumulating types
## WARNING: generating a column for a type that is an alias may cause problems!
defColumn(KiloGram²)
block:
  let df2 = df.mutate(f{int: "kg²" ~ `x`.kg²})
  echo df2

block:
  # can construct using `toDf` call
  let df2 = toDf(fooSeq)
  echo df2

block:
  # still works with two
  let y = @[1, 2]
  let df2 = toDf(fooSeq, y)
  echo df2

block:
  # also with a single named argument
  let df2 = toDf({"x" : fooSeq})
  echo df2

block:
  # and with Measurement[float]
  let df2 = toDf({"x" : x})
  echo df2


block:
  # and of course mixed
  let y = @[1, 2]
  let df2 = toDf({"x" : x, "y" : y})
  echo df2
