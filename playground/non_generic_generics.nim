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

when true:
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
  genColumn(KiloGram²)
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

  #let f2 = f{float -> KiloGram: "Kg" ~ `x`.kg}
  #
  #investigateFormula(fn)
  #investigateFormula(f2)
  #
  #proc foo[T](f: FormulaNode[T, T]) =
  #  investigateFormula(f)
  #
  #foo(f{float -> KiloGram: "Kg" ~ `x`.kg})

when false:

  genTypeEnum(KiloGram)
  patchColumn(getTypeEnum(KiloGram))
  type ckg = getColType(KiloGram)
  let c = ckg(kind: colGeneric, gkKind: gkKiloGram, gKiloGram: @[1.kg, 2.kg].toTensor)
  echo c.repr
  echo getTensor(c, Tensor[KiloGram])[1]

  genTypeEnum(KiloGram, Meter)
  patchColumn(getTypeEnum(KiloGram, Meter))
  type ckgm = getColType(KiloGram, Meter)
  let c2 = ckgm(kind: colGeneric, gkKind: gkKiloGram, gKiloGram: @[1.kg, 2.kg].toTensor)
  let c3 = ckgm(kind: colGeneric, gkKind: gkMeter, gMeter: @[1.m, 2.m].toTensor)

  echo c2.pretty
  echo c3.pretty
  #echo c2.getField(KiloGram)[1]
  #echo c3.getField(Meter)[0]

  var df = newDataFrameLike[ckgm]()
  df["blub"] = @[1.2.kg, 2.2.kg].toTensor
  echo df
