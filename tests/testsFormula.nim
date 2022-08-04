import datamancer, unittest, sequtils, math, strutils, streams, sugar, times
import seqmath

type
  Foo = object
    fd: float

template fails(body: untyped): untyped =
  when compiles(body):
    check false, "Condition " & $astToStr(body) & " succeeded unexpectantly"
  else:
    check true

when (NimMajor, NimMinor, NimPatch) < (1, 6, 0):
  proc isNan(x: float): bool =
    result = classify(x) == fcNaN

suite "Formulas":
  let a = [1, 2, 3]
  let b = [3, 4, 5]
  let c = [4, 5, 6]
  let d = [8, 9, 10]
  let e = [11, 12, 13]
  let f = [false, true, false]
  let g = ["hello", "world", "foo"]
  let h = [2.5, 7.5, NaN]
  let i = ["5", "6", "7"]
  let df = seqsToDf(a, b, c, d, e, f, g, h, i)
  test "Basic `idx` tests with automatic type deduction from context":
    block:
      # - infix, "a" read as integer automatically
      let fn = f{ idx("a") == 5 }
      check fn.evaluate(df).bCol == [false, false, false].toTensor
    block:
      # - infix, a read as float automatically
      let fn = f{ idx("a") == 5.5 }
      check fn.evaluate(df).bCol == [false, false, false].toTensor
    block:
      # - infix involving `in`, type conversion on `idx` and set
      let fn = f{ idx("a").int8 in {1'i8, 3, 5, 7} }
      check fn.evaluate(df).bCol == [true, false, true].toTensor
    block:
      # - infix of `>` works
      # - type determined automatically
      let fn = f{ 5 > idx("a") }
      check fn.evaluate(df).bCol == [true, true, true].toTensor
    block:
      # - infix of `>` works w/ order switched around
      # - type determined automatically
      let fn = f{ idx("a") > 5 }
      check fn.evaluate(df).bCol == [false, false, false].toTensor
    block:
      # - type deduction on one side works with `Value`
      let fn = f{ idx("a") >= %~ 5.5 }
      check fn.evaluate(df).bCol == [false, false, false].toTensor
    block:
      # - reads data as `bool`
      # - runtime error due to a, b being int
      ## TODO: decide if this should become a CT error due to ambiguity.
      ## Probably yes, requires change to `assignType` I suppose (not to use
      ## default type info here)
      expect(ValueError):
        let fn = f{ idx("a") > idx("b") }
        discard fn.evaluate(df)
    block:
      # - RHS is float, infix means LHS will be read as float
      let fn = f{idx("a") < idx("b").float }
      check fn.evaluate(df).bCol == [true, true, true].toTensor
    block:
      # - above works with `==` too
      let fn = f{ idx("a") == idx("b").float }
      check fn.evaluate(df).bCol == [false, false, false].toTensor
    block:
      var fm = Foo(fd: 5.2)
      let fn = f{ idx("a") > fm.fd }
      check fn.evaluate(df).bCol == [false, false, false].toTensor

    block:
      # - prefix, automatic type deduction
      let fn = f{ not idx("f") }
      check fn.evaluate(df).bCol == [true, false, true].toTensor
    block:
      let fn = f{ idx("x") >= max(col("x")) * 0.5 }

    block:
      let fn = f{ parseInt(idx("a")) > 2 }

  test "Basic `col` test with type deduction from context":
    block:
      ## the following fails at CT, because type of output is ambiguous (max is overloaded)
      # let fn = f{ col("a").max }
      ## This one should always work
      let fn2 = f{float: col("a").max }
      check fn2.reduce(df).toInt == 3

    block:
      # - accessing column length works
      let fn = f{float: col("a").len }
      check fn.reduce(df).toInt == 3

    block:
      # - accessing tensor elments with bracket
      let fn = f{float: col("a")[1] }
      check fn.reduce(df).toInt == 2

  test "Automatic type deduction based on nnkDotExpr w/ a (non ambiguous) proc call":
    block:
      # - examples of determining type from unique procedure in a case where
      #   heuristic type extraction fails
      proc uniqueProcWithType(x: int): int =
        x + 5
      let fn = f{ idx("a").uniqueProcWithType }
      check fn.evaluate(df).iCol == [6, 7, 8].toTensor

  test "Automatic type deduction based on `idx` in argument of a call overloaded proc call":
    block:
      # - type deduction based on `idx` in specific argument of a typically overloaded
      #   symbol. Can be deduced due to only single overload matching the arguments
      proc someInt(): int = 2
      proc max(x: int, y: string, z: float, b: int): int =
        result = 5
      let fn = f{ max(idx("a"), "hello", 5.5, someInt()) }
      check fn.evaluate(df).iCol == [5, 5, 5].toTensor

    block:
      # - automatically determines that `a` should be read as `int`
      # - formula is mapping
      let fn = f{ max(idx("a"), 2) }
      check fn.evaluate(df).iCol == [2, 2, 3].toTensor

  test "Formula with an if expression accessing multiple columns":
    block:
      # - formula with an if expression accessing multiple columns
      let fn = f{int -> int: if `a` < 2:
                               `b`
                             else:
                               `c` }
      check fn.evaluate(df).iCol == [3, 5, 6].toTensor

    when (NimMajor, NimMinor, NimPatch) >= (1, 4, 0):
      block:
        ## TODO: 1. we need the parenthesis (otherwise lexer error)
        ## 2. return type is deduced to be bool. It should be taken from
        ## the if expression! `nnkIfExpr` not implemented yet.
        let fn = f{float -> float: "h" ~ (if classify(idx("h")) == fcNaN:
                                            -1.0
                                          else:
                                            `h`)}
        check fn.evaluate(df).fCol == [2.5, 7.5, -1.0].toTensor

  test "Dot expression requiring `Value` input works automatically":
    block:
      # - dot call requiring `Value` argument, output is object column (because
      #   `isNull` returns a boolean as a `Value`
      let fn = f{ idx("a").isNull }
      check fn.evaluate(df).oCol == [%~ false, %~ false, %~ false].toTensor

  test "Infix with `notin` and local array":
    block:
      # - `notin` works and determines `g`
      let existKeys = ["hello"]
      let fn = f{string: `g` notin existKeys}
      check fn.evaluate(df).bCol == [false, true, true].toTensor

  test "`ggplotnim` formula accessing (proc) field of an object":
    block:
      type
        MS = object
          trans: proc(x: float): float
      let col = %~ "a"
      let ms = MS(trans: (proc(x: float): float = 5.5))
      let colStr = "log10(x4)"
      let fn = f{float: colStr ~ ms.trans( df[col.toStr][idx] ) }
      check fn.evaluate(df).fCol == [5.5, 5.5, 5.5].toTensor

  test "`max` overload is resolved in context of infix with float":
    block:
      let fn = f{ `a` >= max(`a`) * 0.5 }
      check fn.evaluate(df).bCol == [false, true, true].toTensor

    block:
      ## TODO: this is technically broken, because from `*` we take `float`
      ## as result and from the integer `-1` we determine the infix to be
      ## integer
      #let fn = f{ -1 * c"hwy"}

  test "Reducing formula with boolean return value":
    block:
      let df2 = seqsToDf({"var1" : toSeq(0 ..< 10)})
      let fn = f{ sum(`var1`) > 20000 }
      check fn.reduce(df2).toBool == false

  test "Example of no `idx` but reducing proc (mean) as a mapping":
    block:
      ## example of a formula that contradicts our assumption that we should error in
      ## case the determined formula kind and the given one mismatch.
      ## In this case we might *want* to assign something + the mean for each element in
      ## the DF (in the context of a `group_by` call this makes sense!
      ## We'll turn it into a warning.
      ## Also: keep in mind that if the user writes something, same as with type hints, we
      ## should value that decision.
      # here we only check it compiles (no CT error anymore)
      let fn = f{float -> float: "subMeanHwy" ~ 0.0 + mean(col("hwy"))}

  test "Name test":
    let f = f{"meanCty" ~ (c"hwy" + c"cty")}
    # name is the full name. Manual parens (nnkPar) are included in representation.
    check f.name == "(~ meanCty ((+ hwy cty)))"

  test "Constant mapping of integer":
    let countCol = "count"
    let fn = f{int: countCol ~ 0}
    check fn.evaluate(df).iCol == [0, 0, 0].toTensor

  test "Name of long formula":
    const cut_rms_trans_low = 0.1
    const cut_rms_trans_high = 1.5
    proc inRegion(x, y: float, r: string): bool =
      discard

    let fn = f{float -> bool:
      `rmsTransverse` >= cut_rms_trans_low and
      `rmsTransverse` <= cut_rms_trans_high and
      inRegion(df["centerX"][idx], df["centerY"][idx], "crSilver") and
      `hits` < 500}

    check $fn == """(and (and (and (>= rmsTransverse cut_rms_trans_low) (<= rmsTransverse cut_rms_trans_high)) (inRegion df["centerX"][idx] df["centerY"][idx] crSilver)) (< hits 500))"""

  test "Explicit types in `col`, `idx`":
    block:
      # explicit types work
      let fn = f{ idx("a", int) }
      check fn.evaluate(df).iCol == [1, 2, 3].toTensor

    block:
      # mixing explicit types work
      let fn = f{ idx("a", int) + idx("i", string).parseInt}
      check fn.evaluate(df).iCol == [6, 8, 10].toTensor

    block:
      # type hints do ``not`` overwrite explicit types
      let fn = f{string -> int: (
        if `g` == "hello":
          idx("a", int)
        else:
          idx("b", int)) }
      check fn.evaluate(df).iCol == [1, 4, 5].toTensor

  test "Add with integer should produce integer":
    let fn = f{"a+5" ~ `a` + 5 }
    check fn.evaluate(df).kind == colInt
    check fn.evaluate(df).iCol == [6, 7, 8].toTensor

  test "Add with float should produce float":
    let fn = f{"a+5.0" ~ `a` + 5.0 }
    check fn.evaluate(df).kind == colFloat
    check fn.evaluate(df).fCol == [6.0, 7.0, 8.0].toTensor

  test "Complex reduction with multiple types and type deduction of `mean`":
    # this was broken up to `v0.1.3`
    let df = seqsToDf({ "x" : @[1, 2, 3, 4, 5], "y" : @["a", "b", "c", "d", "e"] })
    block:
      let fn = f{"mean+ord" << mean(`x`) + ord(max(col(`y`, string))[0]).float }
      check fn.reduce(df).kind == VFloat
      check fn.reduce(df).toFloat == 104.0
    block:
      let fn = f{"mean+ord" << mean(`x`) + col(`y`, string).max[0].ord.float }
      check fn.reduce(df).kind == VFloat
      check fn.reduce(df).toFloat == 104.0

  test "Formula variable name generation":
    # this was broken up to `v0.1.8`, as all variables were turned into `colT`
    # (we just *removed* the part that made each column unique)
    let df = seqsToDf({"0" : [1,1,1], "1" : [2,2,2], "2" : [3,3,3]})
    let fn = f{idx("0") + idx("1") + idx("2")}
    check fn.evaluate(df).toTensor(int) == toTensor [6,6,6]

  test "Formula deducing result type from impure dot expression":
    # this formula cannot determine type of input! Should be easy via explicit float. Related to
    # the one above (same error if parens different )
    ## if we run the following without type hints, we fail to determine the input type
    type
      Second = distinct float
      Hour = distinct float
    proc to[T; U](x: T, dtype: typedesc[U]): U = x.U
    fails:
      # Error: Could not determine data types of tensors in formula:
      #   name: cumulativeTime / h
      #   formula:
      # idx("cumulativeTime / s").Second.to(Hour).float
      #   data type:
      #   output data type: float
      # Consider giving type hints via: `f{T -> U: <theFormula>}`
      discard f{"cumulativeTime / h" ~ idx("cumulativeTime / s").Second.to(Hour).float}
    fails:
      discard f{"cumulativeTime / h" ~ to(idx("cumulativeTime / s").Second, Hour).float}

    # this succeeds successfully
    discard f{float: "cumulativeTime / h" ~ to(Second(idx("cumulativeTime / s")), Hour).float}
    discard f{float: "cumulativeTime / h" ~ idx("cumulativeTime / s").Second.to(Hour).float}

  test "Formula type from dotExpr":
    fails:
      # fails if no input type possible
      discard f{"foo" ~ idx("bar").float}
    fails:
      # type hint & type from body mismatch
      discard f{int -> int: "foo" ~ idx("bar").float}
    # with type hint for input works
    let fn = f{int: "foo" ~ idx("bar").float}
    let df = toDf({"bar" : @[1, 2]})
    let exp = df.mutate(fn)
    check "foo" in exp
    check exp["foo"].kind == colFloat
    check exp["bar"].kind == colInt

  test "Block expression in formula":
    # remove everything that has invalid NaN
    let fn = f{float: (block:
                         let x = idx("B")
                         echo x, " and ", isNaN(x), " and class ", classify(x)
                         not isNaN(idx("B"))) }
    let df = toDf({"B" : @[NaN, 2.0, NaN, 4.0]})
    let exp = df.filter(fn)
    check "B" in exp
    check exp.len == 2
    check exp["B", float] == [2.0, 4.0].toTensor

  test "Formula with complex dot expression chain":
    # this formula was broken! failed in line ~900 in determineTypesImpl due to `pureTree` assertion
    # reason was the `()` at the format
    # works fine now
    let df = seqsToDf({"cycleStart (unix)" : @[1]})
    let exp = df.mutate(f{int -> string: "cycleStart" ~ idx("cycleStart (unix)").fromUnix().inZone(utc()).format("yyyy-MM-dd") })
    check "cycleStart" in exp
    check exp.len == 1
    check exp["cycleStart", string][0] == "1970-01-01"

  test "Regression from ggplotnim recipe formula":
    # should deduce to float
    let fn = f{c"spikes" - c"lineSize" / 2.0}
    check $fn == "(- spikes (/ lineSize 2.0))"
    check fn.kind == fkVector
    let df = toDf({"spikes" : @[1, 2], "lineSize" : @[2, 4]})
    let res = fn.evaluate(df)
    check res.kind == colFloat
    check res.toTensor(int) == @[0, 0].toTensor # compare as int for simplicity

suite "Formulas using the full `formula` macro":
  ## compute the number of cycles & integrated "time on" time
  ## This is still rather basic, but works now.
  ## Things still missing:
  ## - in summarizing formulas, allow to change the `res +=` part
  ##   in case we generate a for loop (e.g. user might want `res -=` or whatever)
  ##   (maybe allow explicit LHS?
  test "Simple full fkVector formula":
    let fn = formula:
      loop:
        "B5" ~ idx("B") * 5
    let df = toDf({"B" : [1, 2]})
    let exp = df.mutate(fn)
    check exp.len == 2
    check "B5" in exp
    check exp["B5", int] == [5, 10].toTensor

  test "Simple full fkScalar formula":
    let fn = formula:
      typeHint: float # read as a float
      loop:
        "Bmean" << mean(`B`)
    let df = toDf({"B" : [1, 2]})
    let exp = df.summarize(fn)
    check exp.len == 1
    check "Bmean" in exp
    check exp["Bmean", float] == [1.5].toTensor

  test "Full fkVector formula with preface":
    ## XXX: should such a formula result in `int`? We know from `Bidx` input that
    ## this is read as `int.` But that knowledge currently isn't used and we fall
    ## back to our `*` heuristics (which we use over the fact that `5` is an integer,
    ## as it's likely the user is lazy about writing `5.0` and forcing the `B` to be
    ## read as `int` by default is bad.
    ## This case is bad though, because just writing it as below results in us generating
    ## a bad closure that will cause a CT error from the generated code.
    ## We should introduce something like a notion of "narrowest type" for the full
    ## body. We only have this in a very restricted sense.
    fails: ## XXX: this *should not* fail / it should fail with a custom error message!
      let fn = formula:
        preface:
          Bidx in df["B", int]
        loop:
          "B5" ~ Bidx * 5 # result will be float due to `*` heuristics
    let fn = formula:
      preface:
        Bidx in df["B", int]
      typeHint: int -> int
      loop:
        "B5" ~ Bidx * 5 # result will be float due to `*` heuristics
    let df = toDf({"B" : [1, 2]})
    let exp = df.mutate(fn)
    check exp.len == 2
    check "B5" in exp
    check exp["B5", int] == [5, 10].toTensor

  test "Full fkVector formula with preface & applied proc in preface":
    proc foo(t: Tensor[int]): Tensor[float] =
      result = t.map_inline(x.float * 2.0)
    let fn = formula:
      preface:
        Bidx in foo(df["B", int])
      loop:
        "B5" ~ Bidx * 5 # result will be float due to `*` heuristics
    let df = toDf({"B" : [1, 2]})
    let exp = df.mutate(fn)
    check exp.len == 2
    check "B5" in exp
    check exp["B5", float] == [10.0, 20.0].toTensor

  test "Full fkScalar formula with custom reduction fails w/o `res` in preface":
    fails: ## this fails, because it does not define the `res` in preface!
      let fn = formula:
        typeHint: int -> int
        loop:
          "Bprod" << (res *= `B`) ## Needs to be inside parens or in `block`! Parser...

  test "Full fkScalar formula with custom reduction, `+=`":
    let fn = formula:
      typeHint: int -> int
      preface:
        var res = 0
      loop:
        "Bsum" << (res += `B`) ## Needs to be inside parens or in `block`! Parser...
    let df = toDf({"B" : [1, 2]})
    let exp = df.summarize(fn)
    check exp.len == 1
    check "Bsum" in exp
    check exp["Bsum", int][0] == 3

  test "Full fkScalar formula with custom reduction, `*=`":
    let fn = formula:
      preface:
        var res = 1
      typeHint: int -> int
      loop:
        "Bprod" << (res *= `B`) ## Needs to be inside parens or in `block`! Parser...
    let df = toDf({"B" : [1, 2]})
    let exp = df.summarize(fn)
    check exp.len == 1
    check "Bprod" in exp
    check exp["Bprod", int][0] == 2

  test "Full fkVector formula with custom variable declaration":
    let fn = formula:
      preface:
        var count = 0
      typeHint: int -> int
      loop:
        "B10" ~ (block:
          if count > 0:
            `B` * 10
          else:
            inc count
            0
        )
    let df = toDf({"B" : [1, 2]})
    let exp = df.mutate(fn)
    check exp.len == 2
    check "B10" in exp
    check exp["B10", int] == [0, 20].toTensor

  test "Complex `fkScalar` reduction with preface, if/else and transformation":
    let fn = formula:
      preface:
        lagIdx in lag(df["Time", float], fill = Inf)
        var res = 0.0
      loop:
        "sumTime" << (
          res += (block:
                    if idx("B") > 1.0:
                      idx("Time") - lagIdx
                    else:
                      0.0))
    let df = toDf({"B" : [0.0, 0.5, 1.5, 2.5], "Time" : @[10, 20, 30, 40]})
    let exp = df.summarize(fn)
    check exp.len == 1
    check "sumTime" in exp
    check exp["sumTime", float][0] == 20.0

  ## make sure this  works (i.e. `in` usage with non `forEach` generated, i.e. string column
  when false:
    let fn = formula:
      preface:
        lag in lag(df["Foo", string])
      loop:
        # some loop that uses `lag`. Will generate `for` instead of `forEach` due to `string`
        # could needs to replace `lag` by `lag[idx]`!
        discard
