import unittest, math

# need to include `io` in order to test `parseNumber`
include ../src/datamancer/io


template initBuf(): untyped {.dirty.} =
  # `bufStr` is our global string that we modify for each test and `buf` the cor
  var bufStr: string
  var intBuf: int
  var floatBuf: float
  var buf: ptr UncheckedArray[char]

template toBuf(val: string): untyped {.dirty.} =
  # `bufStr` is our global string that we modify for each test and `buf` the cor
  bufStr = val
  buf = cast[ptr UncheckedArray[char]](bufStr[0].addr)

proc `=~=`(a, b: float): bool = abs(a - b) <= abs(a + b) * 1e-8

suite "`parseNumber` tests":
  test "Pure valid integers":
    initBuf()
    template checkInt(v: typed): untyped =
      toBuf($v)
      let ret = buf.parseNumber(sep = ',',
                                idxIn = 0,
                                intBuf, floatBuf)
      check intBuf == v
      check ret == rtInt
      check classify(floatBuf) == fcZero

    # some simple integers
    for i in 0 ..< 50:
      checkInt(i)
      checkInt(-i)

    # some larger integers
    for i in 123456789 .. 123456789 + 50:
      checkInt(i)

    # some edge cases
    checkInt(0)
    # `giant` numbers, currently broken:
    when false:
      checkInt(int.low)
      checkInt(int.high)

  test "Integers with separator":
    initBuf()
    template checkInt(str, val: typed, start: int): untyped =
      toBuf(str)
      let ret = buf.parseNumber(sep = ',',
                                idxIn = start,
                                intBuf, floatBuf)
      check intBuf == val
      check ret == rtInt
      check classify(floatBuf) == fcZero

    # with separator & start at 0
    for i in 0 ..< 50:
      # without space
      checkInt($i & "," & $i, i, start = 0)
      checkInt($(-i) & "," & $(-i), -i, start = 0)
      # including space
      checkInt($i & "," & $i, i, start = 0)

    # with separator & start after separator
    for i in 0 ..< 50:
      checkInt($i & "," & $i, i, start = if i < 10: 2 else: 3)
      if i > 0: # `-0` is just `0` and our `start` would be wrong
        checkInt($(-i) & "," & $(-i), -i, start = if i < 10: 3 else: 4)

    # parse starting on separator yields nothing, return is `rtNaN`
    for i in 0 ..< 50:
      toBuf($i & "," & $i)
      let start = if i < 10: 1 else: 2
      let ret = buf.parseNumber(sep = ',',
                                idxIn = start,
                                intBuf, floatBuf)
      check ret == rtNaN

  test "Pure valid float values":
    initBuf()
    template checkFloat(v: typed, class = fcNormal, retTyp = rtFloat): untyped =
      toBuf($v)
      let ret = buf.parseNumber(sep = ',',
                                idxIn = 0,
                                intBuf, floatBuf)
      if class notin {fcNan, fcInf, fcNegInf}:
        check floatBuf =~= v # this implies we reconstruct the same number as `$` produces!
      check ret == retTyp
      check classify(floatBuf) == class

    template toFloat(i: int): float =
      i.float + 0.12345678910111213

    # some simple integers
    for i in 0 ..< 50:
      checkFloat(toFloat(i))
      checkFloat(toFloat(-i))

    # some larger integers
    for i in 123456789 .. 123456789 + 50:
      checkFloat(toFloat(i))

    # some edge cases
    checkFloat(0.0, class = fcZero)
    checkFloat(-0.0, class = fcZero)
    checkFloat(Inf, class = fcInf, retTyp = rtInf)
    checkFloat(-Inf, class = fcNegInf, retTyp = rtInf)
    checkFloat(NaN, class = fcNan, retTyp = rtNaN)

  test "Valid float values with separator":
    initBuf()
    template checkFloat(str, val: typed, start: int, retTyp = rtFloat, class = fcNormal): untyped =
      toBuf(str)
      let ret = buf.parseNumber(sep = ',',
                                idxIn = start,
                                intBuf, floatBuf)
      if class notin {fcNan, fcInf, fcNegInf}:
        check floatBuf =~= val
      check ret == retTyp
      check classify(floatBuf) == class

    template toFloat(i: int): float =
      i.float + 0.12345678910111213
    # some simple floats
    for i in 0 ..< 50:
      checkFloat($toFloat(i) & "," & $toFloat(i), toFloat(i), start = 0)
      checkFloat($toFloat(-i) & "," & $toFloat(-i), toFloat(-i), start = 0)

    # some larger floats
    for i in 123456789 .. 123456789 + 50:
      checkFloat($toFloat(i) & "," & $toFloat(i), toFloat(i), start = 0)

    # start after first separator
    for i in 123456789 .. 123456789 + 50:
      when defined(nimPreviewFloatRoundtrip):
        checkFloat($toFloat(i) & "," & $toFloat(i), toFloat(i), start = 19)
      else:
        checkFloat($toFloat(i) & "," & $toFloat(i), toFloat(i), start = 18)

    # some exp notation
    checkFloat("1e5", 1e5, start = 0)
    checkFloat("1e-5", 1e-5, start = 0)

    checkFloat("1.2e5", 1.2e5, start = 0)
    checkFloat("1.2e-5", 1.2e-5, start = 0)

    # positive inf first element
    checkFloat("inf,inf", Inf, start = 0, retTyp = rtInf, class = fcInf)
    checkFloat("Inf,Inf", Inf, start = 0, retTyp = rtInf, class = fcInf)
    checkFloat("INF,Inf", Inf, start = 0, retTyp = rtInf, class = fcInf)
    # positive inf second element
    checkFloat("inf,inf", Inf, start = 4, retTyp = rtInf, class = fcInf)
    checkFloat("Inf,Inf", Inf, start = 4, retTyp = rtInf, class = fcInf)
    checkFloat("INF,Inf", Inf, start = 4, retTyp = rtInf, class = fcInf)

    # negative inf first element
    checkFloat("-inf,-inf", Inf, start = 0, retTyp = rtInf, class = fcNegInf)
    checkFloat("-Inf,-Inf", Inf, start = 0, retTyp = rtInf, class = fcNegInf)
    checkFloat("-INF,-Inf", Inf, start = 0, retTyp = rtInf, class = fcNegInf)
    # negative inf second element
    checkFloat("-inf,-inf", Inf, start = 5, retTyp = rtInf, class = fcNegInf)
    checkFloat("-Inf,-Inf", Inf, start = 5, retTyp = rtInf, class = fcNegInf)
    checkFloat("-INF,-Inf", Inf, start = 5, retTyp = rtInf, class = fcNegInf)

    # nan first element
    checkFloat("nan,nan", NaN, start = 0, retTyp = rtNaN, class = fcNan)
    checkFloat("Nan,Nan", NaN, start = 0, retTyp = rtNaN, class = fcNan)
    checkFloat("NAN,Nan", NaN, start = 0, retTyp = rtNaN, class = fcNan)
    # nan second element
    checkFloat("nan,nan", NaN, start = 4, retTyp = rtNaN, class = fcNan)
    checkFloat("Nan,Nan", NaN, start = 4, retTyp = rtNaN, class = fcNan)
    checkFloat("NAN,Nan", NaN, start = 4, retTyp = rtNaN, class = fcNan)

  test "Invalid float values":
    initBuf()
    template checkFloat(str: typed, start: int, retTyp = rtFloat, class = fcNormal): untyped =
      toBuf(str)
      let ret = buf.parseNumber(sep = ',',
                                idxIn = start,
                                intBuf, floatBuf)
      check ret == retTyp
      check classify(floatBuf) == class

    # only signs invalid
    checkFloat("+", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("-", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("+,", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("-,", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("+.", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("-.", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("++++++", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("-+-+-+-+-", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("++++++,---", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("-+-+-+-+-,foo", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("foo,bar", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("foo,bar", start = 4, retTyp = rtError, class = fcZero)

    # invalid floats
    checkFloat("e5",  start = 0, retTyp = rtError, class = fcZero)
    checkFloat("e-5", start = 0, retTyp = rtError, class = fcZero)

    # other invalid strings
    checkFloat("INVALID", start = 0, retTyp = rtError, class = fcZero)
    checkFloat("N/A", start = 0, retTyp = rtError, class = fcZero)
    # any string starting with `E`/`e` is special, as it `E` has a meaning as exponent
    # thus handled differently in the parsing proc
    checkFloat("ERR", start = 0, retTyp = rtError, class = fcZero)

  test "Empty values, line breaks & EOF are NaN":
    initBuf()
    template checkFloat(str: typed, start: int, retTyp = rtFloat, class = fcNormal): untyped =
      toBuf(str)
      let ret = buf.parseNumber(sep = ',',
                                idxIn = start,
                                intBuf, floatBuf)
      check ret == retTyp
      check classify(floatBuf) == class

    # only signs invalid
    checkFloat(",", start = 0, retTyp = rtNaN, class = fcNan)
    checkFloat(",,", start = 1, retTyp = rtNaN, class = fcNan)
    checkFloat("\n", start = 0, retTyp = rtNaN, class = fcNan) # e.g. end of line
    checkFloat("0,1,\n", start = 4, retTyp = rtNaN, class = fcNan) # e.g. end of line
    checkFloat("1,2,3,\0", start = 6, retTyp = rtNaN, class = fcNan) # end of file w/o linebreak
