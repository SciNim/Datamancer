import datamancer, unittest, sequtils, math, strutils, streams, sugar, sets, tables
import algorithm
import seqmath
from os import removeFile

when not declared(AssertionDefect):
  type AssertionDefect = AssertionError

suite "Column":
  test "Constant columns":
    let c = constantColumn(12, 100)
    check c.kind == colConstant
    check c.len == 100
    check c.cCol == %~ 12

    for i in 0 ..< c.len:
      check c[i, int] == 12

  test "Column form a scalar":
    block Int:
      let x = 1
      let c = toColumn x
      check c.kind == colInt
      check c.toTensor(int) == [1].toTensor
    block Float:
      let x = 1.0
      let c = toColumn x
      check c.kind == colFloat
      check c.toTensor(float) == [1.0].toTensor
    block String:
      let x = "1"
      let c = toColumn x
      check c.kind == colString
      check c.toTensor(string) == ["1"].toTensor
    block Bool:
      let x = true
      let c = toColumn x
      check c.kind == colBool
      check c.toTensor(bool) == [true].toTensor

  test "Column from scalar Value yields native":
    block Int:
      let x = %~ 1
      let c = toColumn x
      check c.kind == colInt
      check c.toTensor(int) == [1].toTensor
    block Float:
      let x = %~ 1.0
      let c = toColumn x
      check c.kind == colFloat
      check c.toTensor(float) == [1.0].toTensor
    block String:
      let x = %~ "1"
      let c = toColumn x
      check c.kind == colString
      check c.toTensor(string) == ["1"].toTensor
    block Bool:
      let x = %~ true
      let c = toColumn x
      check c.kind == colBool
      check c.toTensor(bool) == [true].toTensor

  test "Adding two equal constant columns":
    let c1 = constantColumn(12, 40)
    let c2 = constantColumn(12, 60)
    check c1.len == 40
    check c1.cCol == %~ 12
    check c2.len == 60
    check c2.cCol == %~ 12

    let res = add(c1, c2)
    check res.kind == colConstant
    check res.cCol == %~ 12
    check res.len == 100

  test "Adding two unequal constant columns of same value type":
    let c1 = constantColumn(12, 40)
    let c2 = constantColumn(14, 60)
    check c1.len == 40
    check c1.cCol == %~ 12
    check c2.len == 60
    check c2.cCol == %~ 14

    let res = add(c1, c2)
    check res.kind == colInt
    check res.len == 100
    for i in 0 ..< 100:
      if i < 40:
        check res[i, int] == 12
      else:
        check res[i, int] == 14

  test "Adding two unequal constant columns of int & float":
    let c1 = constantColumn(12, 40)
    let c2 = constantColumn(14.0, 60)
    check c1.len == 40
    check c1.cCol == %~ 12
    check c2.len == 60
    check c2.cCol == %~ 14.0

    let res = add(c1, c2)
    check res.kind == colFloat
    check res.len == 100
    for i in 0 ..< 100:
      if i < 40:
        check res[i, float] == 12.0
      else:
        check res[i, float] == 14.0

  test "Adding two unequal constant columns of different types":
    let c1 = constantColumn(12, 40)
    let c2 = constantColumn("foo", 60)
    check c1.len == 40
    check c1.cCol == %~ 12
    check c2.len == 60
    check c2.cCol == %~ "foo"

    let res = add(c1, c2)
    check res.kind == colObject
    check res.len == 100
    for i in 0 ..< 100:
      if i < 40:
        check res[i, Value] == %~ 12.0
      else:
        check res[i, Value] == %~ "foo"

  test "Adding non constant to (equal type) constant column results in native type":
    let c1 = constantColumn(5, 5)
    let c2 = toColumn [1, 2, 3, 4, 5]
    check c1.len == 5
    check c1.cCol == %~ 5
    check c2.len == 5
    check c2.kind == colInt

    let res = add(c1, c2)
    check res.kind == colInt
    check res.len == 10
    check res[0 ..< 5].toTensor(int) == [5, 5, 5, 5, 5].toTensor
    check res[5 ..< 10].toTensor(int) == [1, 2, 3, 4, 5].toTensor

  test "Adding non constant to (compatible type) constant column results in native type":
    let c1 = constantColumn(5.0, 5)
    let c2 = toColumn [1, 2, 3, 4, 5]
    check c1.len == 5
    check c1.cCol == %~ 5.0
    check c2.len == 5
    check c2.kind == colInt

    let res = add(c1, c2)
    check res.kind == colFloat
    check res.len == 10
    check res[0 ..< 5].toTensor(float) == [5.0, 5.0, 5.0, 5.0, 5.0].toTensor
    check res[5 ..< 10].toTensor(float) == [1.0, 2.0, 3.0, 4.0, 5.0].toTensor

  test "Slice assignment to constant column of compatible type leads to native column":
    block Single:
      var c1 = constantColumn(5, 5)
      check c1.len == 5
      check c1.cCol == %~ 5.0

      c1[3] = 4
      check c1.kind == colInt
      check c1.toTensor(int) == [5, 5, 5, 4, 5].toTensor
    block Slice:
      var c1 = constantColumn(5, 5)
      check c1.len == 5
      check c1.cCol == %~ 5.0

      c1[3 .. 4] = [1, 2].toTensor
      check c1.kind == colInt
      check c1.toTensor(int) == [5, 5, 5, 1, 2].toTensor

  test "Conversion of constant column results to tensor":
    let c = constantColumn(12, 40)
    check c.toTensor(0 .. 10, int) == newTensorWith(11, 12)
    check c.toTensor(int) == newTensorWith(40, 12)

  test "Lag - lag a tensor by 1 element, fill `default(T)`":
    block Int:
      let t = [1, 2, 3].toTensor
      let exp = t.lag()
      check exp.len == t.len
      check exp[0] == 0 # default(int)
      check exp == [0, 1, 2].toTensor
    block Float:
      let t = [1.0, 2.0, 3.0].toTensor
      let exp = t.lag()
      check exp.len == t.len
      check exp[0] == 0.0 # default(float)
      check exp == [0.0, 1.0, 2.0].toTensor
    block String:
      let t = ["1", "2", "3"].toTensor
      let exp = t.lag()
      check exp.len == t.len
      check exp[0] == "" # default(string)
      check exp == ["", "1", "2"].toTensor

  test "Lag - lag a tensor by 2 element, fill `default(T)`":
    block Int:
      let t = [1, 2, 3].toTensor
      let exp = t.lag(n = 2)
      check exp.len == t.len
      check exp[0] == 0 # default(int)
      check exp[1] == 0 # default(int)
      check exp == [0, 0, 1].toTensor
    block Float:
      let t = [1.0, 2.0, 3.0].toTensor
      let exp = t.lag(n = 2)
      check exp.len == t.len
      check exp[0] == 0.0 # default(float)
      check exp[1] == 0.0 # default(float)
      check exp == [0.0, 0.0, 1.0].toTensor
    block String:
      let t = ["1", "2", "3"].toTensor
      let exp = t.lag(n = 2)
      check exp.len == t.len
      check exp[0] == "" # default(string)
      check exp[1] == "" # default(string)
      check exp == ["", "", "1"].toTensor

  test "Lag - lag a tensor by 1 element, custom fill":
    block Int:
      let t = [1, 2, 3].toTensor
      let exp = t.lag(fill = int.high)
      check exp.len == t.len
      check exp[0] == int.high # default(int)
      check exp == [int.high, 1, 2].toTensor
    block Float:
      let t = [1.0, 2.0, 3.0].toTensor
      let exp = t.lag(fill = NaN)
      check exp.len == t.len
      check classify(exp[0]) == fcNaN # default(float)
      check exp[1 .. 2] == [1.0, 2.0].toTensor
    block String:
      let t = ["1", "2", "3"].toTensor
      let exp = t.lag(fill = "foo")
      check exp.len == t.len
      check exp[0] == "foo" # default(string)
      check exp == ["foo", "1", "2"].toTensor

  test "Lag - lag a column by 1 element, fill `default(T)`":
    block Int:
      let c = toColumn [1, 2, 3]
      let exp = c.lag()
      check exp.len == c.len
      check exp[0, int] == 0 # default(int)
      check exp.toTensor(int) == [0, 1, 2].toTensor
    block Float:
      let c = toColumn [1.0, 2.0, 3.0]
      let exp = c.lag()
      check exp.len == c.len
      check exp[0, float] == 0.0 # default(float)
      check exp.toTensor(float) == [0.0, 1.0, 2.0].toTensor
    block String:
      let c = toColumn ["1", "2", "3"]
      let exp = c.lag()
      check exp.len == c.len
      check exp[0, string] == "" # default(string)
      check exp.toTensor(string) == ["", "1", "2"].toTensor

  test "Lead - lead a tensor by 1 element, fill `default(T)`":
    block Int:
      let t = [1, 2, 3].toTensor
      let exp = t.lead()
      check exp.len == t.len
      check exp[2] == 0 # default(int)
      check exp == [2, 3, 0].toTensor
    block Float:
      let t = [1.0, 2.0, 3.0].toTensor
      let exp = t.lead()
      check exp.len == t.len
      check exp[2] == 0.0 # default(float)
      check exp == [2.0, 3.0, 0.0].toTensor
    block String:
      let t = ["1", "2", "3"].toTensor
      let exp = t.lead()
      check exp.len == t.len
      check exp[2] == "" # default(string)
      check exp == ["2", "3", ""].toTensor

  test "Lead - lead a tensor by 2 element, fill `default(T)`":
    block Int:
      let t = [1, 2, 3].toTensor
      let exp = t.lead(n = 2)
      check exp.len == t.len
      check exp[1] == 0 # default(int)
      check exp[2] == 0 # default(int)
      check exp == [3, 0, 0].toTensor
    block Float:
      let t = [1.0, 2.0, 3.0].toTensor
      let exp = t.lead(n = 2)
      check exp.len == t.len
      check exp[1] == 0.0 # default(float)
      check exp[2] == 0.0 # default(float)
      check exp == [3.0, 0.0, 0.0].toTensor
    block String:
      let t = ["1", "2", "3"].toTensor
      let exp = t.lead(n = 2)
      check exp.len == t.len
      check exp[1] == "" # default(string)
      check exp[2] == "" # default(string)
      check exp == ["3", "", ""].toTensor

  test "Lead - lead a tensor by 1 element, custom fill":
    block Int:
      let t = [1, 2, 3].toTensor
      let exp = t.lead(fill = int.high)
      check exp.len == t.len
      check exp[2] == int.high # default(int)
      check exp == [2, 3, int.high].toTensor
    block Float:
      let t = [1.0, 2.0, 3.0].toTensor
      let exp = t.lead(fill = NaN)
      check exp.len == t.len
      check classify(exp[2]) == fcNaN # default(float)
      check exp[0 .. 1] == [2.0, 3.0].toTensor
    block String:
      let t = ["1", "2", "3"].toTensor
      let exp = t.lead(fill = "foo")
      check exp.len == t.len
      check exp[2] == "foo" # default(string)
      check exp == ["2", "3", "foo"].toTensor

  test "Lead - lead a column by 1 element, fill `default(T)`":
    block Int:
      let c = toColumn [1, 2, 3]
      let exp = c.lead()
      check exp.len == c.len
      check exp[2, int] == 0 # default(int)
      check exp.toTensor(int) == [2, 3, 0].toTensor
    block Float:
      let c = toColumn [1.0, 2.0, 3.0]
      let exp = c.lead()
      check exp.len == c.len
      check exp[2, float] == 0.0 # default(float)
      check exp.toTensor(float) == [2.0, 3.0, 0.0].toTensor
    block String:
      let c = toColumn ["1", "2", "3"]
      let exp = c.lead()
      check exp.len == c.len
      check exp[2, string] == "" # default(string)
      check exp.toTensor(string) == ["2", "3", ""].toTensor

suite "DataTable parsing":
  proc cmpElements[T](s1, s2: seq[T]): bool =
    # comparse the two seq, while properly handling `NaN`
    result = true
    for (x, y) in zip(s1, s2):
      when T is float:
        if classify(x) == fcNaN xor classify(y) == fcNaN:
          return false
        elif classify(x) != fcNaN and classify(y) != fcNaN:
          if not almostEqual(x, y): return false
        # else both NaN
      else:
        if x != y: return false


  test "Parsing with inf, NaN":
    let exp = """w,x,y,z
1,10,0.1,100
2,ERR,inf,200
NaN,N/A,0.3,300
4,40,0.4,400"""

    let exp2 = exp & "\n"
    let exp3 = exp & "\n\n"
    let exp4 = exp & "\n\n\n"

    template checkBlock(arg: typed): untyped {.dirty.} =
      let df = parseCsvString(arg)
      check df["w"].kind == colFloat
      check df["x"].kind == colObject # because of invalid floats
      check df["y"].kind == colFloat
      check df["z"].kind == colInt
      check cmpElements(df["w", float].toSeq1D, @[1'f64, 2, NaN, 4])
      check cmpElements(df["x", Value].toSeq1D, @[%~ 10, %~ "ERR", %~ "N/A", %~ 40])
      check cmpElements(df["y", float].toSeq1D, @[0.1, Inf, 0.3, 0.4])
      check cmpElements(df["z", int].toSeq1D, @[100, 200, 300, 400])

    block NoNewline:
      checkBlock(exp)
    block OneNewline:
      checkBlock(exp2)
    block TwoNewlines:
      checkBlock(exp3)
    block ThreeNewlines:
      checkBlock(exp4)

  test "Parsing with newlines after data":
    let exp = """x,y,z
1,2,3
4,5,6
7,8,9


"""
    template checkBlock(): untyped {.dirty.} =
      check df["x"].kind == colInt
      check df["y"].kind == colInt
      check df["z"].kind == colInt

      check df["x", int] == toTensor([1,4,7])
      check df["y", int] == toTensor([2,5,8])
      check df["z", int] == toTensor([3,6,9])

    block FromString:
      let df = parseCsvString(exp)
      checkBlock()
    block FromFile:
      let path = "/tmp/test_newlines_datamancer.csv"
      when defined(linux):
        ## XXX: use proper temp handling to check on other OSs
        writeFile(path, exp)
        let df = readCsv(path)
        checkBlock()
        removeFile(path)

  test "Parsing with missing values, float":
    let exp = """x,y,z
1,2,
4,,6
,8,9
"""
    template checkBlock(): untyped {.dirty.} =
      check df["x"].kind == colFloat
      check df["y"].kind == colFloat
      check df["z"].kind == colFloat
      check cmpElements(df["x", float].toSeq1D, @[1'f64,4,NaN])
      check cmpElements(df["y", float].toSeq1D, @[2'f64,NaN,8])
      check cmpElements(df["z", float].toSeq1D, @[NaN,6,9])

    block FromString:
      let df = parseCsvString(exp)
      checkBlock()

    block FromFile:
      let path = "/tmp/test_missing_datamancer.csv"
      when defined(linux):
        ## XXX: use proper temp handling to check on other OSs
        writeFile(path, exp)
        let df = readCsv(path)
        checkBlock()
        removeFile(path)

  test "Parsing with missing values, string":
    let exp = """x,y,z
a,2,
aa,3,
b,,foo
,8,bar
"""
    template checkBlock(): untyped {.dirty.} =
      check df["x"].kind == colString
      check df["y"].kind == colFloat
      check df["z"].kind == colString
      check cmpElements(df["x", string].toSeq1D, @["a", "aa", "b", ""])
      check cmpElements(df["y", float].toSeq1D, @[2'f64,3,NaN,8])
      check cmpElements(df["z", string].toSeq1D, @["","","foo","bar"])

    block FromString:
      let df = parseCsvString(exp)
      checkBlock()

    block FromFile:
      let path = "/tmp/test_missing_string_datamancer.csv"
      when defined(linux):
        ## XXX: use proper temp handling to check on other OSs
        writeFile(path, exp)
        let df = readCsv(path)
        checkBlock()
        removeFile(path)

  test "Parsing with fully column":
    ## Reported by @KosKosynsky on the Nim #science channel
    let data = """,ID of record,Record number,date_from,date_to,(Name) Additional name if exists,Canal
0,29528,173/MZS/2020,2020/08-04,2021-08-03,,DE
1,29529,113/KEK/1443,2020-08-11,2021-08-10,,DE
2,29530,148/BBK/1527,2020-08-12,2021-08-11,,DE
3,29531,159/ROT/2769,2020-08-13,2021-08-12,,DE
4,29532,745/REZ/3265,2020-08-20,2021-08-19,,DE
5,29533,158/GTK/2144,2020/08-25,2021-0824,,DE
6,29534,151/ZEB/1654,2020-08-28,2021-08-27,,DE
7,29535,158/MTG/6526,2020-08-23,2021-08-22,,DE
"""
    let df = parseCsvString(data)
    check df.getKeys.len == 7
    check "(Name) Additional name if exists" in df
    check "Unnamed0" in df
    check df["(Name) Additional name if exists"].kind == colObject
    check df["(Name) Additional name if exists", Value][0] == null()

suite "DataTable tests":

  test "`toDf` is no-op for DF":
    let df = toDf(toDf(readCsv("data/mpg.csv")))
    check df["class", string] == readCsv("data/mpg.csv")["class", string]

  test "`toDf` works on an OrderedTable[string, seq[string]]":
    var tab = initOrderedTable[string, seq[string]]()
    tab["x"] = @["1", "2"]
    tab["y"] = @["4", "5"]
    let df = toDf(tab)
    check df["x", int] == [1, 2].toTensor
    check df["y", int] == [4, 5].toTensor

  test "`toDf` works on an OrderedTable[string, seq[Value]]":
    var tab = initOrderedTable[string, seq[Value]]()
    tab["x"] = @[%~ 1, %~ 2]
    tab["y"] = @[%~ 4, %~ 5]
    let df = toDf(tab)
    check df["x", int] == [1, 2].toTensor
    check df["y", int] == [4, 5].toTensor

  test "`toDf` works for a single identifier":
    let x = @[1, 2, 3]
    let df = toDf(x)
    check "x" in df
    check df["x", int] == [1, 2, 3].toTensor

  test "`toDf` works for multiple identifiers":
    let x = @[1, 2, 3]
    let y = @[4, 5, 6]
    let df = toDf(x, y)
    check "x" in df
    check df["x", int] == [1, 2, 3].toTensor
    check "y" in df
    check df["y", int] == [4, 5, 6].toTensor

  test "`toDf` works for a single call":
    proc foo(): seq[int] =
      result = @[1, 2, 3]
    let df = toDf(foo())
    check "foo()" in df
    check df["foo()", int] == [1, 2, 3].toTensor

  test "`toDf` works for multiple calls":
    proc foo(): seq[int] =
      result = @[1, 2, 3]
    proc bar(): seq[string] =
      result = @["a", "b", "c"]
    let df = toDf(foo(), bar())
    check "foo()" in df
    check df["foo()", int] == [1, 2, 3].toTensor
    check "bar()" in df
    check df["bar()", string] == ["a", "b", "c"].toTensor

  test "`toDf` works for a single TableConstr element":
    let x = @[1, 2, 3]
    let df = toDf({"x" : x})
    check "x" in df
    check df["x", int] == [1, 2, 3].toTensor

  test "`toDf` works for multiple TableConstr elements":
    let x = @[1, 2, 3]
    let y = @[4, 5, 6]
    let df = toDf({"x" : x, "y" : y})
    check "x" in df
    check df["x", int] == [1, 2, 3].toTensor
    check "y" in df
    check df["y", int] == [4, 5, 6].toTensor

  test "`toDf` works for a single call in a TableConstr":
    proc foo(): seq[int] =
      result = @[1, 2, 3]
    let df = toDf({"x" : foo()})
    check "x" in df
    check df["x", int] == [1, 2, 3].toTensor

  test "`toDf` works for multiple calls in a TableConstr":
    proc foo(): seq[int] =
      result = @[1, 2, 3]
    proc bar(): seq[string] =
      result = @["a", "b", "c"]
    let df = toDf({"x" : foo(), "y" : bar()})
    check "x" in df
    check df["x", int] == [1, 2, 3].toTensor
    check "y" in df
    check df["y", string] == ["a", "b", "c"].toTensor

  test "Creation of DFs from seqs":
    let a = [1, 2, 3]
    let b = [3, 4, 5]
    let c = [4, 5, 6]
    let d = [8, 9, 10]
    # creation directly from a,b,c,d
    block:
      let df = toDf(a, b, c, d)
      check "a" in df
      check "b" in df
      check "c" in df
      check "d" in df
    # creation via key / value pairs
    block:
      let df = toDf({ "one" : a,
                      "two" : b,
                      "three" : c,
                      "four" : d})
      check "one" in df
      check "two" in df
      check "three" in df
      check "four" in df

  #test "Creation of DF w/ int, float other than int64, float64":
  #  let a = @[123'u8, 12, 55]
  #  let b = @[1.123'f32, 4.234, 1e12]
  #  let c = @[1001'i32, 1002, 1003]
  #  genColumn(uint8)
  #  #genColumn(uint8, float32, int32)
  #  var df = seqsToDf({ "a" : a,
  #                      "b" : b })
  #  check df["a"].kind == colInt
  #  check df["b"].kind == colFloat
  #  check df["a"].toTensor(int) == a.toTensor.asType(int)
  #  check df["b"].toTensor(float) == b.toTensor.asType(float)
  #  # check toColumn directly
  #  df["c"] = toColumn c
  #  check df["c"].kind == colInt
  #  check df["c"].toTensor(int) == c.toTensor.asType(int)

  #test "Accessed column of DF is mutable / reference semantics":
  #  let a = @[123'u8, 12, 55]
  #  let aRepl = @[123'u8, 12, 33]
  #  let b = @[1.123'f32, 4.234, 1e12]
  #  var df = seqsToDf({ "a" : a })
  #  check df["a"].kind == colInt
  #  check df["a"].toTensor(int) == a.toTensor.asType(int)
  #  df["a"][df.high] = 33
  #  check df["a"].kind == colInt
  #  check df["a"].toTensor(int) == aRepl.toTensor.asType(int)
  #  df["a"] = b
  #  check df["a"].kind == colFloat
  #  check df["a"].toTensor(float) == b.toTensor.asType(float)
  #
  #  # check reference semantics
  #  let bMod = @[1.123'f32, 4.234, 1e4]
  #  var colB = df["a"]
  #  # modifying `colB` modifies `df["a"]`
  #  colB[df.high] = 1e4
  #  check df["a"].toTensor(float) == bMod.toTensor.asType(float)
  #
  #  # modifying underlying tensor modifies data too
  #  let bMod2 = @[1.123'f32, 4.234, 1e6]
  #  var tensorB = df["a"].toTensor(float)
  #  tensorB[df.high] = 1e6
  #  check df["a"].toTensor(float) == bMod2.toTensor.asType(float)

  test "Extending a DF by a column":
    let a = [1, 2, 3]
    let b = [3, 4, 5]
    let c = [4, 5, 6]
    let d = [8, 9, 10]
    block:
      ## NOTE: This "manual" way of adding a column to an existing data frame
      ## is sort of "low level" at the moment. What this means is that the
      ## size of the given sequence is ``not`` checked at the moment. So take
      ## care that you actually hand a sequence of the same length as the DF!
      # create DF of the first 3 seqs
      var df = toDf({ "one" : a,
                      "two" : b,
                      "three" : c })
      check "one" in df
      check "two" in df
      check "three" in df
      check "four" notin df
      # and now add fourth manually
      df["four"] = d
      check "four" in df

    block:
      ## This version checks the length and fails if they don't match
      # create DF of the first 3 seqs
      var df = toDf({ "one" : a,
                      "two" : b,
                      "three" : c })
      check "one" in df
      check "two" in df
      check "three" in df
      check "four" notin df
      # and now add fourth manually
      df["four"] = d
      check "four" in df
    block:
      # check fails if length is longer
      let e = [1, 2, 3, 4, 5]
      # create DF of the first 3 seqs
      var df = toDf({ "one" : a,
                      "two" : b,
                      "three" : c })
      check "one" in df
      check "two" in df
      check "three" in df
      check "five" notin df
      # and now add fourth manually
      expect(ValueError):
        df["five"] = e
    block:
      # check fails if length is shorter
      let e = [1, 2]
      # create DF of the first 3 seqs
      var df = toDf({ "one" : a,
                      "two" : b,
                      "three" : c })
      check "one" in df
      check "two" in df
      check "three" in df
      check "five" notin df
      # and now add last manually
      expect(ValueError):
        df["five"] = e

    block:
      # check if we can override existing column
      let e = [11, 22, 33]
      # create DF of the first 3 seqs
      var df = toDf({ "one" : a,
                      "two" : b,
                      "three" : c,
                      "four" : c}) # assign four as `c`
      check "one" in df
      check "two" in df
      check "three" in df
      check "four" in df
      # check `"four"` is `c`
      check df["four"].toTensor(int) == c.toTensor
      # assign actual `"four"`
      df["four"] = e
      # check `"four"` is now `d`
      check df["four"].toTensor(int) == e.toTensor


  test "Testing `bind_rows`":
    let a = [1, 2, 3]
    let b = [3, 4, 5]

    let c = [4, 5, 6, 7]
    let d = [8, 9, 10, 11]
    block:
      # bind_rows with automatic `ids`, both having same columns
      let df = toDf({"a" : a, "b" : b})
      let df2 = toDf({"a" : c, "b" : d})
      let res = bind_rows([df, df2])
      check res["a"].toTensor(int) == concat(a.toTensor(), c.toTensor(), axis = 0)
      check res["b"].toTensor(int) == concat(b.toTensor(), d.toTensor(), axis = 0)
      # without specifying `id`, no column will be added
      #check toSeq(res["id"]) == %~ concat(toSeq(0..<a.len).mapIt("0"),
      #                                      toSeq(0..<c.len).mapIt("1"))
    block:
      # bind_rows with automatic `ids`, having different columns
      let df = toDf({"a" : a, "b" : b})
      let df2 = toDf({"a" : c, "d" : d})
      let res = bind_rows([df, df2])
      check res["a"].toTensor(int) == concat(a.toTensor, c.toTensor, axis = 0)
      check res["b"].toTensor(Value) == concat(toTensor(%~ b),
                                               toTensor(toSeq(0 .. 3).mapIt(Value(kind: VNull))),
                                               axis = 0)
      check res["d"].toTensor(Value) == concat(toTensor(toSeq(0 .. 2).mapIt(Value(kind: VNull))),
                                               toTensor(%~ d),
                                               axis = 0)

      #check toSeq(res["id"]) == %~ concat(toSeq(0..<a.len).mapIt("0"),
      #                                      toSeq(0..<c.len).mapIt("1"))
    block:
      # bind_rows with custom `id` name, both having same columns
      let df = toDf({"a" : a, "b" : b})
      let df2 = toDf({"a" : c, "b" : d})
      let res = bind_rows([df, df2], id = "combine")
      check res["a"].toTensor(int) == concat(a.toTensor(), c.toTensor(), axis = 0)
      check res["b"].toTensor(int) == concat(b.toTensor(), d.toTensor(), axis = 0)
      check res["combine"].toTensor(string) == concat(toTensor(toSeq(0..<a.len).mapIt("0")),
                                                      toTensor(toSeq(0..<c.len).mapIt("1")),
                                                      axis = 0)


    block:
      # bind_rows with custom `id` name, custom `id` values, both having same columns
      let df = toDf({"a" : a, "b" : b})
      let df2 = toDf({"a" : c, "b" : d})
      let res = bind_rows([("one", df), ("two", df2)], id = "combine")
      check res["a"].toTensor(int) == concat(a.toTensor, c.toTensor, axis = 0)
      check res["b"].toTensor(int) == concat(b.toTensor, d.toTensor, axis = 0)
      check res["combine"].toTensor(string) == concat(toTensor(toSeq(0..<a.len).mapIt("one")),
                                                      toTensor(toSeq(0..<c.len).mapIt("two")),
                                                      axis = 0)

  test "Group by":
    proc almostEqual(x, y: float, eps = 1e-6): bool =
      result = (x - y) < eps

    var mpg = readCsv("data/mpg.csv")

    let mpggroup = mpg.group_by("cyl")

    # TODO: make this to `doAssert`!
    let summary = mpg.summarize(f{float: "mean_cyl" << mean(c"cyl")},
                                f{float: "mean_hwy" << mean(c"hwy")})
    echo "done "
    echo summary
    check almostEqual(summary["mean_cyl"][0, float], 5.88889)
    check almostEqual(summary["mean_hwy"][0, float], 23.4402)
    echo "almost queal"
    var sum_grouped = mpggroup.summarize(f{float: "mean_displ" << mean(c"displ")},
                                         f{float: "mean_hwy" << mean(c"hwy")})
    echo "summarized"
    echo sum_grouped
    sum_grouped = sum_grouped
      .arrange("cyl")
    echo "arranged"
    echo sum_grouped
    check sum_grouped.len == 4
    check sum_grouped["cyl"][0, int] == 4
    check sum_grouped["cyl"][1, int] == 5
    check sum_grouped["cyl"][2, int] == 6
    check sum_grouped["cyl"][3, int] == 8
    check almostEqual(sum_grouped["mean_displ"][0, float], 2.14568)
    check almostEqual(sum_grouped["mean_displ"][1, float], 2.5)
    check almostEqual(sum_grouped["mean_displ"][2, float], 3.40886)
    check almostEqual(sum_grouped["mean_displ"][3, float], 5.13286)
    check almostEqual(sum_grouped["mean_hwy"][0, float], 28.8025)
    check almostEqual(sum_grouped["mean_hwy"][1, float], 28.75)
    check almostEqual(sum_grouped["mean_hwy"][2, float], 22.8228)
    check almostEqual(sum_grouped["mean_hwy"][3, float], 17.6286)

    let mpg2groups = mpggroup.group_by("class", add = true)
    let classes = mpg["class"].unique
    let cyls = mpg["cyl"].unique
    let product = product([classes.toTensor(Value).toSeq1D,
                           cyls.toTensor(Value).toSeq1D])
    var subgroupCount = 0
    for (by, df) in groups(mpg2groups):
      # check whether current subgroup is part of our cartesian product, i.e. combinations we
      # expect. `by` contains both the field name and value, extract values
      let curSubGroup = @[by[1][1], by[0][1]]
      check curSubGroup in product
      inc subGroupCount

    # sub group count must be smaller or equal to the cartesian product
    # it can be smaller if a specific combination has no entries
    check subGroupCount <= product.len
    # which is the case for current grouping and the mpg dataset:
    check subGroupCount == 19

    let cylFiltered = mpg.filter(f{c"cyl" == 4})
    check cylFiltered.len == 81
    let cylDrvFiltered = cylFiltered.filter(f{c"drv" == "4"})
    check cylDrvFiltered.len == 23

  test "Unequal":
    let mpg = readCsv("data/mpg.csv")

    let mpgNoSuv = mpg.filter(f{`class` != "suv"})
    check "suv" notin mpgNoSuv["class"].unique

  test "Filter - two comparisons using `and`":
    let x = toSeq(0 .. 100)
    let df = toDf(x)
    let dfFilter = df.filter(f{c"x" >= 50 and
                               c"x" <= 75})
    check dfFilter["x"].toTensor(int) == toTensor toSeq(50 .. 75)

  test "Filter - comparisons using function":
    let x = toSeq(0 .. 100)
    let df = toDf(x)
    let dfFilter = df.filter(f{float: c"x" >= max(c"x") * 0.5})
    check dfFilter["x"].toTensor(int) == toTensor toSeq(50 .. 100)

  test "Filter - data types":
    let x = toSeq(0 .. 100)
    let df = toDf(x)
    let dfFiltered = df.filter(f{float: c"x" >= max(c"x") * 0.5})
    check dfFiltered["x"].kind == colInt
    let dfReduced1 = df.summarize(f{int: max(c"x")})
    check dfReduced1["(max x)"].kind == colInt
    let dfReduced2 = df.summarize(f{float: max(c"x")})
    check dfReduced2["(max x)"].kind == colFloat

  test "Transmute - float arithmetic":
    let x = toSeq(0 ..< 100)
    let y = x.mapIt(sin(it.float))
    let y2 = x.mapIt(pow(sin(it.float), 2.0))
    let df = toDf(x, y)
    check df.len == 100
    let dfTrans = df.transmute(f{"x"}, f{"y2" ~ c"y" * c"y"})
    check "y" notin dfTrans
    check "y2" in dfTrans
    check "x" in dfTrans
    check dfTrans["y2"].toTensor(float) == toTensor y2

  test "Transmute - parse floats in dataframe from string column":
    let x = toSeq(0 ..< 100)
    let y = x.mapIt($sin(it.float))
    let yFloat = x.mapIt(sin(it.float))
    let df = toDf(x, y)
    check df.len == 100
    let dfTrans = df.transmute(f{"x"},
                               f{string -> float: "yFloat" ~ parseFloat(df["y"][idx])})
    check "y" notin dfTrans
    check "yFloat" in dfTrans
    check "x" in dfTrans
    let trans = dfTrans["yFloat"].toTensor(float)
    let exp = toTensor yFloat
    for i in 0 ..< trans.len:
      check almostEqual(trans[i], exp[i])

  test "Gather - 2 columns":
    let x = toSeq(0 ..< 100)
    let y1 = x.mapIt(sin(it.float))
    let y2 = x.mapIt(sin(it.float - PI / 2.0) - 0.5)
    let yComb = concat(y1, y2)
    let df = toDf(x, y1, y2)
    check df.len == 100
    let dfLong = df.gather(["y1", "y2"], key = "from", value = "y")
    check dfLong.len == 200
    check dfLong["from"].unique.toTensor(string) == toTensor @["y1", "y2"]
    check dfLong["y"].toTensor(float) == toTensor(yComb)
    let dfY1FromLong = dfLong.filter(f{c"from" == "y1"})
    let dfY2FromLong = dfLong.filter(f{c"from" == "y2"})
    check dfY1FromLong["y"].toTensor(float) == df["y1"].toTensor(float)
    check dfY2FromLong["y"].toTensor(float) == df["y2"].toTensor(float)
    check dfY1FromLong["x"].toTensor(float) == df["x"].toTensor(float)
    check dfY2FromLong["x"].toTensor(float) == df["x"].toTensor(float)

  test "Gather - 3 columns":
    ## check that it works for 3 columns too
    let x = toSeq(0 ..< 100)
    let y1 = x.mapIt(sin(it.float))
    let y2 = x.mapIt(sin(it.float - PI / 2.0) - 0.5)
    let y3 = x.mapIt(cos(it.float - PI / 2.0) - 0.5)
    let yComb = concat(y1, y2, y3)
    let df = toDf(x, y1, y2, y3)
    check df.len == 100
    let dfLong = df.gather(["y1", "y2", "y3"], key = "from", value = "y")
    check dfLong.len == 300
    check dfLong["from"].unique.toTensor(string) == toTensor @["y1", "y2", "y3"]
    check dfLong["y"].toTensor(float) == toTensor yComb
    let dfY1FromLong = dfLong.filter(f{c"from" == "y1"})
    let dfY2FromLong = dfLong.filter(f{c"from" == "y2"})
    let dfY3FromLong = dfLong.filter(f{c"from" == "y3"})
    check dfY1FromLong["y"].toTensor(float) == toTensor(df["y1"], float)
    check dfY2FromLong["y"].toTensor(float) == toTensor(df["y2"], float)
    check dfY3FromLong["y"].toTensor(float) == toTensor(df["y3"], float)
    check dfY1FromLong["x"].toTensor(float) == toTensor(df["x"], float)
    check dfY2FromLong["x"].toTensor(float) == toTensor(df["x"], float)
    check dfY3FromLong["x"].toTensor(float) == toTensor(df["x"], float)


  test "Gather - string and float column":
    ## while it may be questionable to combine string and float columns in general
    ## it should still work
    let x = toSeq(0 ..< 100)
    let y1 = x.mapIt(sin(it.float))
    let yStr = x.mapIt($it)
    let yComb = concat(%~ y1, %~ yStr)
    let df = toDf(x, y1, yStr)
    check df.len == 100
    let dfLong = df.gather(["y1", "yStr"], key = "from", value = "y")
    check dfLong.len == 200
    check dfLong["from"].unique.toTensor(string) == toTensor @["y1", "yStr"]
    check dfLong["y"].toTensor(Value) == toTensor yComb
    let dfY1FromLong = dfLong.filter(f{c"from" == "y1"})
    let dfYSTRFromLong = dfLong.filter(f{c"from" == "yStr"})
    check dfY1FromLong["y"].toTensor(float) == df["y1"].toTensor(float)
    check dfYSTRFromLong["y"].toTensor(string) == df["yStr"].toTensor(string)
    check dfY1FromLong["x"].toTensor(float) == df["x"].toTensor(float)
    check dfYSTRFromLong["x"].toTensor(float) == df["x"].toTensor(float)

  test "Gather - dropping null values":
    ## check that it works for 3 columns too
    let x = toSeq(0 ..< 100)
    var
      y1: seq[float]
      y2: seq[Value]
      x2s: seq[int]
    for i, val in x:
      y1.add sin(val.float)
      if val mod 3 == 0:
        y2.add (%~ (sin(val.float - PI / 2.0) - 0.5))
        x2s.add i
      else:
        y2.add Value(kind: VNull)
    let df = toDf(x, y1, y2)
    let gathered = df.gather(["y1", "y2"], dropNulls = false)
    let onlyy2 = gathered.filter(f{Value: isNull(df["value"][idx]).toBool == false and
                                  c"key" == %~ "y2"})
    check onlyy2["x"].toTensor(int) == toTensor x2s
    check onlyy2.len == x2s.len

  test "Spread":
    let df = readCsv("data/fishdata_sparse.csv")
    let dfSpread = df.spread(namesFrom = "station", valuesFrom = "seen")
    let namesExp = concat(df["station"].unique.toTensor(string).toSeq1D,
                          @["fish"]).sorted
    check dfSpread.len == 19
    check dfSpread.getKeys().len == 12
    check dfSpread.getKeys().sorted == namesExp
    for k in dfSpread.getKeys():
      check dfSpread[k].kind == colInt
    # easy column to check, all 1
    check dfSpread["\"Release\"", int] == newTensorWith(19, 1)
    ## TODO: support NULL values instead of filling by default T(0)

  test "Pretty printing of DFs":
    var
      # need the data as two sequences (well actually as a DataTable, but that is
      # created most easily from two or more sequences).
      x: seq[float]
      y: seq[float]
    for i in 0 ..< 1000:
      let pos = 2 * 3.1415 / 100.0 * i.float
      x.add pos
      y.add sin(pos)
    let df = toDf(x, y)
    let defaultExp = """
     Idx            x            y
  dtype:        float        float
       0            0            0
       1      0.06283      0.06279
       2       0.1257       0.1253
       3       0.1885       0.1874
       4       0.2513       0.2487
       5       0.3141        0.309
       6        0.377       0.3681
       7       0.4398       0.4258
       8       0.5026       0.4817
       9       0.5655       0.5358
      10       0.6283       0.5878
      11       0.6911       0.6374
      12        0.754       0.6845
      13       0.8168        0.729
      14       0.8796       0.7705
      15       0.9425        0.809
      16        1.005       0.8443
      17        1.068       0.8763
      18        1.131       0.9048
      19        1.194       0.9298
"""
    let dfStr = pretty(df, header = false)
    check dfStr == defaultExp
    let expPrecision12 = """
     Idx                    x                    y
  dtype:                float                float
       0                    0                    0
       1              0.06283       0.062788670114
       2              0.12566       0.125329556644
       3              0.18849       0.187375853836
       4              0.25132       0.248682707741
       5              0.31415       0.309008182482
       6              0.37698       0.368114215006
       7              0.43981       0.425767554563
       8              0.50264       0.481740683175
       9              0.56547       0.535812713502
      10               0.6283       0.587770260526
      11              0.69113       0.637408283636
      12              0.75396       0.684530895785
      13              0.81679       0.728952136516
      14              0.87962       0.770496705823
      15              0.94245       0.809000655938
      16              1.00528       0.844312038323
      17              1.06811       0.876291503299
      18              1.13094        0.90481284997
      19              1.19377       0.929763524249
"""
    let dfPrecision12 = pretty(df, precision = 12, header = false)
    check expPrecision12 == dfPrecision12

  test "CSV parsing with spaces":
    let csvDataStream = newStringStream("""
t_in_s,  C1_in_V,  C2_in_V,  type
-3.0000E-06,  -2.441E-04,  -6.836E-04,  T1
-2.9992E-06,  2.441E-04,  -6.836E-04 ,  T1
-2.9984E-06,  1.025E-03,  -8.789E-04 ,  T1
-2.9976E-06,  1.025E-03,  -2.930E-04 ,  T1
-2.9968E-06,  9.277E-04,  2.930E-04  ,  T2
-2.9960E-06,  4.395E-04,  4.883E-04  ,  T2
-2.9952E-06,  1.465E-04,  -2.930E-04 ,  T2
-2.9944E-06,  -3.418E-04,  -1.270E-03,  T2
""")
    let csvRead = readCsv(csvDataStream)
    let texp = @[-3.0000E-06, -2.9992E-06, -2.9984E-06, -2.9976E-06, -2.9968E-06,
                 -2.9960E-06, -2.9952E-06, -2.9944E-06]
    let c1Exp = @[-2.441E-04, 2.441E-04, 1.025E-03, 1.025E-03, 9.277E-04, 4.395E-04,
                   1.465E-04, -3.418E-04]
    let c2Exp = @[-6.836E-04, -6.836E-04, -8.789E-04, -2.930E-04, 2.930E-04,
                  4.883E-04, -2.930E-04, -1.270E-03]
    let typeExp = @["T1", "T1", "T1", "T1", "T2",
                    "T2", "T2", "T2"]
    let dfExp = toDf({ "t_in_s" : texp, "C1_in_V" : c1Exp, "C2_in_V" : c2Exp,
                       "type" : typeExp})
    let df = toDf(csvRead)
    check df["t_in_s"].toTensor(float) == dfExp["t_in_s"].toTensor(float)
    check df["C1_in_V"].toTensor(float) == dfExp["C1_in_V"].toTensor(float)
    check df["C2_in_V"].toTensor(float) == dfExp["C2_in_V"].toTensor(float)
    check df["type"].toTensor(string) == dfExp["type"].toTensor(string)

  test "CSV parsing of data with unnamed column":
    let df = readCsv("data/03-sample_hugo.csv")
    check df.ncols == 9
    check "Unnamed0" in df
    check df["Unnamed0", int] == arange(0, 200).toTensor

  test "Summarize":
    let mpg = readCsv("data/mpg.csv")
    block:
      # explicit LHS
      let res = mpg.summarize(f{int: "num" << sum(c"cyl")})
      check "num" in res
      check res.len == 1
      check res["num", 0] == %~ 1378
      # implicit LHS
      let resImplicit = mpg.summarize(f{int: sum(c"cyl")})
      let fname = "(sum cyl)"
      check fname in resImplicit
      check resImplicit.len == 1
      check resImplicit[fname, 0] == %~ 1378
    block:
      # explicit LHS
      let res = mpg.summarize(f{float: "mean" << mean(c"cyl")})
      check "mean" in res
      check res.len == 1
      check almostEqual(res["mean", 0].toFloat, 5.888888889)
      # implicit LHS
      let resImplicit = mpg.summarize(f{float: mean(c"cyl")})
      let fname = "(mean cyl)"
      check fname in resImplicit
      check resImplicit.len == 1
      check almostEqual(resImplicit[fname, 0].toFloat, 5.888888889)
    block:
      # summarize multiple groups at the same time
      let res = mpg.group_by(["class", "cyl"]).summarize(f{float: mean(c"hwy")})
      check res.len == 19
      # expected numbers. They seem reasonable, but ``I did NOT`` check them
      # manually!!
      # hence another test below with known numbers and their sum
      let exp = @[24.8, 24.8, 29.47, 29.47, 29, 29, 25.31, 25.31, 29.19, 29.19, 26.26, 26.26, 24, 24, 24, 24, 22.2, 22.2, 20.67, 20.67, 17.9, 17.9, 15.8, 15.8, 30.81, 30.81, 28.5, 28.5, 24.71, 24.71, 21.6, 21.6, 23.75, 23.75, 18.5, 18.5, 16.79, 16.79]
      let resSet = res[$f{float: mean(c"hwy")}].toTensor(float).map(x => x.round(2)).toHashSet
      let expSet = exp.toHashSet
      check resSet == expSet
    block:
      # generate numbers
      let num = toSeq(1 .. 100)
      let numVec = repeat(num, 26).flatten
      let sumNum = num.sum
      let lab1 = toSeq({'a'..'z'}).mapIt($it)
      let lab2 = toSeq({'A'..'Z'}).mapIt($it)
      var l1 = newSeq[string]()
      var l2 = newSeq[string]()
      var count = 0
      for j in 0 ..< lab1.len:
        for i in 0 ..< num.len:
          l1.add lab1[j]
          l2.add lab2[j]
          inc count
      check count == 2600
      let df = toDf(l1, l2, numVec)
      let dfG = df.group_by(["l1", "l2"]).summarize(f{int: sum(c"numVec")})
      check dfG.len == 26
      check sumNum == 5050
      for el in dfG[$f{int: sum(c"numVec")}].toTensor(Value):
        check el == %~ sumNum

    block:
      let df = seqsToDf({"x": @[1, 2, 3, 4, 5], "y": @[5, 10, 15, 20, 25]})
      try:
        # fails with `FormulaMismatchError` as there is no reducing proc call in
        # the formula body!
        echo df.summarize(f{float: `x`})
      except FormulaMismatchError:
        discard

  test "Count":
    # count elements by group. Useful combination of group_by and summarize(len)
    let mpg = readCsv("data/mpg.csv")
    # in manual case the order is not preserved, due to `summarize` impl!
    let exp = toHashSet({6 : 79, 8 : 70, 4 : 81, 5 : 4})
    block:
      # manually
      let res = mpg.group_by("cyl").summarize(f{int: "num" << col("cyl").len})
      check "num" in res
      check res.len == 4
      var resSet = initHashSet[(int, int)]()
      for row in res:
        resSet.incl (row["cyl"].toInt.int, row["num"].toInt.int)
      check resSet == exp
      # using `count` directly
      let resDirect = mpg.count("cyl")
      check "n" in resDirect
      check resDirect.len == 4
      var resDirectSet = initHashSet[(int, int)]()
      for row in resDirect:
        resDirectSet.incl (row["cyl"].toInt.int, row["n"].toInt.int)
      check resDirectSet == exp

  test "isNull":
    # tests removal of VNull elements in a column with VNull
    let x1 = toSeq(0 .. 100)
    let x2 = toSeq(0 .. 10)
    let df = toDf(x1, x2)
    check df.filter(f{Value: isNull(df["x2"][idx]).toBool == false})["x2"].toTensor(Value) == toTensor (%~ x2)

  test "Unique - duplicates using all columns":
    # given some data containing duplicates
    let dataDuplStream = newStringStream("""
t_in_s,  C1_in_V,  C2_in_V,  type
-3.0000E-06,  -2.441E-04,  -6.836E-04,  T1
-2.9992E-06,  2.441E-04,  -6.836E-04 ,  T1
-2.9984E-06,  1.025E-03,  -8.789E-04 ,  T1
-2.9976E-06,  1.025E-03,  -2.930E-04 ,  T1
-2.9992E-06,  2.441E-04,  -6.836E-04 ,  T1
-2.9984E-06,  1.025E-03,  -8.789E-04 ,  T1
-2.9976E-06,  1.025E-03,  -2.930E-04 ,  T1
-2.9968E-06,  9.277E-04,  2.930E-04  ,  T2
""")
    let df = toDf(readCsv(dataDuplStream))
    check df.len == 8
    let dfUnique = df.unique
    check dfUnique.len == 5

  test "Unique - duplicates using subset of columns":
    let s1 = @[1, 2, 3, 4, 5]
    let s2 = @["A", "E", "A", "D", "E"]
    let s3 = @["B", "G", "B", "G", "X"]
    let df = seqsToDF({ "id" : s1,
                        "Start" : s2,
                        "Stop" : s3 })
    check df.len == 5
    let dfUniqueAll = df.unique
    check dfUniqueAll.len == 5
    # now only use columns start and stop
    let dfUnique = df.unique(["Start", "Stop"])
    check dfUnique.len == 4

  test "setDiff":
    # remove duplicates of `mpg` (for some reason there are 9 duplicates..)
    let mpg = readCsv("data/mpg.csv").unique
    let mpgS1 = mpg[0 .. 25]
    let mpgS2 = mpg[20 .. 29]
    block:
      # S1 is primary
      let exp = mpg[0 .. 19].arrange(toSeq(keys(mpg)))
      let res = setDiff(mpgS1, mpgS2).arrange(toSeq(keys(mpg)))
      check exp.len == res.len
      for i in 0 ..< exp.len:
        check row(exp, i) == row(res, i)
    block:
      # S2 is primary
      let exp = mpg[26 .. 29].arrange(toSeq(keys(mpg)))
      let res = setDiff(mpgS2, mpgS1).arrange(toSeq(keys(mpg)))
      check exp.len == res.len
      for i in 0 ..< exp.len:
        check row(exp, i) == row(res, i)
    block:
      # symmetric difference
      let exp = bind_rows(mpg[0 .. 19], mpg[26 .. 29], id = "")
        .arrange(toSeq(keys(mpg)))
      let res = setDiff(mpgS1, mpgS2, symmetric = true).arrange(toSeq(keys(mpg)))
      check exp.len == res.len
      for i in 0 ..< exp.len:
        check row(exp, i) == row(res, i)

  test "Custom column names when reading CSV like data":
    # given some data without a header and column names
    let data = """
-3.0000E-06,  -2.441E-04,  -6.836E-04,  T1
-2.9992E-06,  2.441E-04,  -6.836E-04 ,  T1
-2.9984E-06,  1.025E-03,  -8.789E-04 ,  T1
"""
    let dataDuplStream = newStringStream(data)
    # define columns
    let cols = @["V1", "V2", "V3", "Channel"]
    block OldParser:
      let df = toDf(readCsv(dataDuplStream, colNames = cols))
      check df.len == 3
      check df.getKeys.sorted == cols.sorted
    block NewParser:
      let df = parseCsvString(data, colNames = cols)
      check df.len == 3
      check df.getKeys.sorted == cols.sorted

  test "Column names containing numbers":
    # given some data without a header and column names
    let data = """
-3.0000E-06,  -2.441E-04,  -6.836E-04,  T1
-2.9992E-06,  2.441E-04,  -6.836E-04 ,  T1
-2.9984E-06,  1.025E-03,  -8.789E-04 ,  T1
"""
    let dataDuplStream = newStringStream(data)
    # define columns
    let cols = @["0", "1", "2", "3"]
    let colsNot = @["\"0\"", "\"1\"", "\"2\"", "\"3\""]
    block OldParser:
      let df = toDf(readCsv(dataDuplStream, colNames = cols))
      check df.len == 3
      check df.getKeys.sorted == cols.sorted
      # redundant but a showcase what happened previously
      for k in zip(df.getKeys, colsNot):
        check k[0] != k[1]
    block NewParser:
      let df = parseCsvString(data, colNames = cols)
      check df.len == 3
      check df.getKeys.sorted == cols.sorted
      # redundant but a showcase what happened previously
      for k in zip(df.getKeys, colsNot):
        check k[0] != k[1]

  test "Custom column names replacing a real header":
    let data = """
 ag, Z=47, (Energy (eV),f1,f2)
   10.0000     -9999.00      1.18566
   10.1617     -9999.00      1.22941
   10.3261     -9999.00      1.27478
   10.4931     -9999.00      1.32182
   10.6628     -9999.00      1.38215
"""
    let cols = @["Energy", "f1", "f2"]
    # note the `skipLines`! Have to skip the real header line!
    let df = parseCsvString(data, colNames = cols, sep = ' ', skipLines = 1)
    check df.len == 5
    check df.getKeys.sorted == cols.sorted
    check df["f1", float].toSeq1D == @[-9999.0, -9999.0, -9999.0, -9999.0, -9999.0]

  test "Parsing space seperated data with spacing at the end of lines":
    let data = """
   Energy            f1           f2
   10.0000     -9999.00      1.18566
   10.1617     -9999.00      1.22941
   10.3261     -9999.00      1.27478
   10.4931     -9999.00      1.32182
   10.6628     -9999.00      1.38215
"""
    let df = parseCsvString(data, sep = ' ')
    check df.len == 5
    check df.getKeys.sorted == @["Energy", "f1", "f2"]
    check df["f1", float].toSeq1D == @[-9999.0, -9999.0, -9999.0, -9999.0, -9999.0]

  test "Evaluate data frame using FormulaNode":
    let mpg = readCsv("data/mpg.csv")
    let f = f{`hwy` ~ (`displ` + `cyl` - `cty`)} # this doesn't make sense, but anyways...
    # Displacement + Cylinders - City mpg. Yeah :D
    # use RHS of formula for calculation of 0 row.
    # not exactly possible on arraymancer backend
    check f.evaluate(mpg)[0, Value] == %~ -12.2

    # applying negative column results in expected
    # stringifaction of the formula
    let dfNeg = mpg.clone.transmute(f{-1.0 * c"hwy"})
    check "(* -1.0 hwy)" == getKeys(dfNeg)[0]

    # negative prefix of existing column results in what we expect
    check evaluate(f{-1.0 * c"hwy"}, mpg).toTensor(float) == mpg["hwy"].toTensor(float).map(x => -x)
    # evaluate non existant key to vector of constant
    check evaluate(f{"nonExistant"}, mpg).toTensor(string) == toTensor toSeq(0 ..< mpg.len).mapIt("nonExistant")
    # evaluate formula without column on DF
    check evaluate(f{1 + 2}, mpg).toTensor(int) == toTensor toSeq(0 ..< mpg.len).mapIt(3)

  test "Reduce data frame using FormulaNode":
    let mpg = readCsv("data/mpg.csv")
    # check reduction via a formula and VectorFloatProc
    check almostEqual(reduce(f{float: mean(c"hwy")}, mpg).toFloat, 23.44017, 1e-3)

    # combine with calculation
    check almostEqual(reduce(f{float: 235 / mean(c"hwy")}, mpg).toFloat, 10.0255, 1e-3)

  test "Allow `add` if first argument is still uninitialized":
    # uninitialized data frame (DataTable is ref object)
    var df: DataTable[Column]
    check df.isNil
    let dfToAdd = toDf({ "x" : @[1, 2, 3],
                             "y" : @[4, 5, 6] })
    df.add dfToAdd
    check df == dfToAdd
    check dfToAdd["x"].toTensor(int) == [1, 2, 3].toTensor
    check dfToAdd["y"].toTensor(int) == [4, 5, 6].toTensor

  test "Inner join - fully qualified":
    let idents = @["A", "B", "C", "D"]
    let ids = @[1, 2, 3, 4]
    let words = @["suggest", "result", "from", "to"]
    let df1 = toDf({ "Ident" : idents,
                     "Ids" : ids})
    let df2 = toDf({ "Ident" : idents,
                     "Words" : words })
    let dfExp = toDf({ "Ident" : idents,
                       "Words" : words,
                       "Ids" : ids })
    let dfRes = df1.innerJoin(df2, by = "Ident")
    check dfRes.len == dfExp.len
    check dfRes.getKeys == dfExp.getKeys
    check dfRes["Ident"].toTensor(string) == dfExp["Ident"].toTensor(string)
    check dfRes["Ids"].toTensor(int) == dfExp["Ids"].toTensor(int)
    check dfRes["Words"].toTensor(string) == dfExp["Words"].toTensor(string)

  test "Inner join - int & float column":
    let idents = @["A", "B", "C", "D"]
    let ids = @[1, 2, 3, 4]
    let idsFloat = @[1'f64, 2, 3, 4]
    let words = @["suggest", "result", "from", "to"]
    let df1 = toDf({ "Ident" : idents,
                     "Ids" : ids})
    let df2 = toDf({ "Ident" : idents,
                     "Ids" : idsFloat,
                     "Words" : words})
    let dfExp = toDf({ "Ident" : idents,
                       "Words" : words,
                       "Ids" : idsFloat })
    let dfRes = df1.innerJoin(df2, by = "Ident")
    check dfRes.len == dfExp.len
    check dfRes.getKeys == dfExp.getKeys
    check dfRes["Ident"].toTensor(string) == dfExp["Ident"].toTensor(string)
    # result has enveloping column kind float
    check dfRes["Ids"].kind == colFloat
    check dfRes["Ids"].toTensor(float) == dfExp["Ids"].toTensor(float)
    check dfRes["Words"].toTensor(string) == dfExp["Words"].toTensor(string)

  test "Inner join - missing elements":
    let idents = @["A", "B", "C", "D", "E"]
    let ids = @[1, 2, 3, 4, 5]
    let idsFloat = @[1'f64, 2, 3, 4]
    let words = @["suggest", "result", "from", "to"]
    let df1 = toDf({ "Ident" : idents,
                     "Ids" : ids})
    let df2 = toDf({ "Ident" : idents[0 ..< ^1],
                     "Ids" : idsFloat,
                     "Words" : words})
    let dfExp = toDf({ "Ident" : idents[0 ..< ^1],
                       "Words" : words,
                       "Ids" : idsFloat })
    let dfRes = df1.innerJoin(df2, by = "Ident")
    check dfRes.len == dfExp.len
    check dfRes.getKeys == dfExp.getKeys
    check dfRes["Ident"].toTensor(string) == dfExp["Ident"].toTensor(string)
    # result has enveloping column kind float
    check dfRes["Ids"].kind == colFloat
    check dfRes["Ids"].toTensor(float) == dfExp["Ids"].toTensor(float)
    check dfRes["Words"].toTensor(string) == dfExp["Words"].toTensor(string)

  test "Convert (one typed) object column to native":
    let a = @["A", "B", "C", "D", "E"]
    let b = @[1, 2, 3, 4, 5]
    let c = @[1.1, 1.2, 1.3, 1.5]
    let d = @[true, true, false, true]
    let aCol = toColumn(%~ a)
    let bCol = toColumn(%~ b)
    let cCol = toColumn(%~ c)
    let dCol = toColumn(%~ d)
    check aCol.kind == colObject
    check bCol.kind == colObject
    check cCol.kind == colObject
    check dCol.kind == colObject
    check aCol.toNativeColumn.kind == colString
    check bCol.toNativeColumn.kind == colInt
    check cCol.toNativeColumn.kind == colFloat
    check dCol.toNativeColumn.kind == colBool

  test "Convert multi typed (real object) column to native fails":
    let a = @["A", "B", "C", "D", "E"]
    let b = @[1, 2, 3, 4, 5]
    let ab = concat(%~ a, %~ b)
    let c = @[1.1, 1.2, 1.3, 1.5]
    let d = @[true, true, false, true]
    let cd = concat(%~ c, %~ d)
    let abCol = toColumn(%~ ab)
    let cdCol = toColumn(%~ cd)
    check abCol.kind == colObject
    check cdCol.kind == colObject
    try:
      # This actually works because ints can be converted to string!
      # that's not really desired behavior, is it?
      check abCol.toNativeColumn.kind == colString
      check false
    except AssertionError:
      check true
    try:
      check cdCol.toNativeColumn.kind == colFloat
      check false
    except AssertionError:
      check true

  test "Remove 'null' values from DF":
    let idents = @["A", "B", "C", "D", "E"]
    let ids = @[1, 2, 3, 4, 5]
    let ages = @[43, 27, 32, 43]
    let cities = @[%~ "NYC", %~ "London", %~ "Sydney", Value(kind: VNull),
                   %~ "Berlin"]
    let df = toDf({ "Ident" : idents,
                    "Id" : ids,
                    "Age" : ages,
                    "City" : cities})
                    # now check for:
                    # -> filter by each individual column
                    # -> filter by both columns in one call
    let dfExp1 = toDf({ "Ident" : idents[0 ..< ^1],
                        "Id" : ids[0 ..< ^1],
                        "Age" : ages,
                        "City" : cities[0 ..< ^1] })
    let dfExp2 = toDf({ "Ident" : @["A", "B", "C", "E"],
                        "Id" : @[1, 2, 3, 5],
                        "Age" : @[%~ 43, %~ 27, %~ 32, Value(kind: VNull)],
                        "City" : cities.filterIt(it.kind != VNull) })
    let dfExp3 = toDf({ "Ident" : @["A", "B", "C"],
                        "Id" : @[1, 2, 3],
                        "Age" : %~ @[43, 27, 32],
                        "City" : %~ cities[0 ..< ^2]})
    block noNativeConversion:
      let dfRes1 = df.drop_null("Age")
      check dfRes1["Age"].kind == colObject
      check dfRes1["City"].kind == colObject
      let dfRes2 = df.drop_null("City")
      check dfRes2["Age"].kind == colObject
      check dfRes2["City"].kind == colObject
      let dfRes3 = df.drop_null()
      check dfRes3["Age"].kind == colObject
      check dfRes3["City"].kind == colObject
      let keys = getKeys(df)
      for k in keys:
        check dfRes1[k].toTensor(Value) == dfExp1[k].toTensor(Value)
        check dfRes2[k].toTensor(Value) == dfExp2[k].toTensor(Value)
        check dfRes3[k].toTensor(Value) == dfExp3[k].toTensor(Value)

      # convert manually to correct dtypes
      check dfRes1["Age"].toNativeColumn.kind == colInt
      expect(AssertionDefect):
        check dfRes1["City"].toNativeColumn.kind == colString
      check dfRes1["City"].toNativeColumn(failIfImpossible = false).kind == colObject

      check dfRes2["City"].toNativeColumn.kind == colString
      expect(AssertionDefect):
        check dfRes2["Age"].toNativeColumn.kind == colInt
      check dfRes2["Age"].toNativeColumn(failIfImpossible = false).kind == colObject

      check dfRes3["Age"].toNativeColumn.kind == colInt
      check dfRes3["City"].toNativeColumn.kind == colString

    block nativeConversion:
      let dfRes1 = df.drop_null("Age", convertColumnKind = true)
      let dfRes2 = df.drop_null("City", convertColumnKind = true)
      let dfRes3 = df.drop_null(convertColumnKind = true)

      # convert manually to correct dtypes
      check dfRes1["Age"].kind == colInt
      check dfRes1["City"].kind == colObject

      check dfRes2["City"].kind == colString
      check dfRes2["Age"].kind == colObject

      check dfRes3["Age"].kind == colInt
      check dfRes3["City"].kind == colString

  test "Inplace filter & assign":
    let c1 = constantColumn(10, 40)
    let c2 = toColumn toSeq(0 ..< 40)
    var df = toDf(c1, c2)
    df[f{`c2` > 10 and `c2` < 20}, "c2"] = 42
    df[f{`c2` > 20 and `c2` < 30}, "c1"] = 46
    check df.filter(f{`c2` == 42}).len == 9
    check df.filter(f{`c1` == 46}).len == 9
    let data1 = df["c1", int]
    let data2 = df["c2", int]
    check data1[21 .. 29] == toSeq(0 .. 8).mapIt(46).toTensor()
    check data2[11 .. 19] == toSeq(0 .. 8).mapIt(42).toTensor()

  test "Add row to DF (WARNING: very slow!)":
    let c1 = constantColumn(10, 10)
    let c2 = toColumn toSeq(0 ..< 10).mapIt(it.float)
    var df = toDf(c1, c2)
    for i in 0 ..< 10:
      df.add(i, i.float * 2)
    check df.len == 20
    let t1 = df["c1", int]
    let t2 = df["c2", float]
    check t1 == toTensor toSeq(0 ..< 20).mapIt(if it < 10: 10 else: it - 10)
    check t2 == toTensor toSeq(0 ..< 20).mapIt(if it < 10: it.float else: (it.float - 10.0) * 2)

  test "Mutate/Transmute works on grouped dataframes":
    block Mutate:
      let df = readCsv("data/mpg.csv")
        .group_by("class")
        # for simplicity, we're gonna add the mean of each group to
        .mutate(f{float -> float: "subMeanHwy" ~ 0.0 + mean(df["hwy"])})
        .arrange("class")
      let expDf = df.group_by("class").summarize(f{float -> float: "subMeanHwy" << mean(`hwy`)})
        .arrange("class")

      check df.select("subMeanHwy").unique()["subMeanHwy", float] == expDf.select("subMeanHwy")["subMeanHwy", float]

    block Transmute:
      let df = readCsv("data/mpg.csv")
      var dfTr = df
        .group_by("class")
        # for simplicity, we're gonna add the mean of each group to
        .transmute(f{float -> float: "subMeanHwy" ~ 0.0 + mean(df["hwy"])},
                   f{"class"})
        .arrange("class")
      let expDf = df.group_by("class").summarize(f{float -> float: "subMeanHwy" << mean(`hwy`)})
        .arrange("class")

      check dfTr.select("subMeanHwy").unique()["subMeanHwy", float] == expDf.select("subMeanHwy")["subMeanHwy", float]

  test "Construction with scalar":
    var df = toDf({ "x" : @[1,2,3],
                        "y" : toSeq(5..7),
                        "z" : "foo",
                        "α" : 2.5 })
    check df.len == 3
    check df["x", int] == [1,2,3].toTensor
    check df["y", int] == [5,6,7].toTensor
    echo df
    check df["z"].kind == colConstant
    check df["α"].kind == colConstant
    check df["z"].cCol == %~ "foo"
    check df["α"].cCol == %~ 2.5
    df["β"] = 123
    check df["β"].kind == colConstant
    check df["β"].cCol == %~ 123

  test "Index access for DataFrames using `[[i]]` operator":
    let df = toDf({"a" : [1, 2], "b" : [3, 4], "c" : [5, 6], "d" : [7, 8]})
    block:
      check df[[0]].toTensor(int) == [1, 2].toTensor
      check df[[1]].toTensor(int) == [3, 4].toTensor
      check df[[2]].toTensor(int) == [5, 6].toTensor
      check df[[3]].toTensor(int) == [7, 8].toTensor
    block:
      try:
        discard df[[-1]]
      except IndexError:
        discard
      try:
        discard df[[5]]
      except IndexError:
        discard

    let df2 = toDf({"b" : [3, 4], "a" : [1, 2], "d" : [7, 8], "c" : [5, 6]})
    block:
      check df2[[1]].toTensor(int) == [1, 2].toTensor
      check df2[[0]].toTensor(int) == [3, 4].toTensor
      check df2[[3]].toTensor(int) == [5, 6].toTensor
      check df2[[2]].toTensor(int) == [7, 8].toTensor

  test "Select - selecting a column":
    let df = toDf({"a" : [1, 2], "b" : [3, 4], "c" : [5, 6], "d" : [7, 8]})
    block:
      let res = df.select("a")
      check "a" in res
      check "b" notin res and "c" notin res and "d" notin res
    block:
      let res = df.select("b")
      check "b" in res
      check "a" notin res and "c" notin res and "d" notin res
    block:
      let res = df.select("d")
      check "d" in res
      check "a" notin res and "b" notin res and "c" notin res

  test "Select - selecting multiple columns":
    let df = toDf({"a" : [1, 2], "b" : [3, 4], "c" : [5, 6], "d" : [7, 8]})
    block:
      let res = df.select("a", "b")
      check "a" in res
      check "b" in res
      check "c" notin res and "d" notin res
    block:
      let res = df.select("b", "d")
      check "b" in res
      check "d" in res
      check "a" notin res and "c" notin res
    block: # using array
      let res = df.select(["a", "d"])
      check "a" in res
      check "d" in res
      check "b" notin res and "c" notin res
    block: # using seq
      let res = df.select(@["a", "d"])
      check "a" in res
      check "d" in res
      check "b" notin res and "c" notin res

  test "Select - using a Formula":
    let df = toDf({"a" : [1, 2], "b" : [3, 4], "c" : [5, 6], "d" : [7, 8]})
    block:
      let res = df.select(f{"a"}, f{"B" <- "b"}) # formula & string cannot be mixed
      check "a" in res
      check "B" in res
      check "c" notin res and "d" notin res and "b" notin res

  test "Select - respects order of given keys":
    let df = toDf({"a" : [1, 2], "b" : [3, 4], "c" : [5, 6], "d" : [7, 8]})
    block:
      let res = df.select("a", "b")
      check res[[0]].toTensor(int) == [1, 2].toTensor
      check res[[1]].toTensor(int) == [3, 4].toTensor
    block:
      let res = df.select("b", "a")
      check res[[1]].toTensor(int) == [1, 2].toTensor
      check res[[0]].toTensor(int) == [3, 4].toTensor

  test "Relocate - relocate a single column":
    let df = toDf({"a" : [1, 2], "b" : [3, 4], "c" : [5, 6], "d" : [7, 8]})
    check df[[0]].toTensor(int) == [1, 2].toTensor
    check df[[1]].toTensor(int) == [3, 4].toTensor
    check df[[2]].toTensor(int) == [5, 6].toTensor
    check df[[3]].toTensor(int) == [7, 8].toTensor
    block:
      let res = df.relocate("a", after = "c")
      check res[[2]].toTensor(int) == [1, 2].toTensor
      check res[[0]].toTensor(int) == [3, 4].toTensor
      check res[[1]].toTensor(int) == [5, 6].toTensor
      check res[[3]].toTensor(int) == [7, 8].toTensor
    block:
      let res = df.relocate("a", after = "d")
      check res[[3]].toTensor(int) == [1, 2].toTensor
      check res[[0]].toTensor(int) == [3, 4].toTensor
      check res[[1]].toTensor(int) == [5, 6].toTensor
      check res[[2]].toTensor(int) == [7, 8].toTensor
    block:
      let res = df.relocate("a", before = "b")
      check res[[0]].toTensor(int) == [1, 2].toTensor
      check res[[1]].toTensor(int) == [3, 4].toTensor
      check res[[2]].toTensor(int) == [5, 6].toTensor
      check res[[3]].toTensor(int) == [7, 8].toTensor
    block:
      let res = df.relocate("c", before = "a")
      check res[[1]].toTensor(int) == [1, 2].toTensor
      check res[[2]].toTensor(int) == [3, 4].toTensor
      check res[[0]].toTensor(int) == [5, 6].toTensor
      check res[[3]].toTensor(int) == [7, 8].toTensor
    block:
      let res = df.relocate(f{"C" <- "c"}, before = "a")
      check "C" in res and "c" notin res
      check res[[1]].toTensor(int) == [1, 2].toTensor
      check res[[2]].toTensor(int) == [3, 4].toTensor
      check res[[0]].toTensor(int) == [5, 6].toTensor
      check res[[3]].toTensor(int) == [7, 8].toTensor
    block: # cannot relocate to itself
      try:
        let res = df.relocate("a", after = "a")
      except KeyError:
        discard

  test "Relocate - relocate multiple columns":
    let df = toDf({"a" : [1, 2], "b" : [3, 4], "c" : [5, 6], "d" : [7, 8]})
    check df[[0]].toTensor(int) == [1, 2].toTensor
    check df[[1]].toTensor(int) == [3, 4].toTensor
    check df[[2]].toTensor(int) == [5, 6].toTensor
    check df[[3]].toTensor(int) == [7, 8].toTensor
    block: # need to hand array for varargs
      let res = df.relocate(["b", "c"], after = "d")
      check res[[0]].toTensor(int) == [1, 2].toTensor
      check res[[2]].toTensor(int) == [3, 4].toTensor
      check res[[3]].toTensor(int) == [5, 6].toTensor
      check res[[1]].toTensor(int) == [7, 8].toTensor
    block: #
      let res = df.relocate(["c", "b"], after = "d")
      check res[[0]].toTensor(int) == [1, 2].toTensor
      check res[[3]].toTensor(int) == [3, 4].toTensor
      check res[[2]].toTensor(int) == [5, 6].toTensor
      check res[[1]].toTensor(int) == [7, 8].toTensor

  test "Mutate - computing a new column based on two existing":
    let df = toDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12], "z": ["5","6","7"] })
    let dfRes = df.mutate(f{"x+y" ~ `x` + `y`})
    check dfRes.ncols == 4
    check "x+y" in dfRes
    check dfRes["x+y", int] == [11,13,15].toTensor

  test "Mutate - computing a new column using a local variable":
    let df = toDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12], "z": ["5","6","7"] })
    # of course local variables can be referenced:
    let foo = 5
    let dfRes = df.mutate(f{"x+foo" ~ `x` + foo})
    check "x+foo" in dfRes
    check dfRes["x+foo", int] == [6,7,8].toTensor

  test "Mutate - computing a new column by calling a function":
    let df = toDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12], "z": ["5","6","7"] })
    # they can change type and infer it
    let foo = 5
    let dfRes = df.mutate(f{"asInt" ~ parseInt(`z`)})
    check "asInt" in dfRes
    check dfRes["asInt", int] == [5,6,7].toTensor

  test "Mutate - computing a new column without an explicit name":
    let df = toDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12], "z": ["5","6","7"] })
    # and if no name is given:
    let dfRes = df.mutate(f{`x` + `y`})
    check "(+ x y)" in dfRes
    check dfRes["(+ x y)", int] == [11,13,15].toTensor

  test "Mutate - assigning a constant column":
    let df = toDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12], "z": ["5","6","7"] })
    let dfRes = df.mutate(
      f{"foo" <- 2},   # generates a constant column with value 2
      f{"bar" <- "x"}, # generates a constant column with value "x", does *not* rename "x" to "bar"
      f{"baz" ~ 2}     # generates a (non-constant!) column of only values 2
    )
    check dfRes["foo"].kind == colConstant
    check dfRes["foo", 0] == %~ 2
    check dfRes["bar"].kind == colConstant
    check dfRes["bar", 0] == %~ "x"
    check "x" in dfRes # "x" untouched
    check dfRes["baz"].kind == colInt # integer column, not constant!
    check dfRes["baz", int] == toTensor [2, 2, 2]

suite "Formulas":
  test "Formula containing `if`":
    let fn = f{int -> int: if `poopoo` > 5:
                             `pewpew`
                           else:
                             `y`}
    check $fn == "(if (elif (> poopoo 5) (pewpew)) (else (y)))"

    let df = toDf({ "poopoo" : @[1,2,7,8], "pewpew" : @[10, 11, 12, 13],
                    "y" : @[100, 101, 102, 103]})
    check fn.evaluate(df).toTensor(int) == [100, 101, 12, 13].toTensor()

  test "Access using idx()":
    let a = [1, 2, 3]
    let b = [3, 4, 5]
    let c = [4, 5, 6]
    let d = [8, 9, 10]
    let e = [11, 12, 13]
    let df = toDf(a, b, c, d, e)
    block:
      let dStr = "d"
      proc someCall(): string = "e"
      let fn1 = f{int -> int: "newCol1" ~ idx("a") + idx(`b`) + idx(c"c") + idx(dStr) + idx(someCall())}
      let fn2 = f{int -> int: "newCol2" << max(col("a")) + max(col(`b`)) + max(col(c"c")) + max(col(dStr)) + max(col(someCall()))}
      check $fn1 == "newCol1"
      check $fn2 == "newCol2"
      check fn1.evaluate(df).toTensor(int) == [27, 32, 37].toTensor()
      let dfShort = df.summarize(fn2)
      check dfShort.len == 1
      check dfShort[$fn2, int][0] == 3 + 5 + 6 + 10 + 13
    block:
      proc complProcedure(x: int, s: string, b: seq[int]): int =
        result = x + b[0] + ord(s[0])

      let fn = f{"computeMe" ~ complProcedure(idx("a"), "hello", @[1, 2, 3])}
      check fn.evaluate(df).toTensor(int) == @[106, 107, 108].toTensor()

    block:
      proc complProcedure(x: int, s: string, b: seq[int], s2: string): int =
        result = x + b[0] + ord(s[0]) - ord(s2[0])
      proc anotherCall(): int = 5
      proc moreCalls(x: int): string = $x

      let fn = f{"computeMe" ~ complProcedure(idx("a"), "hello", @[1, 2, 3], anotherCall().moreCalls())}
      check fn.evaluate(df).toTensor(int) == @[53, 54, 55].toTensor()


  test "dplyr / pandas comparison inspired tests":
    # some of this functionality was either broken or didn't work before working on
    # that dplyr & pandas comparison
    let df = toDf({ "A" : concat(newSeqWith(50, "a"), newSeqWith(50, "b")),
                    "C" : concat(newSeqWith(25, 5),
                                 newSeqWith(25, 15),
                                 newSeqWith(50, 35)),
                    "B" : toSeq(0 ..< 100) })
    block:
      let res = df.group_by("A").summarize(f{int: sum(`B`)}).filter(f{idx("(sum B)") < 2000})
      check res.len == 1
      check res["A", string][0] == "a"
      check res["(sum B)", int][0] == 1225

    block:
      # now works:
      let res = df.group_by("A").filter(f{ sum(`B`) < 2000})
      check res.len == 50
      check res["B", int] == toSeq(0 ..< 50).toTensor
      check res["C", int] == concat(newSeqWith(25, 5), newSeqWith(25, 15)).toTensor

    block:
      # runtime error: TODO write test! This *could* becoma a CT error in the future.
      expect(FormulaMismatchError):
        discard df.group_by("A").filter(f{ sum(`B`) * 2000})

    block:
      let res = df.group_by(["A", "C"])
        .summarize(f{float: "mean_B" << mean(`B`)},
                   f{int: "sum_B" << sum(`B`)},
                   f{int: "count_B" << col(`B`).len})
      check res.len == 3
      check res["A", string] == ["a", "a", "b"].toTensor
      check res["C", int] == [5, 15, 35].toTensor
      check res["mean_B", float] == [12.0, 37.0, 74.5].toTensor
      check res["sum_B", int] == [300, 925, 3725].toTensor
      check res["count_B", int] == [25, 25, 50].toTensor

    block:
      let res = df.group_by(["A", "C"])
        .summarize(f{float: "mean_B" << mean(`B`)},
                   f{float: "sum_B" << sum(`B`)},
                   f{float: "B_first" << col(`B`)[0]})
      check res.len == 3
      check res["A", string] == ["a", "a", "b"].toTensor
      check res["C", int] == [5, 15, 35].toTensor
      check res["mean_B", float] == [12.0, 37.0, 74.5].toTensor
      check res["sum_B", int] == [300, 925, 3725].toTensor
      check res["B_first", int] == [0, 25, 50].toTensor

    block:
      let res = df.group_by("A").mutate(f{float: "meanB" << mean(`B`)})
      check res.len == 100
      check res["meanB", float] == concat(newSeqWith(50, 24.5), newSeqWith(50, 74.5)).toTensor

  test "Test of idx + mean(col) == mapping operation":
    ## This test is really only to test that the `mutate` formula shown here is
    ## actually compiled correctly into a mapping operation, with or without
    ## user given `~`
    block:
      let df = readCsv("data/mpg.csv")
        .group_by("class")
        .mutate(f{float -> float: "subMeanHwy" ~ `cty` + mean(df["hwy"])})
        .arrange("class")
      check df.len == 234
      check df["subMeanHwy", float][0 ..< 5] == [40.8, 39.8, 40.8, 39.8, 39.8].toTensor
    block:
      let df = readCsv("data/mpg.csv")
        .group_by("class")
        .mutate(f{float -> float: `cty` + mean(df["hwy"])})
        .arrange("class")
      check df.len == 234
      check df["(+ cty (mean df[\"hwy\"]))", float][0 ..< 5] == [40.8, 39.8, 40.8, 39.8, 39.8].toTensor

  test "Slicing DF with constant column":
    var df = toDf({ "Energy" : cycle(linspace(0.0, 24.0, 25), 2),
                    "Counts" : concat(toSeq(0 ..< 25),
                                          toSeq(0 ..< 25)) })
    df["Type"] = constantColumn("background", df.len)
    let dfSlice = df[24 .. 26]
    check dfSlice.len == 3
    check dfSlice["Energy", int] == [24, 0, 1].toTensor
    check dfSlice["Counts", int] == [24, 0, 1].toTensor
    check dfSlice["Type", string] == ["background", "background", "background"].toTensor

  test "Single function call in formula":
    proc inRegion(x, y: float, r: string): bool =
      result = x > 1
    let df = toDf({"x" : [1,2,3], "y" : [4,5,6]})
    let rad = "foo"
    let res = df.filter(f{inRegion(`x`, `y`, rad)})
    check res["x", int] == [2,3].toTensor

  test "Formula referring to bool column":
    let df = toDf({"x" : [1,2,3], "y" : [true, false, true]})
    block IsTrue:
      let res = df.filter(f{bool: `y`})
      check res["x", int] == [1,3].toTensor
    block IsFalse:
      let res = df.filter(f{bool: not `y`})
      check res["x", int] == [2].toTensor

suite "Formulas with object columns using convenience operators":
  test "int comparisons":
    let df = toDf({"x" : [%~ 1, %~ 2, %~ 3]})
    check df.filter(f{`x` == 1})["x", int] == [1].toTensor
    check df.filter(f{`x` != 1})["x", int] == [2,3].toTensor
    check df.filter(f{`x` > 1})["x", int] == [2,3].toTensor
    check df.filter(f{`x` >= 1})["x", int] == [1,2,3].toTensor
    check df.filter(f{`x` < 2})["x", int] == [1].toTensor

    check df.filter(f{1 == `x`})["x", int] == [1].toTensor
    check df.filter(f{1 != `x`})["x", int] == [2,3].toTensor
    check df.filter(f{1 < `x`})["x", int] == [2,3].toTensor
    check df.filter(f{1 <= `x`})["x", int] == [1,2,3].toTensor
    check df.filter(f{2 > `x`})["x", int] == [1].toTensor

  test "float comparisons":
    let df = toDf({"x" : [%~ 1.0, %~ 2.0, %~ 3.0]})
    check df.filter(f{`x` == 1.0})["x", float] == [1.0].toTensor
    check df.filter(f{`x` != 1.0})["x", float] == [2.0,3.0].toTensor
    check df.filter(f{`x` > 1.0})["x", float] == [2.0,3.0].toTensor
    check df.filter(f{`x` >= 1.0})["x", float] == [1.0,2.0,3.0].toTensor
    check df.filter(f{`x` < 2.0})["x", float] == [1.0].toTensor

    check df.filter(f{1.0 == `x`})["x", float] == [1.0].toTensor
    check df.filter(f{1.0 != `x`})["x", float] == [2.0,3.0].toTensor
    check df.filter(f{1.0 < `x`})["x", float] == [2.0,3.0].toTensor
    check df.filter(f{1.0 <= `x`})["x", float] == [1.0,2.0,3.0].toTensor
    check df.filter(f{2.0 > `x`})["x", float] == [1.0].toTensor

  test "float comparisons with int Value":
    let df = toDf({"x" : [%~ 1, %~ 2, %~ 3]})
    check df.filter(f{`x` == 1.0})["x", int] == [1].toTensor
    check df.filter(f{`x` != 1.0})["x", int] == [2,3].toTensor
    check df.filter(f{`x` > 1.0})["x", int] == [2,3].toTensor
    check df.filter(f{`x` >= 1.0})["x", int] == [1,2,3].toTensor
    check df.filter(f{`x` < 2.0})["x", int] == [1].toTensor

    check df.filter(f{1.0 == `x`})["x", int] == [1].toTensor
    check df.filter(f{1.0 != `x`})["x", int] == [2,3].toTensor
    check df.filter(f{1.0 < `x`})["x", int] == [2,3].toTensor
    check df.filter(f{1.0 <= `x`})["x", int] == [1,2,3].toTensor
    check df.filter(f{2.0 > `x`})["x", int] == [1].toTensor

  test "bool comparisons":
    let df = toDf({"x" : [true, false, true]})
    check df.filter(f{`x` == true})["x", bool] == [true, true].toTensor
    check df.filter(f{`x` == false})["x", bool] == [false].toTensor

    check df.filter(f{`x` != true})["x", bool] == [false].toTensor
    check df.filter(f{`x` != false})["x", bool] == [true, true].toTensor

  test "string comparisons":
    let df = toDf({"x" : ["foo", "bar", "baz"]})
    check df.filter(f{`x` == "foo"})["x", string] == ["foo"].toTensor
    check df.filter(f{`x` != "foo"})["x", string] == ["bar", "baz"].toTensor
    check df.filter(f{`x` in ["foo", "bar"]})["x", string] == ["foo", "bar"].toTensor
    echo df.filter(f{`x` notin ["foo", "bar"]})["x", string]
    check df.filter(f{`x` notin ["foo", "bar"]})["x", string] == ["baz"].toTensor
