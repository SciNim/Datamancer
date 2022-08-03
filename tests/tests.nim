import unittest
import datamancer

import tables, sets
import seqmath

proc almostEq(a, b: float, epsilon = 1e-8): bool =
  ## version of `almostEqual` for testing, which prints the values, if
  ## they mismatch
  result = almostEqual(a, b, epsilon)
  if not result:
    echo "Comparison failed: a = ", a, ", b = ", b

suite "Value":
  let
    v1 = %~ 1
    v2 = %~ 1.5
    v3 = %~ true
    v4 = %~ 'a'
    # `v5` itself is already a test, whether we can hash `Value`
    v5 = %~ { "test" : v1,
              "some" : v2,
              "heterogeneous" : v3,
              "fields" : v4 }.toOrderedTable
    v6 = Value(kind: VNull)

  test "Storing in sets":
    var valueSet = initHashSet[Value]()
    valueSet.incl v1
    valueSet.incl v2
    valueSet.incl v3
    valueSet.incl v4
    valueSet.incl v5
    valueSet.incl v6
    check v1 in valueSet
    check v2 in valueSet
    check v3 in valueSet
    check v4 in valueSet
    check v5 in valueSet
    check v6 in valueSet
    check valueSet.card == 6

  test "Storing in tables":
    var tab = initTable[string, Value]()
    tab["v1"] = v1
    tab["v2"] = v2
    tab["v3"] = v3
    tab["v4"] = v4 # is converted to string!
    tab["v5"] = v5
    tab["v6"] = v6
    check tab.len == 6
    check tab["v1"] == v1
    check tab["v2"] == v2
    check tab["v3"] == v3
    check tab["v4"] == v4
    check tab["v5"] == v5
    check tab["v6"] == v6

  test "Extracting values":
    check v1.toInt == 1
    check v2.toFloat == 1.5
    check v3.toBool == true
    check v4.toStr == "a"
    check v1.toStr == "1"
    check v2.toStr == "1.5"
    check v3.toStr == "true"
    expect(ValueError):
      discard v5.toStr
    expect(ValueError):
      discard v6.toStr

  test "Direct `isNumber` check":
    # Note: this test checks basically whether the content of a `Value`
    # to be echoed is recognized as a number (in which case it's engulfed
    # by literal ``"``) or a normal string (no ``"``)
    let n1 = "1.1"
    let n2 = "1.3e5"
    let n3 = "aba"
    let n4 = "1..1"
    let n5 = "1.123"
    let n6 = "1.5e5E5"
    let n7 = "e"
    let n8 = "E"
    let n9 = "."
    let n10 = "1e"
    let n11 = "1E"
    let n12 = "1."
    let n13 = "e1"
    let n14 = "E1"
    let n15 = ".1"
    # and some actually valid floats
    let n16 = "6.084E+01"
    let n17 = "1.676E+01"
    let n18 = "6.863E+00"
    let n19 = "2.007E+00"
    let n20 = "9.329E-01"
    let n21 = "2.441E-04"
    let n22 = "-2.441E-04"
    let n23 = "--2.441"
    let n24 = "-6.836E-04 "
    let n25 = "2.930E-04    "
    let n26 = "2.930E-04  d   "
    check n1.isNumber
    check n2.isNumber
    check not n3.isNumber
    check not n4.isNumber
    check n5.isNumber
    check not n6.isNumber
    check not n7.isNumber
    check not n8.isNumber
    check not n9.isNumber
    check not n10.isNumber
    check not n11.isNumber
    check n12.isNumber
    check not n13.isNumber
    check not n14.isNumber
    check not n15.isNumber
    check n16.isNumber
    check n17.isNumber
    check n18.isNumber
    check n19.isNumber
    check n20.isNumber
    check n21.isNumber
    check n22.isNumber
    check not n23.isNumber
    check n24.isNumber
    check n25.isNumber
    check not n26.isNumber

  test "String conversion":
    # Note: this test checks basically whether the content of a `Value`
    # to be echoed is recognized as a number (in which case it's engulfed
    # by literal ``"``) or a normal string (no ``"``)
    # This uses `isNumber` internally.
    let n1 = %~ "1.1"
    let n2 = %~ "1.3e5"
    let n3 = %~ "aba"
    let n4 = %~ "1..1"
    let n5 = %~ "1.123"
    let n6 = %~ "1.5e5E5"
    let n7 = %~ "e"
    let n8 = %~ "E"
    let n9 = %~ "."
    let n10 = %~ "1e"
    let n11 = %~ "1E"
    let n12 = %~ "1."
    let n13 = %~ "e1"
    let n14 = %~ "E1"
    let n15 = %~ ".1"
    # and some actually valid floats
    let n16 = %~ "6.084E+01"
    let n17 = %~ "1.676E+01"
    let n18 = %~ "6.863E+00"
    let n19 = %~ "2.007E+00"
    let n20 = %~ "9.329E-01"
    let n21 = %~ "2.441E-04"
    let n22 = %~ "-2.441E-04"
    check $n1 == "\"1.1\""
    check $n2 == "\"1.3e5\""
    check $n3 == "aba"
    check $n4 == "1..1"
    check $n5 == "\"1.123\""
    check $n6 == "1.5e5E5"
    check $n7 == "e"
    check $n8 == "E"
    check $n9 == "."
    check $n10 == "1e"
    check $n11 == "1E"
    check $n12 == "\"1.\""
    check $n13 == "e1"
    check $n14 == "E1"
    check $n15 == ".1"
    check $n16 == "\"6.084E+01\""
    check $n17 == "\"1.676E+01\""
    check $n18 == "\"6.863E+00\""
    check $n19 == "\"2.007E+00\""
    check $n20 == "\"9.329E-01\""
    check $n21 == "\"2.441E-04\""
    check $n22 == "\"-2.441E-04\""

    # check that `emphStrNumber` can be disabled
    check n16.pretty(emphStrNumber = false) == "6.084E+01"
    check n17.pretty(emphStrNumber = false) == "1.676E+01"
    check n18.pretty(emphStrNumber = false) == "6.863E+00"
    check n19.pretty(emphStrNumber = false) == "2.007E+00"
    check n20.pretty(emphStrNumber = false) == "9.329E-01"
    check n21.pretty(emphStrNumber = false) == "2.441E-04"
    check n22.pretty(emphStrNumber = false) == "-2.441E-04"


  test "Math with Values":
    check (v1 * v2).kind == VFloat
    check (v1 + v1).kind == VFloat
    check (v1 + v1) == %~ 2
    check (v1 * v1).kind == VFloat
    check almostEq((v1 * v2).toFloat, 1.5)
    check almostEq((v1 / v2).toFloat, 2.0 / 3.0)
    check v1 * v6 == Value(kind: VNull)

suite "Formula":
  test "Testing ~ formula creation using f{} macro":
    let f = f{"meanCty" ~ (c"hwy" + c"cty")}
    # manual parens still appear in `name`!
    check f.name == "(~ meanCty ((+ hwy cty)))"
    # TODO: Add more tests here...
    # create with `.` access
    let tup = (a: 5.5, b: "ok")
    let h = f{%~ tup.a == %~ tup.b}
    check h.kind == fkVariable
    check h.val == %~ false
    check h.name == "(== (%~ tup.a) (%~ tup.b))"

    let f2 = f{float: "min" << min(c"runTimes")}
    check $f2 == "min" # LHS of formula
    check f2.name == "(<< min (min runTimes))"


  test "Evaluate raw formula (no DF column dependency)":
    # arithmetic works
    check evaluate(f{1 + 2}) == %~ 3
    # parens work in arithmetic
    check evaluate(f{2 * (5 - 3)}) == %~ 4
    check evaluate(f{10 / 10}) == %~ 1
    # strings are evaluated to themseles
    check evaluate(f{"hwy"}) == %~ "hwy"

  test "Formula, literal on RHS":
    let f = f{"from" ~ 0}
    check f.name == "(~ from 0)"

  test "Test formula creation of type `fkVariable`":
    let f1 = f{"Test"}
    let f2 = f{1.1}
    let f3 = f{4}
    let f4 = f{true}
    check f1.kind == fkVariable
    check f2.kind == fkVariable
    check f3.kind == fkVariable
    check f4.kind == fkVariable
    check $f1 == "Test"
    check $f2 == "1.1"
    check $f3 == "4"
    check $f4 == "true"
