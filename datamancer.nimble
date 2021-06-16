# Package

version       = "0.1.0"
author        = "Vindaar"
description   = "A dataframe library with a dplyr like API"
license       = "MIT"
srcDir        = "src"


# Dependencies

requires "nim >= 1.2.0"
requires "https://github.com/Vindaar/seqmath >= 0.1.11"
requires "arraymancer >= 0.6.2"

task test, "Run standard tests":
  exec "nim c -r tests/testDf.nim"
  exec "nim c -r tests/tests.nim"
  exec "nim c -r tests/test_issue20.nim"
  exec "nim c -r tests/test_issue28.nim"
  exec "nim c -r tests/testsFormula.nim"
