# Package

version       = "0.3.4"
author        = "Vindaar"
description   = "A dataframe library with a dplyr like API"
license       = "MIT"
srcDir        = "src"


# Dependencies

requires "nim >= 1.2.0"
requires "https://github.com/Vindaar/seqmath >= 0.1.11"
requires "arraymancer >= 0.7.1"

task test, "Run standard tests":
  exec "nim c -r tests/testDf.nim"
  exec "nim c -r tests/tests.nim"
  exec "nim c -r tests/test_issue20.nim"
  exec "nim c -r tests/test_issue28.nim"
  exec "nim c -r tests/testsFormula.nim"
  exec "nim c -r tests/testParse.nim"

import os, strutils, strformat
const
  pkgName = "datamancer"
  orgFile = "docs" / (pkgName & ".org")
  rstFile = "docs" / (pkgName & ".rst")
  rstFileAuto = "docs" / (pkgName & "_autogen.rst")

template canImport(x: untyped): untyped =
  compiles:
    import x

when canImport(docs / docs):
  # can define the `gen_docs` task (docs already imported now)
  # this is to hack around weird nimble + nimscript behavior.
  # when overwriting an install nimble will try to parse the generated
  # nimscript file and for some reason then it won't be able to import
  # the module (even if it's put into `src/`).
  task gen_docs, "Generate datamancer documentation":
    # build the actual docs and the index
    exec "pandoc " & orgFile & " -o " & rstFile
    buildDocs(
      "src/", "docs/",
      defaultFlags = "--hints:off --warnings:off"
    )
