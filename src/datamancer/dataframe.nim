import macros, tables, strutils, options, fenv, sets, hashes, sugar, math
import sequtils, stats, strformat, algorithm, parseutils

# for error messages to print types
import typetraits

import arraymancer/tensor
export tensor

import value
export value

import column
export column

import df_types
export df_types

import formula
export formula

# formulaNameMacro contains a macro and type based on the fallback `FormulaNode`,
# which is used to generate the names of each `FormulaNode` in lisp representation
import formulaNameMacro
export formulaNameMacro

const ValueNull* = Value(kind: VNull)

# ---------- Simple 1 line helper procs ----------
template ncols*(df: DataFrame): int =
  ## Returns the number of columns in the `DataFrame df`.
  df.data.len
proc high*(df: DataFrame): int =
  ## Returns the highest possible index in any column of the input `DataFrame df`.
  df.len - 1

# ---------- Forward declaraions ----------

# ---------- DataFrame construction ----------

proc select*[T: string | FormulaNode](df: DataFrame, cols: varargs[T]): DataFrame
proc newDataFrame*(size = 8,
                   kind = dfNormal): DataFrame =
  ## Initialize a DataFrame by initializing the underlying table for `size` number
  ## of columns. The given size will be rounded up to the next power of 2!
  ##
  ## The `kind` argument can be used to create a grouped `DataFrame` from the start.
  ## Be very careful with this and instead use `groub_by` to create a grouped DF!
  result = DataFrame(kind: kind,
                     data: initOrderedTable[string, Column](nextPowerOfTwo(size)),
                     len: 0)

proc clone(data: OrderedTable[string, Column]): OrderedTable[string, Column] =
  ## clones the given table by making sure the columns are copied
  result = initOrderedTable[string, Column]()
  for key in keys(data):
    result[key] = data[key].clone

proc clone*(df: DataFrame): DataFrame =
  ## Returns a cloned version of `df`, which deep copies the tensors of the
  ## `DataFrame`. This makes sure there is *no* data sharing due to reference
  ## semantics between the input and output DF.
  result = DataFrame(kind: df.kind)
  result.len = df.len
  result.data = df.data.clone
  case df.kind
  of dfGrouped:
    result.groupMap = df.groupMap
  else: discard

proc shallowCopy*(df: DataFrame): DataFrame =
  ## Creates a shallowCopy of the `DataFrame` that does ``not`` deep copy the tensors.
  ##
  ## Used to return a different DF that contains the same data for those columns
  ## that exist in both. Only the `OrderedTable` object is cloned to not reference the
  ## same column keys. This is the default for all procedures that take and return
  ## a DF.
  result = DataFrame(kind: df.kind)
  result.len = df.len
  # simply do a regular copy of the DF (no deep copy of the data, but a new
  # table)
  result.data = df.data
  case df.kind
  of dfGrouped:
    result.groupMap = df.groupMap
  else: discard

# ---------- General convenience helpers ----------

func len*[T](t: Tensor[T]): int =
  ## Helper proc for 1D `Tensor[T]` to return the length of the vector, which
  ## corresponds to a length of a DF column.
  assert t.rank == 1
  result = t.size

proc contains*(df: DataFrame, key: string): bool =
  ## Checks if the `key` names column in the `DataFrame`.
  result = df.data.hasKey(key)

iterator keys*(df: DataFrame): string =
  ## Iterates over all column keys of the input `DataFrame`.
  for k in keys(df.data):
    yield k

proc getKeys[T](tab: OrderedTable[string, T]): seq[string] =
  ## Returns the keys of the table as a seq.
  for k in keys(tab):
    result.add k

proc getKeys*(df: DataFrame): seq[string] =
  ## Returns the column keys of a `DataFrame` as a sequence.
  ##
  ## The order is the same as the order of the keys in the DF.
  for k in keys(df):
    result.add k

# -------------------------------
# ---------- Accessors ----------
# -------------------------------

proc `[]`*(df: DataFrame, k: string): var Column {.inline.} =
  ## Returns the column `k` from the `DataFrame` as a mutable object.
  assert not df.isNil, "DF is used in uninitialized context!"
  result = df.data[k]

proc `[]`*(df: DataFrame, k: Value): Column {.inline.} =
  ## Returns the column `k` from the `DataFrame` for a `Value` object
  ## storing a column reference.
  assert not df.isNil, "DF is used in uninitialized context!"
  result = df.data[k.toStr]

proc `[]`*(df: DataFrame, k: string, idx: int): Value {.inline.} =
  ## Returns the element at index `idx` in column `k` directly as a `Value`, without
  ## converting (to `Value`) and returning the whole column first.
  ##
  ## An efficient way to access few individual elements without specifying a
  ## data type.
  ##
  ## If `idx` is not within the DF's length an `IndexError` is raised.
  assert not df.isNil, "DF is used in uninitialized context!"
  result = df.data[k][idx, Value]

proc `[]`*[T](df: DataFrame, k: string, idx: int, dtype: typedesc[T]): T {.inline.} =
  ## Returns the element at index `idx` in column `k` directly, without returning
  ## returning the whole column first.
  ##
  ## If `dtype` corresponds to the data type of the type of the underlying `Tensor`,
  ## no type conversions need to be performed.
  ##
  ## If `dtype` does ``not`` match the data type of the underlying `Tensor` the value
  ## will be read as its native type and then converted to `dtype` via explicit conversion.
  ##
  ## If `idx` is not within the DF's length an `IndexError` is raised.
  assert not df.isNil, "DF is used in uninitialized context!"
  result = df.data[k][idx, dtype]

proc `[]`*[T](df: DataFrame, k: string, slice: Slice[int], dtype: typedesc[T]): Tensor[T] {.inline.} =
  ## Returns the elements in `slice` in column `k` directly, without returning the
  ## whole column first as a tensor of type `dtype`.
  ##
  ## If `dtype` corresponds to the data type of the type of the underlying `Tensor`,
  ## no type conversions need to be performed and the slice is returned as is.
  ##
  ## If `dtype` does ``not`` match the data type of the underlying `Tensor` the slice
  ## will be read as its native type and then converted to `dtype` via explicit
  ## `asType` conversion.
  assert not df.isNil, "DF is used in uninitialized context!"
  result = df.data[k][slice.a .. slice.b, dtype]

proc `[]`*(df: DataFrame, k: string, slice: Slice[int]): Column {.inline.} =
  ## Returns the elements in `slice` in column `k` directly as a new `Column`
  ## without returning the full column first.
  assert not df.isNil, "DF is used in uninitialized context!"
  result = df.data[k][slice.a .. slice.b]

template `^^`(df, i: untyped): untyped =
  (when i is BackwardsIndex: df.len - int(i) else: int(i))

proc `[]`*[T, U](df: DataFrame, rowSlice: HSlice[T, U]): DataFrame =
  ## Returns a slice of the data frame given by `rowSlice`, which is simply a
  ## subset of the input data frame.
  let keys = getKeys(df)
  result = newDataFrame(df.ncols)
  let a = (df ^^ rowSlice.a)
  let b = (df ^^ rowSlice.b)
  for k in keys:
    result[k] = df[k, a .. b]
  # add 1, because it's an ``inclusive`` slice!
  result.len = (b - a) + 1

proc `[]`*[T](df: DataFrame, key: string, dtype: typedesc[T]): Tensor[T] =
  ## Returns the column `key` as a Tensor of type `dtype`.
  ##
  ## If `dtype` matches the actual data type of the `Tensor` underlying the column,
  ## this is a no copy operation. Otherwise a type conversion is performed on the
  ## `Tensor` using `asType`
  ##
  ## This is the easiest way to access the raw `Tensor` underlying a column for
  ## further processing.
  runnableExamples:
    import sequtils
    let df = seqsToDf({"x" : toSeq(1 .. 5)})
    let t: Tensor[int] = df["x", int]
    doAssert t.sum == 15
  result = df.data[key].toTensor(dtype)

proc get*(df: DataFrame, key: string): Column {.inline.} =
  ## Returns the column of `key`.
  ##
  ## Includes an explicit check on whether the column exists in the `DataFrame`
  ## and raises a `KeyError` with a custom message in case the key does not
  ## exist.
  ##
  ## This is mainly useful in an application where the exception message should
  ## contain information about the fact that we're accessing a *data frame* as
  ## a regular access using `[]` already raises a `KeyError`.
  if key in df:
    result = df[key]
  else:
    # create column of constants or raise?
    raise newException(KeyError, "Given string " & $key & " is not a valid column!")

proc `[]=`*(df: var DataFrame, k: string, col: Column) {.inline.} =
  ## Assigns the column `col` as a column with key `k` to the `DataFrame`.
  ##
  ## If the length of the column does not match the existing DF length (unless
  ## it is 0), a `ValueError` is raised.
  if df.isNil:
    df = newDataFrame()
  df.data[k] = col
  if df.len == col.len or df.len == 0:
    df.len = col.len
  else:
    raise newException(ValueError, "Given column length of " & $col.len &
      " does not match DF length of: " & $df.len & "!")

proc `[]=`*[T: SomeNumber | string | bool](df: var DataFrame, k: string, t: T) {.inline.} =
  ## Assigns a scalar `t` as a constant column to the `DataFrame`.
  runnableExamples:
    var df = seqsToDf({"x" : @[1,2,3]})
    df["y"] = 5
    doAssert df["y"].isConstant
    doAssert df["y"].len == 3
    doAssert df["y", 0, int] == 5
    doAssert df["y", 1, int] == 5
    doAssert df["y", 2, int] == 5
  df[k] = constantColumn(t, df.len)

proc `[]=`*[T: Tensor | seq | array](df: var DataFrame, k: string, t: T) {.inline.} =
  ## Assigns a `Tensor`, `seq` or `array` to the `DataFrame df` as column key `k`.
  ##
  ## If the length of the input `t` does not match the existing DF's length, a `ValueError`
  ## is raised.
  df[k] = toColumn t

proc `[]=`*[T](df: var DataFrame, k: string, idx: int, val: T) {.inline.} =
  ## A low-level helper to assign a value `val` of type `T` directly to column `k` in
  ## the `DataFrame df` at index `idx`.
  ##
  ## If `idx` is not within the DF's length an `IndexError` is raised.
  ##
  ## WARNING: This procedure does not check the compatibility of the column types. Only
  ## use it if you know the type of `t` corresponds to the data type of the underlying
  ## column! Assign at an index on the ``column`` for a more sane behavior.
  runnableExamples:
    var df = seqsToDf({"x" : [1,2,3]})
    df["x", 1] = 5
    doAssert df["x", int] == [1,5,3].toTensor
    ## df["x", 2] = 1.2 <- produces runtime error that specif `kind` field in Column
    ## is inaccesible!

  # we depend on df.len != df.data.len in `innerJoin` among others. This is a somewhat
  # unsafe procedure!
  assert df.data[k].len > idx, "Invalid index " & $idx & " for DF column of length " & $df.data.len
  when T is float:
    df.data[k].fcol[idx] = val
  elif T is int:
    df.data[k].icol[idx] = val
  elif T is string:
    df.data[k].scol[idx] = val
  elif T is bool:
    df.data[k].bcol[idx] = val
  elif T is Value:
    df.data[k].ocol[idx] = val

proc `[]=`*[T](df: var Dataframe, fn: FormulaNode, key: string, val: T) =
  ## Evaluates the given `FormulaNode fn`, which needs to be a function returning a bool,
  ## and assigns a constant value `val` to all rows of column `key` matching the condition.
  ##
  ## This is a somewhat esoteric procedure, but can be used to mask rows matching some condition.
  runnableExamples:
    var df = seqsToDf({"x" : [1,2,3], "y" : [5,6,7]})
    df[f{`x` > 1}, "x"] = 5 ## assign 5 to all rows > 1
    doAssert df["x", int] == [1,5,5].toTensor
    doAssert df["y", int] == [5,6,7].toTensor ## remains unchanged
    df[f{`y` < 7}, "x"] = -1 ## can also refer to other columns of course
    doAssert df["x", int] == [-1,-1,5].toTensor
    doAssert df["y", int] == [5,6,7].toTensor ## still unchanged
  # eval boolean function on DF
  doAssert fn.kind == fkVector, "Function must be of kind `fkVector` " &
    "(i.e. function acting on a whole column)!"
  let filterIdx = fn.fnV(df)
  doAssert filterIdx.kind == colBool, "Function must return bool values! " &
    "Returns " & $fn.resType
  var col = df[key] # make mutable copy, reference semantics so data will be modified
  let bTensor = filterIdx.bCol
  for idx in 0 ..< bTensor.size:
    if bTensor[idx]: # if condition true
      col[idx] = val
  df[key] = col

proc asgn*(df: var DataFrame, k: string, col: Column) {.inline.} =
  ## Low-level assign, which does not care about sizes of column. If used with a given
  ## column of different length than the `DataFrame` length, it results in a ragged
  ## DF. ``Only`` use this if you intend to extend these columns later or won't use
  ## any other procedure taking a `DataFrame`.
  ##
  ## Used in `toTab` macro, where shorter columns are extended afterwards using
  ## `extendShortColumns`.
  df.data[k] = col

# ---------- Data frame construction from data ----------

proc extendShortColumns*(df: var DataFrame) =
  ## initial calls to `seqsToDf` and other procs may result in a ragged DF, which
  ## has less entries in certain columns than the data frame length.
  ## This proc fills up the mutable dataframe in those columns
  for k in keys(df):
    if df[k].len == 1:
      ## make it a constant column of `df` length
      df[k] = constantColumn(df[k][0, Value], df.len)
    elif df[k].len < df.len:
      let nFill = df.len - df[k].len
      df[k] = df[k].add nullColumn(nFill)

macro toTab*(args: varargs[untyped]): untyped =
  expectKind(args, nnkArglist)
  var s = args
  if args.len == 1 and args[0].kind == nnkTableConstr:
    # has to be tableConstr or simple ident
    s = args[0]
  elif args.len == 1 and args[0].kind notin {nnkIdent, nnkSym}:
    error("If only single argument it has to be an ident or symbol, " &
      "but " & $args[0].repr & " is of kind: " & $args[0].kind)
  let data = ident"columns"
  result = newStmtList()
  result.add quote do:
    var `data` = newDataFrame()
  for a in s:
    # let's just try to deal the compiler with it. It should fail on `toColumn` if we
    # cannot support it after all
    case a.kind
    of nnkExprColonExpr:
      let nameCh = a[0]
      let valCh = a[1]
      let colN = genSym(nskLet, "column")
      result.add quote do:
        let `colN` = `valCh`.toColumn
        asgn(`data`, `nameCh`, `colN`)
        `data`.len = max(`data`.len, `colN`.len)
    else:
      let colN = genSym(nskLet, "column")
      let aName = a.toStrLit
      result.add quote do:
        let `colN` = `a`.toColumn
        asgn(`data`, `aName`, `colN`)
        `data`.len = max(`data`.len, `colN`.len)
  result = quote do:
    block:
      `result`
      # finally fill up possible columns shorter than df.len
      `data`.extendShortColumns()
      `data`
  #echo result.treerepr
  #echo result.repr

template seqsToDf*(s: varargs[untyped]): untyped =
  ## converts an arbitrary number of sequences to a `DataFrame` or any
  ## number of key / value pairs where we have string / seq[T] pairs.
  toTab(s)

template colsToDf*(s: varargs[untyped]): untyped =
  ## converts an arbitrary number of columns to a `DataFrame` or any
  ## number of key / value pairs where we have string / seq[T] pairs.
  toTab(s)

template dataFrame*(s: varargs[untyped]): untyped =
  ## alias for `seqsToDf`
  toTab(s)

template toDf*(s: varargs[untyped]): untyped =
  ## alias for `seqsToDf`
  toTab(s)

proc toDf*(t: OrderedTable[string, seq[string]]): DataFrame =
  ## Creates a data frame from a table of seq[string].
  ##
  ## Note 1: This is mostly used for the old `readCsv` procedure, which is now called
  ## `readCsvAlt`. One should normally not have to deal with a table of strings as
  ## a DF input.
  ##
  ## Note 2: This proc assumes that the given entries in the `seq[string]`
  ## have been cleaned of white space. The `readCsv` proc takes care of
  ## this.
  result = DataFrame(len: 0)
  for k, v in t:
    var col = newColumn()
    # check first element of v for type
    if v.len > 0:
      # TODO: CLEAN UP
      var maybeNumber = v[0].isNumber
      var maybeInt = v[0].isInt
      if maybeNumber and maybeInt:
        # try as int
        try:
          let data = v.mapIt(it.parseInt)
          col = data.toColumn
        except ValueError:
          try:
            let data = v.mapIt(it.parseFloat)
            col = data.toColumn
          except ValueError:
            # then parse as value
            var data = newSeq[Value](v.len)
            for i, x in v:
              try:
                data[i] = %~ x.parseInt
              except ValueError:
                try:
                  data[i] = %~ x.parseFloat
                except ValueError:
                  data[i] = %~ x
            col = toColumn data
      elif maybeNumber:
        try:
          let data = v.mapIt(it.parseFloat)
          col = data.toColumn
        except ValueError:
          # then parse as value
          var data = newSeq[Value](v.len)
          for i, x in v:
            try:
              data[i] = %~ x.parseFloat
            except ValueError:
              data[i] = %~ x
          col = data.toColumn
      else:
        # try bool?
        try:
          let data = v.mapIt(it.parseBool)
          col = data.toColumn
        except ValueError:
          # keep as string
          col = v.toColumn
    result.data[k] = col
    result.len = max(result.data[k].len, result.len)
  result.extendShortColumns()

proc toDf*(t: OrderedTable[string, seq[Value]]): DataFrame =
  ## Creates a data frame from a table of `seq[Value]`.
  ##
  ## Note: This is also mainly a fallback option for old code.
  result = DataFrame(len: 0)
  for k, v in t:
    result[k] = v.toColumn
    result.len = max(v.len, result.len)
  result.extendShortColumns()

proc row*(df: DataFrame, idx: int, cols: varargs[string]): Value {.inline.} =
  ## Returns the row `idx` of the DataFrame `df` as a `Value` of kind `VObject`.
  ##
  ## If any `cols` are given, only those columns will appear in the resulting `Value`.
  runnableExamples:
    let df = seqsToDf({"x" : [1,2,3], "y" : [1.1, 2.2, 3.3], "z" : ["a", "b", "c"]})
    let row = df.row(0)
    doAssert row["x"] == %~ 1
    doAssert row["x"].kind == VInt
    doAssert row["y"] == %~ 1.1
    doAssert row["y"].kind == VFloat
    doAssert row["z"] == %~ "a"
    doAssert row["z"].kind == VString
  result = newVObject(length = cols.len)
  let mcols = if cols.len == 0: getKeys(df) else: @cols
  for col in mcols:
    result[col] = df[col][idx, Value]

proc assignRow(v: var Value, df: DataFrame, idx: int) =
  ## `v` needs to be a VObject with the exact same keys as `df`! Only used internally.
  for col in keys(df.data):
    v[col] = df[col][idx, Value]

iterator items*(df: DataFrame): Value =
  ## Returns each row of the `DataFrame df` as a Value of kind VObject.
  ##
  ## This is an inefficient way to iterate over all rows in a data frame, as we don't
  ## have type information at compile time. Thus we need to construct a (`Value` internal)
  ## table to store (key, value) pairs at runtime.
  ##
  ## It should only be used for convenience. To work with a data frame use procedures
  ## that are meant to modify / reduce / ... a data frame.
  var row = newVObject(length = df.ncols)
  for i in 0 ..< df.len:
    row.assignRow(df, i)
    yield row

iterator values*(df: DataFrame, cols: varargs[string]): Tensor[Value] {.inline.} =
  ## Yields all columns `cols` of `DataFrame df` as `Tensor[Value]` rows.
  ##
  ## Each row is yielded without column key information. The tensor is filled in the order
  ## of the existing columns. The first entry corresponds to the first column etc.
  ##
  ## This proc is usually not very useful.
  let mcols = if cols.len == 0: getKeys(df) else: @cols
  var res = newTensor[Value](mcols.len)
  # fill col seq with column references, so that we don't have to hash the keys
  # every single iteration
  var colSeq = newSeq[Column](mcols.len)
  for idx, k in mcols:
    colSeq[idx] = df.data[k]
  for idx in 0 ..< df.len:
    for j in 0 ..< mcols.len:
      res[j] = colSeq[j][idx, Value]
    yield res

func isColumn*(fn: FormulaNode, df: DataFrame): bool =
  ## Checks if the given `FormulaNode` as a string representation corresponds to a
  ## column in the `DataFrame`.
  runnableExamples:
    let fn = f{`x` * `x`}
    let df = seqsToDf({"x" : @[1, 2, 3]})
      .mutate(fn) # creates a new column of squared `x`
    doAssert fn.isColumn(df)

  result = $fn in df

func isConstant*(fn: FormulaNode, df: DataFrame): bool =
  ## Checks if the column referenced by the `FormulaNode fn` is a constant column
  ## in the `DataFrame`.
  ##
  ## If the column corresponding to `fn` does not exist, it returns `false` as well.
  ## Be sure to be aware whether `fn` is actually a formula, if you need to distinguish
  ## between constant / non constant columns.
  runnableExamples:
    let fn = f{"y"} # is a reference to a constant column.
    let df = seqsToDf({"x" : @[1, 2, 3], "y" : 5})
    doAssert fn.isConstant(df)

  result = $fn in df and df[$fn].isConstant

template withCombinedType*(df: DataFrame,
                           cols: seq[string],
                           body: untyped): untyped =
  ## A helper template to work with a `dtype` that encompasses all data types
  ## found in the `cols` of the input `DataFrame df`.
  ##
  ## It injects a variable `dtype` into the calling scope.
  runnableExamples:
    let df = seqsToDf({"x" : @[1, 2, 3], "y" : @[2, 3, 4], "z" : @[1.1, 2.2, 3.3]})
    withCombinedType(df, @["x", "y"]):
      doAssert dtype is int
    withCombinedType(df, @["x", "z"]):
      doAssert dtype is float # float can encompass `int` and `float` as we're lenient!

  var colSeq = newSeq[Column]() # need columns to extract correct combined type
  for k in cols:
    colSeq.add df[k]
  let combKind = combinedColKind(colSeq)
  case combKind
  of colInt:
    type dtype {.inject.} = int
    body
  of colFloat:
    type dtype {.inject.} = float
    body
  of colString:
    type dtype {.inject.} = string
    body
  of colBool:
    type dtype {.inject.} = bool
    body
  of colObject:
    type dtype {.inject.} = Value
    body
  of colNone, colConstant: doAssert false, "No valid type!"

proc add*[T: tuple](df: var DataFrame, args: T) =
  ## This procedure adds a given tuple as a new row to the DF.
  ##
  ## If the `DataFrame df` does not have any column yet, columns of the names
  ## given by the tuple field names will be created. Otherwise the tuple field
  ## names are ignored and only the order is considered for placement into
  ## the different columns.
  ##
  ## This should almost always be avoided, because it comes at a huge performance penalty.
  ## Every add causes a new allocation of every tensor of each column of
  ## length (N + 1). Only use this to add ``few`` (!!) rows to a DF. Otherwise
  ## consider storing your intermediate rows to be added in individual seqs
  ## or Tensors (if you know the length in advance) and add the new DF to
  ## the existing one using `bind_rows`, `add` or even `assignStack`.
  ##
  ## Possibly use the `add` template, which takes a `varargs[untyped]` if you
  ## do not wish to construct a tuple manually.
  ##
  ## NOTE: the input is treated in the order of the columns as they are
  ## stored in the internal `OrderedTable`! Make sure the order is as you
  ## think it is!
  runnableExamples:
    var df = newDataFrame()
    df.add((x: 1, y: 2))
    df.add((x: 3, y: 5))
    df.add((z: 5, x: 10)) ## after colums exist, tuple names are ignored!
    doAssert df.len == 3
    doAssert df["x", int] == [1, 3, 5].toTensor
    doAssert df["y", int] == [2, 5, 10].toTensor
  {.warning: "Using `add` to add rows to a DF individually is very slow. Be " &
    "sure to only add very few rows using this proc!".}
  doAssert args.tupleLen == df.ncols or df.ncols == 0
  if df.ncols == 0:
    for key, arg in fieldPairs(args):
      df[key] = newColumn(toColKind(typeof arg))
  var i = 0
  let keys = df.getKeys()
  for arg in fields(args):
    df.asgn(keys[i], df[keys[i]].add toColumn(arg))
    inc i
  df.len = df.len + (i div args.tupleLen)

macro varargsToTuple(args: varargs[untyped]): untyped =
  ## helper macro to convert a `varargs` to a tuple
  result = nnkTupleConstr.newTree()
  for arg in args:
    result.add arg

template add*(df: var DataFrame, args: varargs[untyped]): untyped =
  ## Helper overload for `add` above, which takes a varargs of values that are combined to
  ## a tuple automatically.
  ##
  ## The tuple field names will be default `Field0` etc. You cannot use this overload to
  ## define custom column names in an empty DF (but that use case should ideally be avoided
  ## anyway!).
  let tup = varargsToTuple(args)
  df.add(tup)

proc pretty*(df: DataFrame, numLines = 20, precision = 4, header = true): string =
  ## Converts the first `numLines` of the input `DataFrame df` to a string table.
  ##
  ## If the `numLines` argument is negative, will print all rows of the data frame.
  ##
  ## The precision argument is relevant for `VFloat` values, but can also be
  ## (mis-) used to set the column width, e.g. to show long string columns.
  ##
  ## The `header` is the `Dataframe with ...` information line, which can be disabled
  ## in the returned output to more easily output a simple DF as a string table.
  ##
  ## `pretty` is called by `$` with the default parameters.
  # TODO: need to improve printing of string columns if length of elements
  # more than `alignBy`.
  var maxLen = 6 # default width for a column name
  for k in keys(df):
    maxLen = max(k.len, maxLen)
  if header:
    result.add "Dataframe with " & $df.getKeys.len & " columns and " & $df.len & " rows:\n"
  let alignBy = max(maxLen + precision, 10)
  let num = if numLines > 0: min(df.len, numLines) else: df.len
  # write header
  result.add align("Idx", alignBy)
  for k in keys(df):
    result.add align($k, alignBy)
  result.add "\n"
  # now add data types
  result.add align("dtype:", alignBy)
  for k in keys(df):
    result.add align(toNimType(df[k].kind), alignBy)
  result.add "\n"
  for i in 0 ..< num:
    result.add align($i, alignBy)
    for k in keys(df):
      let element = pretty(df[k, i], precision = precision)
      if element.len < alignBy - 1:
        result.add align(element,
                         alignBy)
      else:
        result.add align(element[0 ..< alignBy - 4] & "...",
                         alignBy)
    result.add "\n"

template `$`*(df: DataFrame): string = df.pretty

proc drop*(df: var DataFrame, key: string) {.inline.} =
  ## Drops the given key from the `DataFrame`.
  df.data.del(key)

proc drop*(df: DataFrame, keys: varargs[string]): DataFrame =
  ## Returns a `DataFrame` with the given keys dropped.
  result = df.shallowCopy()
  for k in keys:
    result.drop(k)

proc colMax*(df: DataFrame, col: string, ignoreInf = true): float =
  ## Returns the maximum value along a given column, which must be readable
  ## as a float tensor.
  ##
  ## If `ignoreInf` is true `Inf` values are ignored.
  ##
  ## In general this is not intended as a user facing procedure. It is used
  ## in `ggplotnim` to determine scales. As a user a simple `df["foo", float].max`
  ## is preferred, unless the `ignoreInf` functionality seems useful.
  let t = df[col].toTensor(float)
  var idx = 0
  for x in t:
    if idx == 0:
      result = x
    if ignoreInf and classify(x) == fcInf:
      inc idx
      continue
    result = max(x, result)
    inc idx

proc colMin*(df: DataFrame, col: string, ignoreInf = true): float =
  ## Returns the minimum value along a given column, which must be readable
  ## as a float tensor.
  ##
  ## If `ignoreInf` is true `Inf` values are ignored.
  ##
  ## In general this is not intended as a user facing procedure. It is used
  ## in `ggplotnim` to determine scales. As a user a simple `df["foo", float].max`
  ## is preferred, unless the `ignoreInf` functionality seems useful.
  let t = df[col].toTensor(float)
  var idx = 0
  for x in t:
    if idx == 0:
      result = x
    if ignoreInf and classify(x) == fcNegInf:
      inc idx
      continue
    result = min(x, result)
    inc idx

proc bind_rows*(dfs: varargs[(string, DataFrame)], id: string = ""): DataFrame =
  ## `bind_rows` combines several data frames row wise (i.e. data frames are
  ## stacked on top of one another).
  ##
  ## The origin of each row is indicated in a new `id` column, where the values are
  ## the first argument in each of the given tuples.
  ##
  ## If a given column does not exist in one of the data frames, the corresponding
  ## rows of the data frame missing it, will be filled with `VNull`.
  runnableExamples:
    let a = [1, 2, 3]
    let b = [3, 4, 5]
    let c = [4, 5, 6, 7]
    let d = [8, 9, 10, 11]

    let df = seqsToDf({"a" : a, "b" : b})
    let df2 = seqsToDf({"a" : c, "b" : d})
    import sequtils

    block:
      let res = bind_rows([("A", df), ("B", df2)], id = "From")
      doAssert res.len == 7
      doAssert res.ncols == 3
      doAssert res["a", int] == concat(@a, @c).toTensor
      doAssert res["b", int] == concat(@b, @d).toTensor
      doAssert res["From", string] == concat(newSeqWith(3, "A"),
                                             newSeqWith(4, "B")).toTensor
    block:
      let df3 = seqsToDf({"a" : c, "d" : d})
      let res = bind_rows([("A", df), ("B", df3)], id = "From")
      doAssert res.ncols == 4
      doAssert res["a", int] == concat(@a, @c).toTensor
      doAssert res["b"].kind == colObject
      doAssert res["b", Value] == [%~ 3, %~ 4, %~ 5, ## equivalent to `b`
                                   null(), null(), null(), null()].toTensor
      doAssert res["d"].kind == colObject
      doAssert res["d", Value] == [null(), null(), null(),
                                   %~ 8, %~ 9, %~ 10, %~ 11].toTensor ## equivalent to `d`
      doAssert res["From", string] == concat(newSeqWith(3, "A"),
                                             newSeqWith(4, "B")).toTensor


  result = DataFrame(len: 0)
  var totLen = 0
  for (idVal, df) in dfs:
    totLen += df.len
    # first add `id` column
    if id.len > 0 and id notin result:
      result.asgn(id, toColumn( newTensorWith(df.len, idVal) ))
    elif id.len > 0:
      result.asgn(id, result[id].add toColumn( newTensorWith(df.len, idVal) ))
    var lastSize = 0
    for k in keys(df):
      if k notin result:
        # create this new column consisting of `VNull` up to current size
        if result.len > 0:
          result.asgn(k, nullColumn(result.len))
        else:
          result.asgn(k, newColumn(df[k].kind))
      # now add the current vector
      if k != id:
        # TODO: write a test for multiple bind_rows calls in a row!
        result.asgn(k, result[k].add df[k])
      lastSize = max(result[k].len, lastSize)
    result.len = lastSize
  # possibly extend vectors, which have not been filled with `VNull` (e.g. in case
  # the first `df` has a column `k` with `N` entries, but another `M` entries are added to
  # the `df`. Since `k` is not found in another `df`, it won't be extend in the loop above
  for k in keys(result):
    if result[k].len < result.len:
      # extend this by `VNull`
      result.asgn(k, result[k].add nullColumn(result.len - result[k].len))
  doAssert totLen == result.len, " totLen was: " & $totLen & " and result.len " & $result.len

template bind_rows*(dfs: varargs[DataFrame], id: string = ""): DataFrame =
  ## Overload of `bind_rows` above, for automatic creation of the `id` values.
  ##
  ## Using this proc, the different data frames will just be numbered by their
  ## order in the `dfs` argument and the `id` column is filled with those values.
  ## The values will always appear as strings, even though we use integer
  ## numbering.
  ##
  ## `bind_rows` combines several data frames row wise (i.e. data frames are
  ## stacked on top of one another).
  ## If a given column does not exist in one of the data frames, the corresponding
  ## rows of the data frame missing it, will be filled with `VNull`.
  runnableExamples:
    let a = [1, 2, 3]
    let b = [3, 4, 5]
    let c = [4, 5, 6, 7]
    let d = [8, 9, 10, 11]

    let df = seqsToDf({"a" : a, "b" : b})
    let df2 = seqsToDf({"a" : c, "b" : d})
    import sequtils

    block:
      let res = bind_rows([df, df2])
      doAssert res.len == 7
      doAssert res.ncols == 2
      doAssert res["a", int] == concat(@a, @c).toTensor
      doAssert res["b", int] == concat(@b, @d).toTensor
    block:
      let res = bind_rows([df, df2], "From")
      doAssert res.len == 7
      doAssert res.ncols == 3
      doAssert res["a", int] == concat(@a, @c).toTensor
      doAssert res["b", int] == concat(@b, @d).toTensor
      doAssert res["From", string] == concat(newSeqWith(3, "0"),
                                             newSeqWith(4, "1")).toTensor

  var ids = newSeq[string]()
  for i, df in dfs:
    ids.add $i
  let args = zip(ids, dfs)
  bind_rows(args, id)

proc add*(df: var DataFrame, dfToAdd: DataFrame) =
  ## The simplest form of "adding" a data frame, resulting in both data frames stacked
  ## vertically on top of one another.
  ##
  ## If the keys match exactly or `df` is empty `dfToAdd` will be stacked below.
  ## This makes a key check and then calls `bind_rows` for the job.
  ##
  ## If they don't match a `ValueError` is thrown.
  runnableExamples:
    let a = [1, 2, 3]
    let b = [3, 4, 5]
    let c = [4, 5, 6, 7]
    let d = [8, 9, 10, 11]

    let df = seqsToDf({"a" : a, "b" : b})
    let df2 = seqsToDf({"a" : c, "b" : d})
    import sequtils
    block:
      var dfRes = newDataFrame()
      dfRes.add df
      doAssert dfRes.len == 3
      dfRes.add df2
      doAssert dfRes.len == 7
      try:
        dfRes.add seqsToDf({"c": [1,3]})
      except ValueError:
        discard

  if df.isNil or df.len == 0:
    df = dfToAdd
  elif dfToAdd.len == 0:
    discard
  else:
    if df.getKeys.sorted != dfToAdd.getKeys.sorted:
       raise newException(ValueError, "All keys must match to add data frames!")
    df = bind_rows([("", df), ("", dfToAdd)])

proc assignStack*(dfs: seq[DataFrame]): DataFrame =
  ## Returns a data frame built as a stack of the data frames in the sequence.
  ##
  ## This is a somewhat unsafe procedure as it trades performance for safety. It's
  ## mainly intended to be used internally to speed up stacking outputs of
  ## certain operations.
  ##
  ## In contrast to calling `add` multiple times, `assignStack` preallocates all
  ## data required for ``all`` arguments immediately and performs slice assignments.
  ## If your need to stack many equivalent data frames, use this procedure.
  ##
  ## All dataframes must have matching keys and column types. It should only
  ## be called from places where this is made sure as the point of the
  ## procedure is speeding up assignment for cases where we know this holds.
  if dfs.len == 0: return newDataFrame()
  elif dfs.len == 1: return dfs[0]
  let df0 = dfs[0]
  result = newDataFrame(df0.getKeys().len)
  # 1. determine required lengths of final columns
  var lengths = 0
  for df in dfs:
    inc lengths, df.len
  # 2. generate output columns of correct type and length
  for k in df0.getKeys():
    result[k] = newColumn(df0[k].kind, lengths)
    # 2a. if column is constant, already assign its value
    if df0[k].kind == colConstant:
      result[k].cCol = df0[k].cCol
  # 3. walk over each output column and assign each slice
  for k in result.getKeys():
    var col = result[k]
    var idx = 0
    for df in dfs:
      if df.len == 0: continue
      col[idx .. idx + df.len - 1] = df[k]
      inc idx, df.len
    result[k] = col

proc hashColumn(s: var seq[Hash], c: Column, finish: static bool = false) =
  ## Performs a partial hash of a DF. I.e. a single column, where
  ## the hash is added to each index in `s`. The hash is not finalized,
  ## rather the idea is to use this to hash all columns on `s` first.
  ##
  ## Currently not used (ref. issue #12).
  # NOTE: this distinction is important to not generate a full tensor for
  # the `withNativeTensor` call in case the input is a constant!
  if c.kind == colConstant:        # if constant, don't have to access `t[idx]` all the time
    let hConst = hash(c[0, Value]) # just hash first element and combine with all hashes
    for idx in 0 ..< s.len:
      when not finish:
        s[idx] = s[idx] !& hConst
      else:
        s[idx] = !$(s[idx] !& hConst)
  else: # else hash everything
    withNativeTensor(c, t):
      assert s.len == t.size
      for idx in 0 ..< t.size:
        when not finish:
          s[idx] = s[idx] !& hash(t[idx])
        else:
          s[idx] = !$(s[idx] !& hash(t[idx]))

proc buildColHashes(df: DataFrame, keys: seq[string]): seq[seq[Value]] =
  ## Computes a sequence of `Value VObject` elements from the given
  ## columns. This is to avoid issue #12 (hash collisions if many input
  ## values present).
  ##
  ## NOTE: This version is up to a factor of ~2.5 or so slower than the old
  ## hashing based version (on the upside we have a different solution for the
  ## `groups` iterator, which is the same speed). Keep this in mind for the future
  ## and optimize it further.
  result = newSeq[seq[Value]](df.len)
  # determine columns
  let mcols = if keys.len == 0: getKeys(df) else: @keys
  # assign columns to a seq (avoid key lookup)
  var colCols = newSeq[Tensor[Value]](mcols.len)
  for i, col in mcols:
    colCols[i] = df[col, Value]
  # assign rows
  var row = newSeq[Value](mcols.len)
  for i in 0 ..< df.len:
    for j, col in mcols:
      row[j] = colCols[j][i]
    result[i] = row

proc selectTensors(df: DataFrame, keys: seq[string]): seq[Tensor[Value]] =
  ## Returns a subset of the `df` containing all given column of the `keys`
  ## in a sequence of `Tensor[Value]`.
  ##
  ## Used as a workaround to issue #12.
  result = newSeq[Tensor[Value]](keys.len)
  for i, k in keys:
    result[i] = df[k, Value]

proc row(cols: seq[Tensor[Value]], idx: int): seq[Value] =
  ## From the result of `selectTensors`, returns a single `seq[Value]` of the
  ## "row" at index `idx`.
  result = newSeq[Value](cols.len)
  for i, col in cols:
    result[i] = col[idx]

proc assignRow(row: var seq[Value], cols: seq[Tensor[Value]], idx: int) =
  ## From the result of `selectTensors`, assigns the mutable `seq[Value]` the values for
  ## "row" at index `idx`.
  for i, col in mpairs(row):
    col = cols[i][idx]

proc arrange*(df: DataFrame, by: varargs[string], order = SortOrder.Ascending): DataFrame
iterator groups*(df: DataFrame, order = SortOrder.Ascending): (seq[(string, Value)], DataFrame) =
  ## Yields the subgroups of a grouped DataFrame `df` and the `(key, Value)`
  ## pairs that were used to create the subgroup.
  ##
  ## If `df` has more than one grouping, a subgroup is defined by the pair of the groupings.
  ## For example: `mpg.group_by("class", "cyl")` will yield all pairs of car `("class", "cyl")`.
  ##
  ## Note: only non empty data frames will be yielded!
  runnableExamples:
    let df = seqsToDf({ "Class" : @["A", "C", "B", "B", "A", "C", "C"],
                        "Num" : @[1, 5, 3, 4, 8, 7, 2] })
      .group_by("Class")
    let expClass = ["A", "B", "C"]
    let dfA = seqsToDf({ "Class" : ["A", "A"], "Num" : [1, 8] })
    let dfB = seqsToDf({ "Class" : ["B", "B"], "Num" : [3, 4] })
    let dfC = seqsToDf({ "Class" : ["C", "C", "C"], "Num" : [5, 7, 2] })
    let expDf = [dfA, dfB, dfC]
    var idx = 0
    for t, subDf in groups(df):
      doAssert t[0][0] == "Class" # one grouping (first `[0]`), by `"Class"`
      doAssert t[0][1] == %~ expClass[idx] # one grouping (first `[0]`), Class label as `Value`
      doAssert subDf["Class", string] == expDf[idx]["Class", string]
      doAssert subDf["Num", int] == expDf[idx]["Num", int]
      inc idx

  doAssert df.kind == dfGrouped
  # sort by keys
  let keys = getKeys(df.groupMap)
  # arrange by all keys in ascending order
  let dfArranged = df.arrange(keys, order = order)
  # having the data frame in a sorted order, walk it and return each combination
  let hashes = dfArranged.selectTensors(keys)

  proc buildClassLabel(df: DataFrame, keys: seq[string],
                       idx: int): seq[(string, Value)] =
    result = newSeq[(string, Value)](keys.len)
    for j, key in keys:
      result[j] = (key, df[key][idx, Value])

  var
    currentHash = hashes.row(0) # [0]
    lastHash = hashes.row(0) # [0]
    startIdx, stopIdx: int # indices which indicate from where to where a subgroup is located
  for i in 0 ..< dfArranged.len:
    currentHash.assignRow(hashes, i) # [i]
    if currentHash == lastHash:
      # continue accumulating
      discard
    elif i > 0:
      # found the end of a subgroup or we're at the end of the DataFrame
      stopIdx = i - 1
      # return subgroup of startIdx .. stopIdx
      # build class label seq
      yield (buildClassLabel(dfArranged, keys, stopIdx), dfArranged[startIdx .. stopIdx])
      # set new start and stop idx
      startIdx = i
      lastHash = currentHash
    else:
      # should only happen for i == 0
      doAssert i == 0
      lastHash = currentHash
  # finally yield the last subgroup or the whole group, in case we only
  # have a single key
  yield (buildClassLabel(dfArranged, keys, dfArranged.high), dfArranged[startIdx .. dfArranged.high])

proc filterImpl[T; U: seq[int] | Tensor[int]](resCol: var Column, col: Column, filterIdx: U) =
  ## Fills the input column `resCol` with the elements of `col` filtered
  ## to the indices `filterIdx`.
  let t = toTensor(col, T)
  var res = newTensorUninit[T](filterIdx.len)
  if filterIdx.len > 0:
    var i = 0
    for idx in 0 ..< filterIdx.len:
      res[i] = t[filterIdx[idx]]
      inc i
  resCol = res.toColumn

proc filter[T: seq[int] | Tensor[int]](col: Column, filterIdx: T): Column =
  ## perform filterting of the given column `key`
  if col.kind == colConstant: # just return a "shortened" constant tensor
    result = col
    result.len = filterIdx.len
  else:
    withNativeDtype(col):
      filterImpl[dtype, T](result, col, filterIdx)

proc countTrue(t: Tensor[bool]): int {.inline.} =
  for el in t:
    if el:
      inc result

proc filteredIdx(t: Tensor[bool]): Tensor[int] {.inline, noinit.} =
  let numNonZero = countTrue(t)
  result = newTensorUninit[int](numNonZero)
  var idx = 0
  var j = 0
  for cond in t:
    if cond:
      result[idx] = j
      inc idx
    inc j

proc applyFilterFormula(df: DataFrame, fn: FormulaNode): Column =
  case fn.kind
  of fkVector:
    if fn.resType != colBool:
      raise newException(FormulaMismatchError, "Input mapping formula " & $fn.name & " does not " &
        "return boolean values, but " & $fn.resType & ". Only boolean mapping formulae " &
        "are supported in `filter`.")
    result = fn.fnV(df)
  of fkScalar:
    if fn.valKind != VBool:
      raise newException(FormulaMismatchError, "Input reducing formula " & $fn.name & " does not " &
        "return boolean value, but " & $fn.valKind & ". Only boolean reducing formulae " &
        "are supported in `filter`.")
    let scaleVal = fn.fnS(df)
    result = constantColumn(scaleVal.toBool, df.len)
  else:
    raise newException(FormulaMismatchError, "Given formula " & $fn.name & " is of unsupported kind " &
      $fn.kind & ". Only reducing `<<` and mapping `~` formulas are supported in `filter`.")

proc filterToIdx*[T: seq[int] | Tensor[int]](df: DataFrame, indices: T,
                                             keys: seq[string] = @[]): DataFrame =
  ## Filters the input dataframe to all rows matching the indices of `idx`.
  ##
  ## If the `keys` argument is empty, all columns are filtered.
  ##
  ## WARNING: If `keys` is given and only represents a subset of the DF,
  ## the resulting DataFrame will be ragged and the unfiltered columns
  ## are "invisible". The dataframe then technically is invalid. Use
  ## at your own risk!
  ##
  ## Mostly used internally, but very useful in certain contexts.
  var keys = keys
  if keys.len == 0:
    keys = df.getKeys()
  result = df.shallowCopy()
  for k in keys:
    result.asgn(k, df[k].filter(indices))
    # fill each key with the non zero elements
  result.len = indices.len

proc filterImpl(df: DataFrame, conds: varargs[FormulaNode]): DataFrame =
  ## Implements filtering of mapping and scalar formulas on a `DataFrame`.
  ## Does not differentiate between grouped and ungrouped inputs (done in
  ## exported `filter` below).
  result = newDataFrame(df.ncols)
  var fullCondition: FormulaNode
  var filterIdx = newColumn(colBool)
  for c in conds:
    if filterIdx.kind == colBool and filterIdx.len > 0:
      # combine two tensors
      let newIdx = df.applyFilterFormula(c)
      if newIdx.kind == colConstant and newIdx.cCol == %~ false:
        return newDataFrame()
      elif newIdx.kind == colConstant:
        # reducing formula evaluated true, do not have to combine anything
        continue
      else:
        # combine existing indices and new indices
        filterIdx.bCol.apply2_inline(newIdx.bCol):
          # calculate logic and
          x and y
    else:
      # eval boolean scalar function on DF. Predicate decides to keep or drop full frame
      filterIdx = df.applyFilterFormula(c)
      if filterIdx.kind == colConstant and filterIdx.cCol == %~ false:
        return newDataFrame()

  case filterIdx.kind
  of colBool:
    let nonZeroIdx = filteredIdx(filterIdx.bCol)
    result = df.filterToIdx(nonZeroIdx)
  of colConstant:
    # assert value is true (scalar formula yielding true)
    doAssert filterIdx.cCol == %~ true, "Constant column needs to be true"
    result = df
  else: doAssert false, "Invalid branch"

proc filter*(df: DataFrame, conds: varargs[FormulaNode]): DataFrame =
  ## Returns the data frame filtered by the conditions given. Multiple conditions are
  ## evaluated successively and all only elements matching all conditions as true will
  ## remain. If the input data frame is grouped, the subgroups are evaluated individually.
  ##
  ## Both mapping and reducing formulas are supported, but each formula kind must return
  ## a boolean value. In a case of a mismatch `FormulaMismatchError` is thrown.
  runnableExamples:
    let df = seqsToDf({ "x" : @[1, 2, 3, 4, 5], "y" : @["a", "b", "c", "d", "e"] })
    let dfRes = df.filter(f{ `x` < 3 or `y` == "e" }) ## arbitrary boolean expressions supported
    doAssert dfRes["x", int] == [1, 2, 5].toTensor
    doAssert dfRes["y", string] == ["a", "b", "e"].toTensor
  let df = df.shallowCopy # make a shallow copy, as otherwise we might modify the input
  case df.kind
  of dfGrouped:
    var dfs = newSeq[DataFrame]()
    var i = 0
    for (tup, subDf) in groups(df):
      var mdf = subDf.filterImpl(conds)
      for (str, val) in tup:
        mdf[str] = constantColumn(val, mdf.len)
      dfs.add mdf
      inc i
    result = assignStack(dfs)
  else:
    result = df.filterImpl(conds)

proc calcNewColumn*(df: DataFrame, fn: FormulaNode): (string, Column) =
  ## Calculates a new column based on the `fn` given. Returns the name of the resulting
  ## column (derived from the formula) as well as the column.
  ##
  ## This is not indented for the user facing API. It is used internally in `ggplotnim`.
  result = (fn.colName, fn.fnV(df))

proc calcNewConstColumnFromScalar*(df: DataFrame, fn: FormulaNode): (string, Column) =
  ## Calculates a new constant column based on the scalar (reducing) `fn` given.
  ## Returns the name of the resulting column (derived from the formula) as well as the column.
  ##
  ## This is not indented for the user facing API. It is used internally in `ggplotnim`.
  assert fn.kind == fkScalar
  result = (fn.valName, constantColumn(fn.fnS(df), df.len))

proc selectInplace*[T: string | FormulaNode](df: var DataFrame, cols: varargs[T]) =
  ## Inplace variant of `select` below.
  var toDrop = toHashSet(df.getKeys)
  for fn in cols:
    when type(T) is string:
      toDrop.excl fn
    else:
      case fn.kind
      of fkVariable: toDrop.excl fn.val.toStr
      of fkAssign:
        df.asgn(fn.lhs, df[fn.rhs])
        toDrop.excl fn.lhs
      else:
        raise newException(FormulaMismatchError, "Formula `" & $fn & "` of kind `" & $fn.kind & "` not allowed " &
          "for selection.")
  # bind `items` for `HashSet` here to make it work in a module that does not import `sets`
  bind items
  # now drop all required keys
  for key in items(toDrop): df.drop(key)

proc select*[T: string | FormulaNode](df: DataFrame, cols: varargs[T]): DataFrame =
  ## Returns the data frame cut to the names given as `cols`. The argument
  ## may either be the name of a column as a string, or a `FormulaNode`.
  ##
  ## If the input is a formula node the left hand side (left of `<-`, `~`, `<<`) if it
  ## exists or the name of the formula is computed from the formula. In the simplest
  ## case it may just be a `fkVariable: f{"myColumn"}` formula.
  ##
  ## The `FormulaNode` approach is mainly useful to select and rename a column at
  ## the same time using an assignment formula `<-`.
  ##
  ## Note: string and formula node arguments ``cannot`` be mixed. If a rename is
  ## desired, all other arguments need to be given as `fkVariable` formulas.
  runnableExamples:
    let df = seqsToDf({"Foo" : [1,2,3], "Bar" : [5,6,7], "Baz" : [1.2, 2.3, 3.4]})
    block:
      let dfRes = df.select(["Foo", "Bar"])
      doAssert dfRes.ncols == 2
      doAssert "Foo" in dfRes
      doAssert "Bar" in dfRes
      doAssert "Baz" notin dfRes
    block:
      let dfRes = df.select([f{"Foo"}, f{"New" <- "Bar"}])
      doAssert dfRes.ncols == 2
      doAssert "Foo" in dfRes
      doAssert "New" in dfRes
      doAssert "Bar" notin dfRes
      doAssert "Baz" notin dfRes

  result = df.shallowCopy()
  result.selectInplace(cols)

proc mutateImpl(df: var DataFrame, fns: varargs[FormulaNode],
                dropCols: static bool) =
  ## implementation of mutation / transmutation. Allows to statically
  ## decide whether to only keep touched columns or not.
  var colsToKeep: seq[string]
  for fn in fns:
    case fn.kind
    of fkVariable:
      if fn.isColumn(df):
        colsToKeep.add fn.val.toStr
      else:
        # create column of value
        df.asgn($fn.val, constantColumn(fn.val, df.len))
        colsToKeep.add $fn.val
    of fkAssign:
      # essentially a rename
      df.asgn(fn.lhs, df[fn.rhs.toStr])
      # colToKeep only relevant for `transmute`, where we only want to keep
      # the LHS
      colsToKeep.add fn.lhs
    of fkVector:
      let (colName, newCol) = df.calcNewColumn(fn)
      df.asgn(colName, newCol)
      colsToKeep.add colName
    of fkScalar:
      let (colName, newCol) = df.calcNewConstColumnFromScalar(fn)
      df.asgn(colName, newCol)
      colsToKeep.add colName
    of fkNone:
      raise newException(FormulaMismatchError, "Formula `" & $fn & "` of kind `fkNone` not allowed " &
        "for mutation.")
  when dropCols:
    df.selectInplace(colsToKeep)

proc mutateInplace*(df: var DataFrame, fns: varargs[FormulaNode]) =
  ## Inplace variasnt of `mutate` below.
  case df.kind
  of dfGrouped:
    var dfs = newSeq[DataFrame]()
    var i = 0
    for (tup, subDf) in groups(df):
      var mdf = subDf
      mdf.mutateImpl(fns, dropCols = false)
      dfs.add mdf
      inc i
    df = assignStack(dfs)
  else:
    df.mutateImpl(fns, dropCols = false)

proc mutate*(df: DataFrame, fns: varargs[FormulaNode]): DataFrame =
  ## Returns the data frame with additional mutated columns, described
  ## by the functions `fns`.
  ##
  ## Each formula `fn` given will be used to create a new column in the
  ## data frame.
  ##
  ## Existing columns may also be overwritten by handing a formula with
  ## the name of an existing column as the resulting name.
  ##
  ## The left hand side of the given formula will correspond to the new
  ## name of the column if present. If not, the name will be computed from
  ## a lisp representation of the formula code.
  runnableExamples:
    let df = seqsToDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12], "z": ["5","6","7"] })
    block:
      let dfRes = df.mutate(f{"x+y" ~ `x` + `y`})
      doAssert dfRes.ncols == 4
      doAssert "x+y" in dfRes
      doAssert dfRes["x+y", int] == [11,13,15].toTensor
    block:
      # of course local variables can be referenced:
      let foo = 5
      let dfRes = df.mutate(f{"x+foo" ~ `x` + foo})
      doAssert "x+foo" in dfRes
      doAssert dfRes["x+foo", int] == [6,7,8].toTensor
    import strutils
    block:
      # they can change type and infer it
      let foo = 5
      let dfRes = df.mutate(f{"asInt" ~ parseInt(`z`)})
      doAssert "asInt" in dfRes
      doAssert dfRes["asInt", int] == [5,6,7].toTensor
    block:
      # and if no name is given:
      let dfRes = df.mutate(f{`x` + `y`})
      doAssert "(+ x y)" in dfRes
      doAssert dfRes["(+ x y)", int] == [11,13,15].toTensor

  result = df.shallowCopy()
  result.mutateInplace(fns)

proc transmuteInplace*(df: var DataFrame, fns: varargs[FormulaNode]) =
  ## Inplace variant of `transmute` below.
  case df.kind
  of dfGrouped:
    var dfs = newSeq[DataFrame]()
    var i = 0
    for (tup, subDf) in groups(df):
      var mdf = subDf
      mdf.mutateImpl(fns, dropCols = true)
      dfs.add mdf
      inc i
    df = assignStack(dfs)
  else:
    df.mutateImpl(fns, dropCols = true)

proc transmute*(df: DataFrame, fns: varargs[FormulaNode]): DataFrame =
  ## Returns the data frame cut to the columns created by `fns`, which
  ## should involve a calculation. To only cut to one or more columns
  ## use the `select` proc.
  ##
  ## It is equivalent to calling `mutate` and then `select` the columns
  ## created (or modified) during the `mutate` call.
  ##
  ## Existing columns may also be overwritten by handing a formula with
  ## the name of an existing column as the resulting name.
  ##
  ## The left hand side of the given formula will correspond to the new
  ## name of the column if present. If not, the name will be computed from
  ## a lisp representation of the formula code.
  runnableExamples:
    let df = seqsToDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12], "z": ["5","6","7"] })
    let dfRes = df.transmute(f{"x+y" ~ `x` + `y`})
    doAssert "x+y" in dfRes
    doAssert dfRes.ncols == 1
    doAssert dfRes["x+y", int] == [11,13,15].toTensor
    doAssert "y" notin dfRes
    doAssert "z" notin dfRes

  result = df.shallowCopy()
  result.transmuteInplace(fns)

proc rename*(df: DataFrame, cols: varargs[FormulaNode]): DataFrame =
  ## Returns the data frame with the columns described by `cols` renamed to
  ## the names on the LHS of the given `FormulaNode`. All other columns will
  ## be left untouched.
  ##
  ## The given formulas must be of assignment type, i.e. use `<-`.
  ##
  ## Note: the renamed columns will be moved to the right side of the data frame,
  ## so the column order will be changed.
  runnableExamples:
    let df = seqsToDf({ "x" : @[1, 2, 3], "y" : @[10, 11, 12] })
    let dfRes = df.rename(f{"foo" <- "x"})
    doAssert dfRes.ncols == 2
    doAssert "x" notin dfRes
    doAssert "foo" in dfRes
    doAssert "y" in dfRes

  result = df
  for fn in cols:
    doAssert fn.kind == fkAssign
    result[fn.lhs] = df[fn.rhs.toStr]
    # remove the column of the old name
    result.drop(fn.rhs.toStr)

proc arrangeSortImpl[T](toSort: var seq[(int, T)], order: SortOrder) =
  ## sorts the given `(index, Value)` pair according to the `Value`
  toSort.sort(
      cmp = (
        proc(x, y: (int, T)): int =
          result = system.cmp(x[1], y[1])
      ),
      order = order
    )

proc sortBySubset(df: DataFrame, by: string, idx: seq[int], order: SortOrder): seq[int] =
  let col = df[by]
  if col.kind == colConstant: # nothing to sort
    result = idx
  else:
    withNativeDtype(col):
      var res = newSeq[(int, dtype)](idx.len)
      let t = toTensor(col, dtype)
      for i, val in idx:
        res[i] = (val, t[val])
      res.arrangeSortImpl(order = order)
      # after sorting here, check duplicate values of `val`, slice
      # of those duplicates, use the next `by` in line and sort
      # the remaining indices. Recursively do this until
      result = res.mapIt(it[0])

proc sortRecurse(df: DataFrame, by: seq[string],
                 startIdx: int,
                 resIdx: seq[int],
                 order: SortOrder): seq[int]

proc sortRecurseImpl[T](result: var seq[int], df: DataFrame, by: seq[string],
                        startIdx: int,
                        resIdx: seq[int],
                        order: SortOrder) =
  var res = newSeq[(int, T)](result.len)
  let t = toTensor(df[by[0]], T)
  for i, val in result:
    res[i] = (val, t[val])

  ## The logic in the following is a bit easy to misunderstand. Here we are
  ## sorting the current key `by[0]` (its data is in `res`) by any additional
  ## keys `by[1 .. ^1]`. It is important to keep in mind that `res` (key `by[0]`)
  ## is already sorted in the proc calling `sortRecurse`.
  ## Then we walk over the sorted data and any time a value of `res` changes,
  ## we have to look at that whole slice and sort it by the second key `by[1]`.
  ## Thus, the while loop below checks for:
  ## - `last != cur`: val changed at index i, need to sort, iff the last search
  ##   was ``not`` done at index `i - 1` (that happens immediately the iteration
  ##   after sorting a slice -> `i > lastSearch + 1`.
  ## - `i == df.high`: In the case of the last element we do ``not`` require
  ##   the value to change, ``but`` here we have to sort not the slice until
  ##   `i - 1` (val changed at current `i`, only want to sort same slice!),
  ##   but until `df.high` -> let topIdx = …
  ## Finally, if there are more keys in `by`, sort the subset itself as subsets.
  let mby = by[1 .. ^1]
  var
    last = res[0][1]
    cur = res[1][1]
    i = startIdx
    lastSearch = 0
  while i < res.len:
    cur = res[i][1]
    if last != cur or i == df.high:
      if i > lastSearch + 1:
        # sort between `lastSearch` and `i`.
        let topIdx = if i == df.high: i else: i - 1
        var subset = sortBySubset(df, mby[0],
                                  res[lastSearch .. topIdx].mapIt(it[0]),
                                  order = order)
        if mby.len > 1:
          # recurse again
          subset = sortRecurse(df, mby, lastSearch,
                               resIdx = subset,
                               order = order)
        result[lastSearch .. topIdx] = subset
      lastSearch = i
    last = res[i][1]
    inc i

proc sortRecurse(df: DataFrame, by: seq[string],
                 startIdx: int,
                 resIdx: seq[int],
                 order: SortOrder): seq[int] =
  result = resIdx
  withNativeDtype(df[by[0]]):
    sortRecurseImpl[dtype](result, df, by, startIdx, resIdx, order)

proc sortBys(df: DataFrame, by: seq[string], order: SortOrder): seq[int] =
  withNativeDtype(df[by[0]]):
    var res = newSeq[(int, dtype)](df.len)
    var idx = 0
    let t = toTensor(df[by[0]], dtype)
    for i in 0 ..< t.size:
      let val = t[i]
      res[idx] = (idx, val)
      inc idx
    res.arrangeSortImpl(order = order)
    # after sorting here, check duplicate values of `val`, slice
    # of those
    # duplicates, use the next `by` in line and sort
    # the remaining indices. Recursively do this until
    var resIdx = res.mapIt(it[0])
    if res.len > 1 and by.len > 1:
      resIdx = sortRecurse(df, by, startIdx = 1, resIdx = resIdx, order = order)
    result = resIdx

proc arrange*(df: DataFrame, by: varargs[string], order = SortOrder.Ascending): DataFrame =
  ## Sorts the data frame in ascending / descending `order` by key `by`.
  ##
  ## The sort order is handled as in Nim's standard library using the `SortOrder` enum.
  ##
  ## If multiple keys are given to order by, the priority is determined by the order
  ## in which they are given. We first order by `by[0]`. If there is a tie, we try
  ## to break it by `by[1]` and so on.
  ##
  ## Do ``not`` depend on the order within a tie, if no further ordering is given!
  runnableExamples:
    let df = seqsToDf({ "x" : @[5, 2, 3, 2], "y" : @[4, 3, 2, 1]})
    block:
      let dfRes = df.arrange("x")
      doAssert dfRes["x", int] == [2, 2, 3, 5].toTensor
      doAssert dfRes["y", int][0] == 3
      doAssert dfRes["y", int][3] == 4
    block:
      let dfRes = df.arrange("x", order = SortOrder.Descending)
      doAssert dfRes["x", int] == [5, 3, 2, 2].toTensor
      doAssert dfRes["y", int][0] == 4
      doAssert dfRes["y", int][1] == 2
    block:
      let dfRes = df.arrange(["x", "y"])
      doAssert dfRes["x", int] == [2, 2, 3, 5].toTensor
      doAssert dfRes["y", int] == [1, 3, 2, 4].toTensor

  # now sort by cols in ascending order of each col, i.e. ties will be broken
  # in ascending order of the columns
  result = newDataFrame(df.ncols)
  # remove all constant columns from `by` (nothing to sort there)
  let by = @by.filterIt(df[it].kind != colConstant)
  let idxCol = sortBys(df, by, order = order)
  result.len = df.len
  var data = newColumn()
  for k in keys(df):
    withNativeDtype(df[k]):
      let col = df[k].toTensor(dtype)
      var res = newTensor[dtype](df.len)
      for i in 0 ..< df.len:
        res[i] = col[idxCol[i]]
      data = toColumn res
    result.asgn(k, data)

proc assign(df: var DataFrame, key: string, idx1: int, c2: Column, idx2: int) =
  ## Assigns the value in `df` in col `key` at index `idx1` to the value of
  ## index `idx2` of column `c2`
  ##
  ## This is not meant as a user facing proc and is used internally.
  withNativeDtype(df[key]):
    df[key, idx1] = c2[idx2, dtype]

proc innerJoin*(df1, df2: DataFrame, by: string): DataFrame =
  ## Returns a data frame joined by the given key `by` in such a way as to only keep
  ## rows found in both data frames.
  ##
  ## This is useful to combine two data frames that share a single column. It "zips"
  ## them together according to the column `by`.
  runnableExamples:
    let df1 = seqsToDf({ "Class" : @["A", "B", "C", "D", "E"],
                         "Num" : @[1, 5, 3, 4, 6] })
    let df2 = seqsToDf({ "Class" : ["E", "B", "A", "D", "C"],
                         "Ids" : @[123, 124, 125, 126, 127] })
    let dfRes = innerJoin(df1, df2, by = "Class")
    doAssert dfRes.ncols == 3
    doAssert dfRes["Class", string] == ["A", "B", "C", "D", "E"].toTensor
    doAssert dfRes["Num", int] == [1, 5, 3, 4, 6].toTensor
    doAssert dfRes["Ids", int] == [125, 124, 127, 126, 123].toTensor

  # build sets from both columns and seqs of their corresponding indices
  let
    df1S = df1.arrange(by)
    df2S = df2.arrange(by)
  withNativeDtype(df1S[by]): ## TODO: this likely means we convert constants to `Value`...
    let
      col1 = df1S[by].toTensor(dtype).toRawSeq
      col2 = df2S[by].toTensor(dtype).toRawSeq
    let colSet1 = col1.toHashSet
    let colSet2 = col2.toHashSet
    let intersection = colSet1 * colSet2
    let idxDf1 = toSeq(0 ..< col1.len).filterIt(col1[it] in intersection)
    let idxDf2 = toSeq(0 ..< col2.len).filterIt(col2[it] in intersection)

    var
      i = 0
      j = 0
    let
      # for some reason we can't do toSeq(keys(df1S)) anymore...
      # This is due to https://github.com/nim-lang/Nim/issues/7322. `toSeq` isn't exported for now.
      keys1 = getKeys(df1S).toHashSet
      keys2 = getKeys(df2S).toHashSet
      allKeys = keys1 + keys2
      commonKeys = keys1 * keys2
      restKeys = allKeys - commonKeys
    result = newDataFrame(allKeys.card)
    let resLen = (max(df1S.len, df2S.len))
    for k in allKeys:
      if k in df1S and k in df2S:
        doAssert compatibleColumns(df1S[k], df2S[k]), " Key: " & $k & ", df1: " & $df1S[k].kind & ", df2: " & $df2S[k].kind
        result.asgn(k, newColumn(kind = combinedColKind(@[df1S[k], df2S[k]]),
                                 length = resLen))
      elif k in df1S and k notin df2S:
        result.asgn(k, newColumn(kind = df1S[k].kind, length = resLen))
      if k notin df1S and k in df2S:
        result.asgn(k, newColumn(kind = df2S[k].kind, length = resLen))
    var count = 0

    let df1By = df1S[by].toTensor(dtype)
    let df2By = df2S[by].toTensor(dtype)
    while i < idxDf1.len and
          j < idxDf2.len:
      let il = idxDf1[i]
      let jl = idxDf2[j]
      # indices point to same row, merge row
      if df1By[il] == df2By[jl]:
        for k in commonKeys:
          if not equal(df1S[k], il, df2S[k], jl):
            # skip this element
            break
          result.assign(k, count, df1S[k], il)
        for k in restKeys:
          if k in keys1:
            result.assign(k, count, df1S[k], il)
          elif k in keys2:
            result.assign(k, count, df2S[k], jl)
        inc count
      # now increase the indices as required
      if i != idxDf1.high and
         j != idxDf2.high and
         (df1By[idxDf1[i+1]] == df2By[idxDf2[j+1]]):
        inc i
        inc j
      elif i != idxDf1.high and (df1By[idxDf1[i+1]] == df2By[jl]):
        inc i
      elif j != idxDf2.high and (df1By[il] == df2By[idxDf2[j+1]]):
        inc j
      elif i == idxDf1.high and j == idxDf2.high:
        break
      else:
        raise newException(Exception, "This should not happen")
    result.len = count
    # possibly shorten the columns
    if result.len < resLen:
      for k in getKeys(result):
        if result[k].kind != colConstant: # if constant nothing to short
          withNativeTensor(result[k], t):
            result.asgn(k, toColumn(t[_ ..< result.len]))
        result[k].len = result.len

proc toHashSet*[T](t: Tensor[T]): HashSet[T] =
  ## Internal helper to convert a tensor to a `HashSet`
  for el in t:
    result.incl el

proc group_by*(df: DataFrame, by: varargs[string], add = false): DataFrame =
  ## Returns a grouped data frame grouped by all unique keys in `by`.
  ##
  ## Grouping a data frame is an ``almost`` lazy affair. It only calculates the groups
  ## and its classes. Otherwise the data frame remains unchanged.
  ##
  ## If `df` is already a grouped data frame and `add` is `true`, the groups given
  ## by `by` will be added as additional groups.
  ##
  ## It is meant to be used with any of the normal procedurs like `filter`, `summarize`,
  ## `mutate` in which case the action will be performed group wise.
  doAssert by.len > 0, "Need at least one argument to group by!"
  if df.kind == dfGrouped and add:
    # just copy `df`
    result = df.shallowCopy()
  else:
    # copy over the data frame into new one of kind `dfGrouped` (cannot change
    # kind at runtime!)
    result = newDataFrame(df.ncols, kind = dfGrouped)
    result.data = df.data
    result.len = df.len
  for key in by:
    result.groupMap[key] = toHashSet(result[key].toTensor(Value))

proc summarize*(df: DataFrame, fns: varargs[FormulaNode]): DataFrame =
  ## Returns a data frame with the summaries applied given by `fn`. They are applied
  ## in the order in which they are given.
  ##
  ## `summarize` is a reducing operation. The given formulas need to take full columns
  ## as arguments and produce scalars, using the `<<` operator. If no left hand side
  ## and operator is given, the new column will be computed automatically.
  runnableExamples:
    let df = seqsToDf({ "x" : @[1, 2, 3, 4, 5], "y" : @[5, 10, 15, 20, 25] })
    block:
      let dfRes = df.summarize(f{float:  mean(`x`) }) ## compute mean, auto creates a column name
      doAssert dfRes.len == 1 # reduced to 1 row
      doAssert "(mean x)" in dfRes
    block:
      let dfRes = df.summarize(f{float: "mean(x)" << mean(`x`) }) ## same but with a custom name
      doAssert dfRes.len == 1 # reduced to 1 row
      doAssert "mean(x)" in dfRes
    block:
      let dfRes = df.summarize(f{"mean(x)+sum(y)" << mean(`x`) + sum(`y`) })
      doAssert dfRes.len == 1
      doAssert "mean(x)+sum(y)" in dfRes

  result = newDataFrame(kind = dfNormal)
  var lhsName = ""
  case df.kind
  of dfNormal:
    for fn in fns:
      doAssert fn.kind == fkScalar
      lhsName = fn.valName
      # just apply the function
      withNativeConversion(fn.valKind, get):
        let res = toColumn get(fn.fnS(df))
        result.asgn(lhsName, res)
        result.len = res.len
  of dfGrouped:
    # since `df.len >> fns.len = result.len` the overhead of storing the result
    # in a `Value` first does not matter in practice
    var sumStats = initOrderedTable[string, seq[Value]]()
    var keys = initOrderedTable[string, seq[Value]](df.groupMap.len)
    var idx = 0
    var keyLabelsAdded = false
    for fn in fns:
      doAssert fn.kind == fkScalar
      lhsName = fn.valName
      sumStats[lhsName] = newSeqOfCap[Value](1000) # just start with decent size
      for class, subdf in groups(df):
        if not keyLabelsAdded:
          # keys and labels only have to be added for a single `fn`, since the DF
          # will yield the same subgroups anyways!
          # TODO: we're gonna replace this anyways, but we shouldn't iterate over groups
          # several times for several functions!
          for (key, label) in class:
            if key notin keys: keys[key] = newSeqOfCap[Value](1000)
            keys[key].add label
        sumStats[lhsName].add fn.fnS(subDf)
      # done w/ one subgroup, don't add more keys / labels
      keyLabelsAdded = true
    for k, vals in keys:
      result.asgn(k, toNativeColumn vals)
    for k, vals in sumStats:
      result.asgn(k, toNativeColumn vals)
      result.len = vals.len

proc count*(df: DataFrame, col: string, name = "n"): DataFrame =
  ## Counts the number of elements per type in `col` of the data frame.
  ##
  ## The counts are stored in a new column given by `name`.
  ##
  ## It is essentially a shorthand version of first grouping the data frame
  ## by column `col` and then applying a reducing `summarize` call that
  ## returns the length of each sub group.
  runnableExamples:
    let df = seqsToDf({"Class" : @["A", "C", "B", "B", "A", "C", "C"]})
    let dfRes = df.count("Class")
    doAssert dfRes.len == 3 # one row per class
    doAssert dfRes["n", int] == [2, 2, 3].toTensor

  # TODO: handle already grouped dataframes.
  result = DataFrame()
  let grouped = df.group_by(col, add = true)
  var counts = newSeqOfCap[int](1000) # just start with decent size
  var keys = initOrderedTable[string, seq[Value]](grouped.groupMap.len)
  var idx = 0
  for class, subdf in groups(grouped):
    for (c, val) in class:
      if c notin keys: keys[c] = newSeqOfCap[Value](1000)
      keys[c].add val
    counts.add subDf.len
    inc idx
  for k, vals in keys:
    result.asgn(k, toNativeColumn vals)
  result.asgn(name, toColumn counts)
  result.len = idx

proc setDiff*(df1, df2: DataFrame, symmetric = false): DataFrame =
  ## Returns a `DataFrame` with all elements in `df1` that are ``not`` found in
  ## `df2`.
  ##
  ## This comparison is perforrmed ``row`` wise.
  ##
  ## If `symmetric` is true, the symmetric difference of the dataset is
  ## returned instead, i.e. elements which are either not in `df1` ``or`` not in `df2`.
  result = newDataFrame(df1.ncols)
  #[
  Calculate custom hash for each row in each table.
  Keep var h1, h2 = seq[Hashes] where seq[Hashes] is hash of of row.
  Calculate hashes by column! Get df1 column 1, start hash, column 2, add to hash etc.
  Same for df2.
  Compare hashes either symmetric, or asymmetric.
  Use indices of allowed hashes to rebuild final DF via columns again. Should be fast
  ]#
  if getKeys(df1) != getKeys(df2):
    # if not all keys same, all rows different by definition!
    return df1

  let keys = getKeys(df1)
  let h1 = buildColHashes(df1, keys)
  let h2 = buildColHashes(df2, keys)
  # given hashes apply set difference
  var diff: HashSet[seq[Value]]
  if symmetric:
    diff = symmetricDifference(toHashSet(h1), toHashSet(h2))
    var idxToKeep1 = newSeqOfCap[int](diff.card)
    var idxToKeep2 = newSeqOfCap[int](diff.card)
    for idx, h in h1:
      if h in diff:
        # keep this row
        idxToKeep1.add idx
    for idx, h in h2:
      if h in diff:
        # keep this row
        idxToKeep2.add idx
    # rebuild those from df1, then those from idx2
    result = df1.filterToIdx(idxToKeep1, keys)
    var df2Res = newDataFrame()
    df2Res = df2.filterToIdx(idxToKeep2, keys)
    # stack the two data frames
    result.add df2Res
  else:
    diff = toHashSet(h1) - toHashSet(h2)
    # easy
    var idxToKeep = newTensor[int](diff.card)
    var i = 0
    for idx, h in h1:
      if h in diff:
        # keep this row
        idxToKeep[i] = idx
        inc i
    # rebuild the idxToKeep columns
    result = df1.filterToIdx(idxToKeep, keys)

proc head*(df: DataFrame, num: int): DataFrame =
  ## Returns the head of the DataFrame, i.e. the first `num` elements.
  result = df[0 ..< num]

proc tail*(df: DataFrame, num: int): DataFrame =
  ## Returns the tail of the DataFrame, i.e. the last `num` elements.
  result = df[^num .. df.high]

proc gather*(df: DataFrame, cols: varargs[string],
             key = "key", value = "value", dropNulls = false): DataFrame =
  ## Gathers the `cols` from `df` and merges these columns into two new columns,
  ## where the `key` column contains the name of the column from which the `value`
  ## entry is taken. I.e. transforms `cols` from wide to long format.
  ##
  ## A different way to think about the operation is that all columns to be gathered
  ## belong to one class. They are simply different labels in that class. `gather` is
  ## used to collect all labels in the class and produces a new data frame, in which
  ## we have a column for the class labels (`key`) and their values as they appeared
  ## in each label's column before (`value`).
  ##
  ## The inverse operation is `spread`.
  runnableExamples:
    let df = seqsToDf({"A" : [1, 8, 0], "B" : [3, 4, 0], "C" : [5, 7, 2]})
    let dfRes = df.gather(df.getKeys(), ## get all keys to gather
                          key = "Class", ## the name of the `key` column
                          value = "Num")
    doAssert "Class" in dfRes
    doAssert "Num" in dfRes
    doAssert dfRes.ncols == 2
    doAssert dfRes["Class", string] == ["A", "A", "A", "B", "B", "B", "C", "C", "C"].toTensor
    doAssert dfRes["Num", int] == [1, 8, 0, 3, 4, 0, 5, 7, 2].toTensor

  result = newDataFrame(df.ncols)
  let remainCols = getKeys(df).toHashSet.difference(cols.toHashSet)
  let newLen = cols.len * df.len
  # assert all columns same type
  # TODO: relax this restriction, auto convert to `colObject` if non matching
  var keyTensor = newTensorUninit[string](newLen)
  withCombinedType(df, @cols):
    var valTensor = newTensorUninit[dtype](newLen)
    for i in 0 ..< cols.len:
      # for each column, clone the `col` tensor once to the correct position
      let col = cols[i]
      keyTensor[i * df.len ..< (i + 1) * df.len] = col #.clone()
      # TODO: make sure we don't have to clone the given tensor!
      valTensor[i * df.len ..< (i + 1) * df.len] = df[col].toTensor(dtype)
    # now create result
    result.asgn(key, toColumn keyTensor)
    result.asgn(value, toColumn valTensor)
  # For remainder of columns, just use something like `repeat`!, `stack`, `concat`
  for rem in remainCols:
    withNativeDtype(df[rem]): ## XXX: this might convert to colObject?
      let col = df[rem].toTensor(dtype)
      var fullCol = newTensorUninit[dtype](newLen)
      for i in 0 ..< cols.len:
        # for each column, clone the `col` tensor once to the correct position
        fullCol[i * df.len ..< (i + 1) * df.len] = col #.clone()
      result[rem] = toColumn(fullCol)
  result.len = newLen

proc spread*[T](df: DataFrame, namesFrom, valuesFrom: string,
                valuesFill: T = 0): DataFrame =
  ## The inverse operation to `gather`. A conversion from long format to
  ## a wide format data frame.
  ##
  ## The name is `spread`, but the API is trying to be more closely aligned
  ## to dplyr's newer `pivot_wider`.
  ##
  ## Note: if the only two columns present are `namesFrom` and `valuesFrom` and
  ## one (or more) of labels have more entries, the output will be filled from
  ## row 0 to N (where N is the number of elements in each label).
  ##
  ## Note: currently `valuesFill` does not have an effect. We simply default
  ## initialize the new columns to the native default value of the data stored
  ## in the column.
  runnableExamples:
    block:
      let df = seqsToDf({ "Class" : ["A", "A", "A", "B", "B", "B", "C", "C", "C"],
                          "Num" : [1, 8, 0, 3, 4, 0, 5, 7, 2] })
      let dfRes = df.spread(namesFrom = "Class",
                            valuesFrom = "Num")
      doAssert dfRes.ncols == 3
      doAssert dfRes["A", int] == [1, 8, 0].toTensor
      doAssert dfRes["B", int] == [3, 4, 0].toTensor
      doAssert dfRes["C", int] == [5, 7, 2].toTensor
    block:
      let df = seqsToDf({ "Class" : ["A", "A", "A", "B", "B", "C", "C", "C", "C"],
                          "Num" : [1, 8, 0, 3, 4, 0, 5, 7, 2] })
      let dfRes = df.spread(namesFrom = "Class",
                            valuesFrom = "Num")
      doAssert dfRes.ncols == 3
      ## in this case all new columns are extended with 0 at the end
      doAssert dfRes["A", int] == [1, 8, 0, 0].toTensor
      doAssert dfRes["B", int] == [3, 4, 0, 0].toTensor
      doAssert dfRes["C", int] == [0, 5, 7, 2].toTensor

  result = newDataFrame()
  # 1. determine new columns from all unique values in `namesFrom`
  let dfGrouped = df.group_by(namesFrom)
  # bind `items` here to make it available in calling scope without `import sets`
  bind items
  let newCols = toSeq(items(dfGrouped.groupMap[namesFrom]))
  # 2. find remaining keys
  let restKeys = df.getKeys().filterIt(it != namesFrom and it != valuesFrom)
  # 3. and length of resulting DF by getting class with most counts
  let dfOutlen = df.count(namesFrom)["n", int].max
  # 4. create result DF from input column types
  for c in restKeys:
    result[c] = newColumn(df[c].kind, dfOutlen)
  for c in newCols:
    result[c.toStr] = newColumn(df[valuesFrom].kind, dfOutlen)
  var idx = 0
  # 5. now group by *other* keys and get the `newCols` from each. That way each subgroup
  #   corresponds to *one row* in the output
  if restKeys.len > 0:
    # 6. for each sub df, walk all rows to get correct key/vals
    # NOTE: this is inefficient
    for (tup, subDf) in groups(df.group_by(restKeys)):
      for row in subDf:
        # NOTE: we could also extract the restKeys info from `tup`
        for col in restKeys:
          withNative(row[col], x):
            result[col, idx] = x
        withNative(row[valuesFrom], x):
          result[row[namesFrom].toStr, idx] = x
      inc idx
  else:
    # if there are no other keys, group by each class and fill the classes separately.
    for (tup, subDf) in groups(df.group_by(namesFrom)):
      idx = 0
      for row in subDf:
        withNative(row[valuesFrom], x):
          result[row[namesFrom].toStr, idx] = x
        inc idx

proc unique*(c: Column): Column =
  ## Returns a `Column` of all unique values in `c` (duplicates are removed).
  runnableExamples:
    let x = toColumn [1, 2, 1, 4, 5]
    doAssert x.unique.toTensor(int) == [1, 2, 4, 5].toTensor
  let cV = c.toTensor(Value)
  var hSet = toHashSet(cV)
  var idxToKeep = newTensor[int](hSet.card)
  var idx = 0
  for i in 0 ..< c.len:
    if cV[i] in hSet:
      idxToKeep[idx] = i
      # remove from set to not get duplicates!
      hSet.excl cV[i]
      inc idx
  # apply idxToKeep as filter
  result = c.filter(idxToKeep)
  result.len = idxToKeep.size

proc unique*(df: DataFrame, cols: varargs[string],
             keepAll = true): DataFrame =
  ## Returns a DF with only distinct rows. If one or more `cols` are given
  ## the uniqueness of a row is only determined based on those columns. By
  ## default all columns are considered.
  ##
  ## If not all columns are considered and `keepAll` is true the resulting
  ## DF contains all other columns. Of those the first duplicated row
  ## is kept!
  ##
  ## Note: The corresponding `dplyr` function is `distinct`. The choice for
  ## `unique` was made, since `distinct` is a keyword in Nim!
  runnableExamples:
    let df = seqsToDf({ "x" : @[1, 2, 2, 2, 4], "y" : @[5.0, 6.0, 7.0, 8.0, 9.0],
                        "z" : @["a", "b", "b", "d", "e"]})
    block:
      let dfRes = df.unique() ## consider uniqueness of all columns, nothing removed
      doAssert dfRes["x", int] == df["x", int]
      doAssert dfRes["y", float] == df["y", float]
      doAssert dfRes["z", string] == df["z", string]
    block:
      let dfRes = df.unique("x") ## only consider `x`, only keeps keeps 1st, 2nd, last row
      doAssert dfRes["x", int] == [1, 2, 4].toTensor
      doAssert dfRes["y", float] == [5.0, 6.0, 9.0].toTensor
      doAssert dfRes["z", string] == ["a", "b", "e"].toTensor
    block:
      let dfRes = df.unique(["x", "z"]) ## considers `x` and `z`, one more unique (4th row)
      doAssert dfRes["x", int] == [1, 2, 2, 4].toTensor
      doAssert dfRes["y", float] == [5.0, 6.0, 8.0, 9.0].toTensor
      doAssert dfRes["z", string] == ["a", "b", "d", "e"].toTensor

  result = newDataFrame(df.ncols)
  var mcols = @cols
  if mcols.len == 0:
    mcols = getKeys(df)
  let hashes = buildColHashes(df, mcols)
  var hSet = toHashSet(hashes)
  # walk df, build indices from `hashes` which differ
  var idxToKeep = newTensor[int](hSet.card)
  var idx = 0
  for i in 0 ..< df.len:
    if hashes[i] in hSet:
      idxToKeep[idx] = i
      # remove from set to not get duplicates!
      hSet.excl hashes[i]
      inc idx
  # apply idxToKeep as filter
  let resCols = if keepAll: getKeys(df) else: mcols
  result = df.filterToIdx(idxToKeep, resCols)

proc drop_null*(df: DataFrame, cols: varargs[string],
                convertColumnKind = false,
                failIfConversionFails: bool = false): DataFrame =
  ## Returns a DF with only those rows left, which contain no null values. Null
  ## values can only appear in `object` columns.
  ##
  ## By default this includes all columns in the data frame. If one or more
  ## `cols` are given, only those columns will be considered.
  ##
  ## By default no attempt is made to convert the new columns to a native
  ## data type, since it introduces another walk over the data. If `convertColumnKind`
  ## is true, conversion is attempted. Whether that throws an assertion error
  ## if the conversion is not possible to a single native type is controlled
  ## by the static `failIfConversionFails`.
  ##
  ## Note: In general this is not a particularly fast proc, since each column
  ## which should drop null values causes a filter of the DF, i.e. a full run over
  ## the lenght of the DF.
  # NOTE: `failIfConversionFails` can't be a static bool right now, because that
  # results in a weird overload resolution bug in the `filter` line below
  # TODO: we could use `column.toTensor` / `column.valueTo` with the `dropNull`
  # argument too. Unify? :/ Which way though?
  var mcols = @cols
  if mcols.len == 0:
    mcols = getKeys(df)
  var colsNeedPruning = newSeq[string]()
  for col in mcols:
    if df[col].kind == colObject: # cols which aren't object cannot contain null
      colsNeedPruning.add col
  # now have to check all those cols for null, advantage: all cols use Value
  # -> can read all
  result = df.shallowCopy()
  for col in colsNeedPruning:
    ## TODO: avoid filtering several times somehow?
    ## can read all cols first and then iterate over them? Not necessarily faster
    let localCol = col # ref: https://github.com/nim-lang/Nim/pull/14447
    result = result.filter(f{Value: isNull(df[localCol][idx]).toBool == false})
    if convertColumnKind:
      if failIfConversionFails: # ugly workaround
        result[col] = result[col].toNativeColumn(failIfImpossible = true)
      else:
        result[col] = result[col].toNativeColumn(failIfImpossible = false)

func evaluate*(node: FormulaNode): Value =
  ## Tries to return a single `Value` from a `FormulaNode`.
  ##
  ## Works either if formula is `fkNone` or `fkVariable`. Returns the stored
  ## value in these cases.
  ##
  ## Raises for `fkVector` and `fkScalar`.
  case node.kind
  of fkVariable: result = node.val
  of fkAssign: result = node.rhs # ?? TODO: should this be allowed?
  of fkScalar: result = %~ node.valName
  of fkVector: result = %~ node.colName
  of fkNone: result = ValueNull

proc evaluate*(node: FormulaNode, df: DataFrame): Column =
  ## Tries to return a `Column` from a `FormulaNode` by evaluating it
  ## on a `DataFrame df`.
  ##
  ## This is usually not extremely useful. It can be handy to understand what a
  ## formula does without having `mutate` and friends interfer.
  # TODO: Handle cases if a value is not a column!
  case node.kind
  of fkVariable:
    if node.isColumn(df):
      result = df[node.val.toStr]
    else:
      # create constant column
      result = constantColumn(node.val, df.len)
  of fkAssign: result = df[node.rhs.toStr]
  of fkVector: result = node.fnV(df)
  of fkScalar: result = constantColumn(node.fnS(df), df.len)
  of fkNone: result = newColumn(colNone, df.len)

proc reduce*(node: FormulaNode, df: DataFrame): Value =
  ## Tries to a single `Value` from a reducing `FormulaNode` by evaluating it
  ## on a `DataFrame df`.
  ##
  ## The argument ``must`` be a reducing formula.
  ##
  ## This is usually not extremely useful. It can be handy to understand what a
  ## formula does without having `mutate` and friends interfer.

  # TODO: Handle cases if a value is not a column!
  case node.kind
  of fkScalar:
    result = node.fnS(df)
  else:
    raise newException(FormulaMismatchError, "Cannot reduce a data frame using a formula " &
      "of kind " & $node.kind & "!")
