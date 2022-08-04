import arraymancer/tensor
import std / [sugar, math, strformat, tables, macros, strutils]
import value

from sequtils import allIt, mapIt

import ast_utils
export ast_utils
type
  ColKind* = enum
    colNone, colFloat, colInt, colBool, colString, colObject, colConstant, colGeneric
  Column* = ref object
    len*: int
    case kind*: ColKind
    of colFloat: fCol*: Tensor[float]
    of colInt: iCol*: Tensor[int]
    of colBool: bCol*: Tensor[bool]
    of colString: sCol*: Tensor[string]
    of colObject: oCol*: Tensor[Value]
    of colConstant: cCol*: Value
    of colGeneric: discard # added when overwriting `Column` type
    #  gKiloGram: Tensor[KiloGram]
    #  gKiloGram²: Tensor[KiloGram²]
    #  # or
    #  case gKind: colGenericKind
    #  of kKiloGram: gKiloGram: Tensor[KiloGram]
    #  of kKiloGram²: gKiloGram²: Tensor[KiloGram²]
    of colNone: discard

  ColumnLike* = concept x
    x.len is int
    x.kind is ColKind

  BuiltInTypes* = float | char | int | bool | string | Value
  SupportedTypes* = SomeNumber | BuiltInTypes


import gencase
export gencase
import macrocache
const TypeNames = CacheTable"ColTypeNames"
const TypeImpls = CacheTable"ColTypeImpls"
const TypeToEnumType = CacheTable"TypeToEnumType"

import algorithm, sugar, sequtils

proc genColNameStr*(types: seq[string]): string =
  result = "Column" & genCombinedTypeStr(types)

proc genColNameStr*(types: seq[NimNode]): string =
  result = "Column" & genCombinedTypeStr(types)

proc genColName*(types: seq[NimNode]): NimNode =
  let name = genColNameStr(types)
  result = genSym(nskType, name) # gensym required to make it a symbol that lasts

proc getRefType*(n: NimNode): NimNode =
  expectKind(n, nnkTypeDef)
  result = n[2]

proc getRecList(n: NimNode): NimNode =
  case n.kind
  of nnkRefTy: result = n[0][2][1]
  of nnkObjectTy: result = n[2][1]
  of nnkTypeDef: result = n[2][0][2][1]
  else: error("Invalid branch: " & $n.kind)

proc getGenericTypeBranch(n: NimNode): NimNode =
  # nice, huh?
  case n.kind
  of nnkTypeDef: result = n.getRefType.getRecList.getGenericTypeBranch
  of nnkRefTy: result = n.getRecList.getGenericTypeBranch()
  of nnkRecCase: result = n[7]
  of nnkObjectTy: result = n.getRecList.getGenericTypeBranch()
  else: error("Invalid branch: " & $n.kind)

proc patchColumn*(enumTyp: NimNode, typs: seq[NimNode]): NimNode =
  # get base `Column` type information
  let colImpl = getTypeInst(Column).getImpl
  var refTy = getRefType(colImpl)
  var body = getRecList(refTy)
  var rec = getGenericTypeBranch(body) # get the `colGeneric` branch of the `Column` object

  let enumName = getEnumName(enumTyp)

  let typName = genColumnTypeStr(typs)
  if typName notin TypeNames:
    let colSym = genSym(nskType, typName)
    TypeNames[typName] = colSym
    TypeToEnumType[typName] = enumName
    rec[1] = nnkRecList.newTree(genRecCase(enumName, typs))
    body[7] = rec
    result = nnkTypeDef.newTree(colSym, newEmptyNode(), refTy)
    result = nnkTypeSection.newTree(result)
    result = result.replaceSymsByIdents()
    TypeImpls[typName] = result
  else:
    result = TypeImpls[typName]

proc defColumn*(t: seq[NimNode]): NimNode =
  result = newStmtList()
  let enumTyp = genTypeEnum(t)
  result.add enumTyp
  result.add patchColumn(enumTyp, t)

proc defColumnImpl(typs: seq[NimNode], single: bool): NimNode =
  # first generate separate types of all `types`, then
  # the combined one. Mixed and matches are *not* generated, as it
  # could cause a complexity explosion
  if single:
    result = defColumn(typs)
  else:
    let typComb = combinations(typs)
    result = newStmtList()
    for comb in typComb:
      result.add defColumn(comb)

macro defColumn*(types: varargs[typed]): untyped =
  ## Generates a `Column*` type that can hold all given types in its `colGeneric` branch
  ## as well as every combination of the types.
  ##
  ## *Warning*: If you call this with more than very few types it will cause a complexity
  ## explosion! If you really need many different types in a `DataTable`, call `defSingleColumn`!
  ##
  ## Notes: in the future likely the macro logic will be changed such that the "largest
  ## possible type" will be looked up instead of the simplest based on a given type.
  let typs = bracketToSeq(types)
  result = defColumnImpl(typs, single = false)

macro defSingleColumn*(types: varargs[typed]): untyped =
  ## Equivalent to the above macro `defColumn`, but only generates the exact type that
  ## can hold *all* types at the same time and no intermediares. Call this if you need
  ## a `Column` type that can hold many types
  let typs = bracketToSeq(types)
  result = defColumnImpl(typs, single = true)


macro assignField(c, val: typed): untyped =
  # get the correct field name
  let typ0 = val.getTypeInst.getInnerType()
  let fn = getGenericField(typ0)
  result = quote do:
    `c`.`fn` = `val`

proc getColumnImpl(n: NimNode): NimNode =
  case n.kind
  of nnkSym:
    if "column" in n.strVal.normalize:
      result = getColumnImpl(n.getTypeImpl)
    else:
      result = getColumnImpl(n.getType)
  of nnkBracketExpr: result = n[1].getColumnImpl
  of nnkTypeDef: result = n[2]
  of nnkObjectTy: result = n
  of nnkCall: result = n.getType.getColumnImpl
  of nnkHiddenDeref: result = n[0].getColumnImpl
  else:
    error("invalid")

template `%~`*(v: Value): Value = v
proc pretty*(c: ColumnLike): string
proc compatibleColumns*[C: ColumnLike](c1, c2: C): bool {.inline.}
# just a no-op
template toColumn*[C: ColumnLike](c: C): C = c

func high*(c: Column): int = c.len - 1

func isConstant*(c: Column): bool = c.kind == colConstant

template makeColumn(s, T: typed): untyped =
  var result = patchColumn(T)(kind: colGeneric, len: s.len) #
  when typeof(s) is Tensor:
    assignField(result, s)
  else:
    let t = s.toTensor
    assignField(result, t)
  result

proc assignData*[C: ColumnLike; U](c: var C, data: Tensor[U]) =
  ## Unsafe if `data` does not match `c's` kind!
  when U is int:
    c.iCol = data
  elif U is float:
    c.fCol = data
  elif U is string:
    c.sCol = data
  elif U is bool:
    c.bCol = data
  elif U is Value:
    c.oCol = data
  else:
    assignField(c, data)

proc toColumn*[T: SupportedTypes](t: Tensor[T]): Column =
  when T is SomeInteger:
    result = Column(kind: colInt,
                    iCol: t.astype(int),
                    len: t.size)
  elif T is SomeFloat:
    result = Column(kind: colFloat,
                    fCol: t.astype(float),
                    len: t.size)
  elif T is bool:
    result = Column(kind: colBool,
                    bCol: t,
                    len: t.size)
  elif T is string or T is char:
    when T is char:
      let s = t.map_inline($x)
    else:
      let s = t
    result = Column(kind: colString,
                    sCol: s,
                    len: t.size)
  elif T is Value:
    result = Column(kind: colObject,
                    oCol: t,
                    len: t.size)
  #elif T isnot seq and T isnot Tensor:
  #  ## generate a new type and return it
  #  result = makeColumn(t)
  else:
    ## XXX: this needs to be a better message, but currently the real usage is still
    ## a bit weird.
    {.error: "The type " & $T & " is not supported in a `Column`. To store it " &
      "in a DataFrame, generate a `Column` derived type using `genColumn(" & $T & ")".}

proc toColumn*[C: ColumnLike; T](_: typedesc[C], t: Tensor[T]): C =
  when T is SomeInteger:
    result = C(kind: colInt,
                    iCol: t.asType(int),
                    len: t.size)
  elif T is SomeFloat:
    result = C(kind: colFloat,
                    fCol: t.asType(float),
                    len: t.size)
  elif T is bool:
    result = C(kind: colBool,
                    bCol: t,
                    len: t.size)
  elif T is string or T is char:
    result = C(kind: colString,
               sCol: t.asType(string),
               len: t.size)
  elif T is Value:
    result = C(kind: colObject,
                    oCol: t,
                    len: t.size)
  else:
    #elif T isnot seq and T isnot Tensor:
    ## generate a new type and return it
    ## get correct type using `getTypeEnum` and `getColType` and set
    ## use `getTypeEnum` to set the correct field value
    result = C(kind: colGeneric,
               len: t.size,
               gkKind: enumField(C, T))
    assignData(result, t)

proc toColumn*[T: not SupportedTypes](t: openArray[T] | Tensor[T]): auto =
  ## Tries to convert the given input data to a matching generic `Column*`
  ## type. Errors at CT if there is no matching `Column*` defined so far.
  when typeof(t) is Tensor:
    let x = t
  else:
    let x = t.toTensor()
  result = colType(T).toColumn(t)

proc toColumn*[C: ColumnLike; T](_: typedesc[C], t: openArray[T]): C =
  result = C.toColumn(t.toTensor())

proc toColumn*[T: SupportedTypes](s: openArray[T]): Column =
  var vals = newTensor[T](s.len)
  for i, x in s:
    vals[i] = x
  result = toColumn(vals)

proc toColumn*[T: SupportedTypes](x: T): Column =
  ## Turn a single scalar element of the supported types into a regular `Column`.
  ## If a single `Value` is handed, we convert to the native underlying type.
  # also possible to create single row column, but inefficient
  # for `summarize` though there's no way around
  when T is Value:
    withNative(x, val):
      let vals = newTensorWith[typeof(val)](1, val)
      result = toColumn(vals)
  else:
    let vals = newTensorWith[T](1, x)
    result = toColumn(vals)

proc toColumn*[C: ColumnLike; T: SupportedTypes](_: typedesc[C], x: T): C =
  ## Turn a single scalar element of the supported types into a regular `Column`.
  ## If a single `Value` is handed, we convert to the native underlying type.
  result = C.toColumn( toColumn(x) )

proc constantColumn*[T](val: T, len: int): Column =
  ## creates a constant column based on `val` and its type
  result = Column(len: len, kind: colConstant, cCol: %~ val)

proc constantColumn*[C: ColumnLike; T](_: typedesc[C], val: T, len: int): C =
  ## creates a constant column based on `val` and its type
  result = C(len: len, kind: colConstant, cCol: %~ val)

proc constantToFull*[C: ColumnLike](c: C): C =
  ## creates a real constant full tensor column based on a constant column
  if c.kind != colConstant: return c
  withNative(c.cCol, val):
    result = toColumn(C, newTensorWith[type(val)](c.len, val))

proc `[]`*[C: ColumnLike](c: C, slice: Slice[int]): C =
  case c.kind
  of colInt: result = C.toColumn c.iCol[slice.a .. slice.b]
  of colFloat: result = C.toColumn c.fCol[slice.a .. slice.b]
  of colString: result = C.toColumn c.sCol[slice.a .. slice.b]
  of colBool: result = C.toColumn c.bCol[slice.a .. slice.b]
  of colObject: result = C.toColumn c.oCol[slice.a .. slice.b]
  of colConstant:
    # for constant keep column, only adjust the length to the slice
    result = c
    result.len = slice.b - slice.a + 1
  of colGeneric:
    withCaseStmt(c, gk, C):
      result = C.toColumn c.gk[slice.a .. slice.b]
  of colNone: raise newException(IndexDefect, "Accessed column is empty!")

proc newColumn*(kind = colNone, length = 0): Column =
  case kind
  of colFloat: result = toColumn newTensor[float](length)
  of colInt: result = toColumn newTensor[int](length)
  of colString: result = toColumn newTensor[string](length)
  of colBool: result = toColumn newTensor[bool](length)
  of colObject: result = toColumn newTensor[Value](length)
  of colConstant: result = Column.constantColumn(Value(kind: VNull), length)
  of colNone: result = Column(kind: colNone, len: 0)
  of colGeneric: raise newException(Exception, "implement me")

proc newColumnLike*[C: ColumnLike](_: typedesc[C], kind = colNone, length = 0): C =
  case kind
  of colFloat: result = toColumn(C, newTensor[float](length))
  of colInt: result = toColumn(C, newTensor[int](length))
  of colString: result = toColumn(C, newTensor[string](length))
  of colBool: result = toColumn(C, newTensor[bool](length))
  of colObject: result = toColumn(C, newTensor[Value](length))
  # XXX: fix constant
  of colConstant: result = C.constantColumn(Value(kind: VNull), length)
  of colNone: result = C(kind: colNone, len: 0)
  of colGeneric: doAssert false, "Constructing a generic column not supported, as it's not a specific type!"

proc toColKind*[T](dtype: typedesc[T]): ColKind =
  when T is SomeFloat:
    result = colFloat
  elif T is SomeInteger:
    result = colInt
  elif T is bool:
    result = colBool
  elif T is string:
    result = colString
  elif T is Value:
    result = colObject

proc toColKind*(vKind: ValueKind): ColKind =
  case vKind
  of VFloat: result = colFloat
  of VInt: result = colInt
  of VString: result = colString
  of VBool: result = colBool
  of VObject: result = colObject
  of VNull: result = colObject

proc toValueKind*(col: Column): ValueKind =
  case col.kind
  of colFloat: result = VFloat
  of colInt: result = VInt
  of colString: result = VString
  of colBool: result = VBool
  of colObject: result = VObject
  of colConstant:
    # need to look at the `ValueKind` of the constant!
    result = col.cCol.kind
  of colGeneric:
    raise newException(ValueError, "Generic column does not have a corresponding ValueKind.")
  of colNone: result = VNull

proc toValueKind*(col: ColKind): ValueKind {.deprecated: "This version of `toValueKind` " &
    "has been deprecated in favor of a `toValueKind` taking a `Column` object. This way a " &
    "conversion of `colConstant` can be done to the underlying type of the `Value` object.".} =
  case col
  of colFloat: result = VFloat
  of colInt: result = VInt
  of colString: result = VString
  of colBool: result = VBool
  of colObject: result = VObject
  of colConstant: result = VObject
  of colNone: result = VNull
  of colGeneric: raise newException(Exception, "implement me")

proc nativeColKind*(col: Column): ColKind =
  ## Returns the native column kind, i.e. the column kind the native data stored
  ## in the column has, ``including`` constant columns (hence the native kind is
  ## ``not`` equal to the `kind` field of the column!
  result = col.toValueKind.toColKind # a back and forth

proc toNimType*[C: ColumnLike](c: C): string =
  ## returns the string name of the underlying data type of the column kind
  case c.kind
  of colFloat: result = "float"
  of colInt: result = "int"
  of colString: result = "string"
  of colBool: result = "bool"
  of colObject: result = "object"
  of colConstant: result = "constant"
  of colNone: result = "null"
  of colGeneric:
    when C isnot Column:
      var typ = $c.gkKind
      typ.removePrefix("gk")
      result = "generic[" & typ & "]"
    else:
      raise newException(ValueError, "Invalid branch for `Column` type.")

template withNativeTensor*[C: ColumnLike](c: C,
                                          valName: untyped,
                                          body: untyped): untyped =
  case c.kind
  of colInt:
    let `valName` {.inject.} =  c.iCol
    body
  of colFloat:
    let `valName` {.inject.} =  c.fCol
    body
  of colString:
    let `valName` {.inject.} =  c.sCol
    body
  of colBool:
    let `valName` {.inject.} =  c.bCol
    body
  of colObject:
    let `valName` {.inject.} =  c.oCol
    body
  of colConstant:
    withNative(c.cCol, realVal):
      let `valName` {.inject.} = newTensorWith(c.len, realVal)
      body
  of colGeneric:
    # get generic type of the given `ColumnLike`
    withCaseStmt(c, gk, C):
      let `valName` {.inject.} = c.gk
      body
  of colNone: raise newException(ValueError, "Accessed column is empty!")

proc toColumn*[C: ColumnLike; U: ColumnLike](_: typedesc[C], c: U): C =
  withNativeTensor(c, t):
    result = toColumn(C, t)

proc combinedColKind*[C: ColumnLike](c: seq[C]): ColKind =
  if c.allIt(it == c[0]):
    # all the same, take any
    result = c[0].kind
  elif c.allIt(it.kind in {colInt, colFloat}):
    # int and float can be combined to float, since we're lenient like that
    result = colFloat
  elif c.anyIt(it.kind == colConstant):
    # extract col constant and convert their `ValueKind` to `ColKind`
    let noConst = c.mapIt(it.nativeColKind)
    if noConst.allIt(it == noConst[0]): result = noConst[0]
    elif noConst.allIt(it in {colInt, colFloat}): result = colFloat
    else: result = colObject
  else:
    # the rest can only be merged via object columns of `Values`.
    result = colObject

template withNative*[C: ColumnLike](c: C, idx: int,
                                    valName: untyped,
                                    body: untyped): untyped =
  case c.kind
  of colInt:
    let `valName` {.inject.} =  c[idx, int]
    body
  of colFloat:
    let `valName` {.inject.} =  c[idx, float]
    body
  of colString:
    let `valName` {.inject.} =  c[idx, string]
    body
  of colBool:
    let `valName` {.inject.} =  c[idx, bool]
    body
  of colObject:
    let `valName` {.inject.} =  c[idx, Value]
    body
  of colConstant:
    let `valName` {.inject.} =  c[idx, Value]
    body
  of colGeneric:
    withCaseStmt(c, gk, C):
      let `valName` {.inject.} = c.gk[idx]
      body
  of colNone, colGeneric: raise newException(ValueError, "Accessed column is empty!")

template withNativeDtype*[C: ColumnLike](c: C, body: untyped): untyped =
  case c.kind
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
  of colConstant:
    withNative(c.cCol, realVal):
      type dtype {.inject.} = typeof(realVal)
      body
  of colGeneric:
    withCaseStmt(c, gk, C):
      type dtype {.inject.} = fieldToType(gk)
      body
  of colNone: raise newException(ValueError, "Accessed column is empty!")

template withDtypeByColKind*(colKind: ColKind, body: untyped): untyped =
  case colKind
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
  of colObject, colConstant:
    type dtype {.inject.} = Value
    body
  of colGeneric:
    raise newException(ValueError, "Also need generic enum field value!")
  of colNone: raise newException(ValueError, "Invalid column kind!")

proc asValue*[T](t: Tensor[T]): Tensor[Value] {.noinit.} =
  ## Apply type conversion on the whole tensor
  result = t.map(x => (%~ x))

proc valueTo*[T](t: Tensor[Value], dtype: typedesc[T],
                 dropNulls: static bool = false): Tensor[T] =
  when not dropNulls:
    when T is string:
      result = t.map(x => x.toStr)
    elif T is float:
      result = t.map(x => x.toFloat)
    elif T is int:
      result = t.map(x => x.toInt)
    elif T is bool:
      result = t.map(x => x.toBool)
    elif T is Value:
      result = t
  else:
    # filter tensor to non Null values
    var outputIdx = newSeqOfCap[int](t.size)
    for idx, x in t:
      if x.kind != VNull:
        outputIdx.add idx[0]
    result = newTensor[T](outputIdx.len)
    when T is string:
      for i, idx in outputIdx:
        result[i] = t[idx].toStr
    elif T is float:
      for i, idx in outputIdx:
        result[i] = t[idx].toFloat
    elif T is int:
      for i, idx in outputIdx:
        result[i] = t[idx].toInt
    elif T is bool:
      for i, idx in outputIdx:
        result[i] = t[idx].toBool
    elif T is Value:
      for i, idx in outputIdx:
        result[i] = t[idx]

proc toTensor*[C: ColumnLike; T](c: C, _: typedesc[T],
                                 dropNulls: static bool = false): Tensor[T] =
  ## `dropNulls` only has an effect on `colObject` columns. It allows to
  ## drop Null values to get (hopefully) a valid raw Tensor
  case c.kind
  of colInt:
    when T is int:
      result = c.iCol
    elif T is SomeNumber:
      result = c.iCol.astype(T)
    elif T is Value:
      result = c.iCol.asValue
    elif T is string:
      result = c.iCol.map_inline($x)
    else:
      raise newException(ValueError, "Invalid conversion of int column to " & $T & "!")
  of colFloat:
    when T is float:
      result = c.fCol
    elif T is SomeNumber:
      result = c.fCol.astype(T)
    elif T is Value:
      result = c.fCol.asValue
    elif T is string:
      result = c.fCol.map_inline($x)
    else:
      raise newException(ValueError, "Invalid conversion of float column to " & $T & "!")
  of colString:
    when T is string:
      result = c.sCol
    elif T is Value:
      result = c.sCol.asValue
    else:
      raise newException(ValueError, "Invalid conversion of string column to " & $T & "!")
  of colBool:
    when T is bool:
      result = c.bCol
    elif T is Value:
      result = c.bCol.asValue
    else:
      raise newException(ValueError, "Invalid conversion of bool column to " & $T & "!")
  of colObject:
    result = c.oCol.valueTo(T, dropNulls = dropNulls)
  of colConstant:
    result = c.constantToFull.toTensor(T, dropNulls)
  of colGeneric:
    result = getTensor(c, Tensor[T])
  of colNone: raise newException(ValueError, "Accessed column is empty!")

proc toTensor*[C: ColumnLike; T](c: C, slice: Slice[int], dtype: typedesc[T]): Tensor[T] =
  case c.kind
  of colInt:
    when T is int:
      result = c.iCol[slice.a .. slice.b]
    elif T is SomeNumber:
      result = c.iCol[slice.a .. slice.b].astype(T)
  of colFloat:
    when T is float:
      result = c.fCol[slice.a .. slice.b]
    elif T is SomeNumber:
      result = c.fCol[slice.a .. slice.b].astype(T)
  of colString:
    when T is string:
      result = c.sCol[slice.a .. slice.b]
  of colBool:
    when T is bool:
      result = c.bCol[slice.a .. slice.b]
  of colObject:
    result = c.oCol[slice.a .. slice.b].valueTo(T)
  of colConstant:
    result = newTensorWith[T](slice.b - slice.a + 1, c.cCol.to(T))
  of colGeneric:
    withCaseStmt(c, gk, C):
      when Tensor[T] is typeof(c.gk):
        result = c.gk[slice.a .. slice.b]
      else:
        raise newException(ValueError, "Invalid types ! " & $T & " for " & $typeof(c.gk))
  of colNone: raise newException(ValueError, "Accessed column is empty!")

proc `[]`*[C: ColumnLike; T](c: C, idx: int, dtype: typedesc[T]): T =
  when T isnot Value:
    case c.kind
    of colInt:
      when T is int:
        result = c.iCol[idx]
      elif T is SomeNumber:
        result = c.iCol[idx].T
      elif T is string:
        result = $c.iCol[idx]
    of colFloat:
      when T is float:
        result = c.fCol[idx]
      elif T is SomeNumber:
        result = c.fCol[idx].T
      elif T is string:
        # convert to Value and then string so that we use one single
        # formatting function. This is slow anyways
        result = pretty(%~ c.fCol[idx])
    of colString:
      when T is string:
        result = c.sCol[idx]
    of colBool:
      when T is bool:
        result = c.bCol[idx]
    of colObject:
      when T is string:
        result = c.oCol[idx].toStr
      elif T is float:
        result = c.oCol[idx].toFloat
      elif T is int:
        result = c.oCol[idx].toInt
      elif T is bool:
        result = c.oCol[idx].toBool
    of colConstant:
      when T is string:
        result = c.cCol.toStr
      elif T is float:
        result = c.cCol.toFloat
      elif T is int:
        result = c.cCol.toInt
      elif T is bool:
        result = c.cCol.toBool
    of colGeneric:
      result = getTensor(c, Tensor[T])[idx]
    of colNone: raise newException(ValueError, "Accessed column is empty!")
  else:
    case c.kind
    of colInt: result = %~ c.iCol[idx]
    of colFloat: result = %~ c.fCol[idx]
    of colString: result = %~ c.sCol[idx]
    of colBool: result = %~ c.bCol[idx]
    of colObject: result = c.oCol[idx]
    of colConstant: result = c.cCol
    of colGeneric:
      # get generic type of the given `ColumnLike`
      withCaseStmt(c, gk, C):
        let val {.inject.} = c.gk[idx]
        result = %~ val
    of colNone: raise newException(ValueError, "Accessed column is empty!")

proc toObjectColumn*[C: ColumnLike](c: C): C =
  ## returns `c` as an object column
  ## XXX: can't we somehow convert same slices of a tensor?
  var res = newTensor[Value](c.len)
  withNativeTensor(c, t):
    for idx in 0 ..< c.len:
      res[idx] = %~ (t[idx])
  result = C.toColumn res

proc `[]=`*[C: ColumnLike; T](c: var C, idx: int, val: T) =
  ## assign `val` to column `c` at index `idx`
  ## If the types match, it just calls `[]=` on the tensor.
  ## If they are compatible, `val` is converted to c's type.
  ## If they are incompatible, `c` will be rewritten to an object
  ## column.
  var rewriteAsValue = false
  when T is SupportedTypes:
    case c.kind
    of colFloat:
      when T is float:
        c.fCol[idx] = val
      elif T is SomeNumber:
        c.fCol[idx] = val.float
    of colInt:
      when T is int:
        c.iCol[idx] = val
      else:
        rewriteAsValue = true
    of colString:
      when T is string:
        c.sCol[idx] = val
      else:
        rewriteAsValue = true
    of colBool:
      when T is bool:
        c.bCol[idx] = val
      else:
        rewriteAsValue = true
    of colObject:
      c.oCol[idx] = %~ val
    of colConstant:
      if c.cCol == %~ val: discard # do nothing
      elif c.cCol.kind == VNull:
        # turn into constant column of `val`
        c.cCol = %~ val
      else:
        # need to replace constant column by non constant with changed value at
        # specified index
        c = c.constantToFull()
        c[idx] = val
    of colNone: raise newException(ValueError, "Accessed column is empty!")
    of colGeneric: raise newException(Exception, "Invalid branch. This should never happen!")
    if rewriteAsValue:
      # rewrite as an object column
      c = c.toObjectColumn()
      c.oCol[idx] = %~ val
  else:
    doAssert c.kind == colGeneric, "Assignment of unsupported types only to `colGeneric` columns!"
    setVal(c, idx, val)

proc `[]=`*[C: ColumnLike; T](c: var C, slice: Slice[int], t: Tensor[T]) =
  ## Assigns the tensor `t` to the slice `slice`. The slice length must match
  ## the tensor length exactly and must be smaller than the column length.
  ##
  ## If the type of `t` does not match the column kind, we reallocate to an object column.
  let length = slice.b - slice.a + 1
  let sa = slice.a
  let sb = slice.b
  if length != t.size:
    raise newException(ValueError, "Given tensor of size " & $t.size & " does not match slice " &
      $slice & " with length: " & $length & ".")
  elif length > c.len:
    raise newException(ValueError, "Given slice " & $slice & " of length " & $length &
      " is larger than column length of " & $c.len & ".")
  case c.kind
  of colInt:
    when T is int:
      c.iCol[sa .. sb] = t
    else:
      c = c.toObjectColumn()
      c.oCol[sa .. sb] = t.asValue()
  of colFloat:
    when T is float:
      c.fCol[sa .. sb] = t
    elif T is int:
      c.fCol[sa .. sb] = t.astype(float)
    else:
      c = c.toObjectColumn()
      c.oCol[sa .. sb] = t.asValue()
  of colString:
    when T is string:
      c.sCol[sa .. sb] = t
    else:
      c = c.toObjectColumn()
      c.oCol[sa .. sb] = t.asValue()
  of colBool:
    when T is bool:
      c.bCol[sa .. sb] = t
    else:
      c = c.toObjectColumn()
      c.oCol[sa .. sb] = t.asValue()
  of colConstant:
    ## if we are handed a Tensor to slice assign, we have to convert to a full column
    ## Then try again with the full tensor (possibly convert to object column then)
    c = c.constantToFull()
    c[sa .. sb] = t
  of colObject:
    when T is Value:
      c.oCol[sa .. sb] = t
    else:
      c.oCol[sa .. sb] = t.asValue()
  of colGeneric:
    withCaseStmt(c, gk, C):
      when Tensor[T] is typeof(c.gk):
        c.gk[slice.a .. slice.b] = t
      else:
        raise newException(ValueError, "Invalid types ! " & $T & " for " & $typeof(c.gk))
  of colNone:
    raise newException(ValueError, "Cannot assign a tensor to an empty column.")

proc `[]=`*[C: ColumnLike](c: var C, slice: Slice[int], col: C) =
  let sa = slice.a.int
  let sb = slice.b.int
  if c.compatibleColumns(col):
    c = c.constantToFull() # in case `c` is const, else is no-op
    withNativeDtype(c):
      c[slice] = col.toTensor(dtype) # converts to full, if it's const
  elif c.kind == colConstant and col.kind == colConstant:
    if c.cCol == col.cCol: return # nothing to do
    else:
      c = c.constantToFull()
      let c2 = col.constantToFull()
      c[slice] = c2
  else:
    # else we have no other choice than convert to `Value` :/
    c = c.toObjectColumn()
    c.oCol[sa .. sb] = col.toTensor(Value)

template withNative2*(c1, c2: Column, idx1, idx2: int,
                      valName1, valName2: untyped,
                      body: untyped): untyped =
  assert c1.kind == c2.kind
  case c1.kind
  of colInt:
    let `valName1` {.inject.} =  c1[idx1, int]
    let `valName2` {.inject.} =  c2[idx2, int]
    body
  of colFloat:
    let `valName1` {.inject.} =  c1[idx1, float]
    let `valName2` {.inject.} =  c2[idx2, float]
    body
  of colString:
    let `valName1` {.inject.} =  c1[idx1, string]
    let `valName2` {.inject.} =  c2[idx2, string]
    body
  of colBool:
    let `valName1` {.inject.} =  c1[idx1, bool]
    let `valName2` {.inject.} =  c2[idx2, bool]
    body
  of colObject:
    let `valName1` {.inject.} =  c1[idx1, Value]
    let `valName2` {.inject.} =  c2[idx2, Value]
    body
  of colConstant: raise newException(ValueError, "Accessed column is constant!")
  of colNone, colGeneric: raise newException(ValueError, "Accessed column is empty!")

proc compatibleColumns*[C: ColumnLike](c1, c2: C): bool {.inline.} =
  if c1.kind == c2.kind: result = true
  elif c1.kind in {colInt, colFloat} and
       c2.kind in {colInt, colFloat}:
    result = true
  elif c1.kind == colConstant:
    # check if underlying type is same as `c2`
    let c1VKind = c1.cCol.kind.toColKind # convert ValueKind of const to ColKind
    result = c1VKind == c2.kind
  elif c2.kind == colConstant:
    # check if underlying type is same as `c1`
    let c1VKind = c2.cCol.kind.toColKind # convert ValueKind of const to ColKind
    result = c1VKind == c1.kind
  else: result = false

proc equal*(c1: Column, idx1: int, c2: Column, idx2: int): bool =
  ## checks if the value in `c1` at `idx1` is equal to the
  ## value in `c2` at `idx2`
  if not compatibleColumns(c1, c2): return false
  elif c1.kind == c2.kind:
    withNativeDtype(c1):
      result = c1[idx1, dtype] == c2[idx2, dtype]
  else:
    # need to get the enveloping kind and read the data using that corresponding
    # data type
    let kind = combinedColKind(@[c1, c2])
    withDtypeByColKind(kind):
      result = c1[idx1, dtype] == c2[idx2, dtype]

proc toObject*[C: ColumnLike](c: C): C {.inline.} =
  case c.kind
  of colObject: result = c
  of colInt: result = C.toColumn c.iCol.asValue
  of colFloat: result = C.toColumn c.fCol.asValue
  of colString: result = C.toColumn c.sCol.asValue
  of colBool: result = C.toColumn c.bCol.asValue
  of colConstant: raise newException(ValueError, "Accessed column is constant!")
  of colGeneric:
    withCaseStmt(c, gk, C):
      result = C.toColumn c.gk.asValue
  of colNone: raise newException(ValueError, "Accessed column is empty!")

proc add*[C: ColumnLike](c1, c2: C): C =
  ## adds column `c2` to `c1`. Uses `concat` internally.
  ## XXX: for generic columns: IF both share the same field type (and the same field
  ## is filled in each case) we *can* add them even if one is `C` and the other `D`. Need
  ## to return a different type than either possibly or one of them.
  if c1.isNil: return c2 # allows to add to an uninitialized column
  if c2.len == 0: return c1
  elif c1.len == 0: return c2
  if c1.kind == c2.kind:
    # just concat directly
    case c1.kind
    of colInt: result = C.toColumn concat(c1.iCol, c2.iCol, axis = 0)
    of colFloat: result = C.toColumn concat(c1.fCol, c2.fCol, axis = 0)
    of colBool: result = C.toColumn concat(c1.bCol, c2.bCol, axis = 0)
    of colString: result = C.toColumn concat(c1.sCol, c2.sCol, axis = 0)
    of colObject: result = C.toColumn concat(c1.oCol, c2.oCol, axis = 0)
    of colConstant:
      if c1.cCol == c2.cCol: result = c1 # does not matter which to return
      else: result = add(c1.constantToFull, c2.constantToFull)
    of colGeneric:
      withCaseStmt(c1, gk, C):
        result = C.toColumn concat(c1.gk, c2.gk, axis = 0)
    of colNone: doAssert false, "Both columns are empty!"
  elif compatibleColumns(c1, c2):
    # convert both to float
    case c1.kind
    of colInt:
      # c1 is int, c2 is float
      let c2T = c2.constantToFull().toTensor(float)
      result = C.toColumn concat(c1.iCol.astype(float), c2T, axis = 0)
    of colFloat:
      # c1 is float, c2 is int
      let c2T = c2.constantToFull().toTensor(float)
      result = C.toColumn concat(c1.fCol, c2T, axis = 0)
    else:
      # one of the two is constant and same type as the other
      # `constantToFull` is a no-op for the non-constant column
      result = add(c1.constantToFull, c2.constantToFull) # recurse on this proc
  elif c1.kind == colConstant or c2.kind == colConstant:
    result = add(c1.constantToFull, c2.constantToFull)
  else:
    # convert both columns to Value
    result = C.toColumn concat(c1.toObject.oCol, c2.toObject.oCol, axis = 0)
  result.len = c1.len + c2.len

proc toNativeColumn*(s: openArray[Value]): Column =
  ## given input as `Value`, will attempt to return the column as native
  ## data type.
  ## NOTE: this is unsafe and assumes the values are indeed all one type!
  if s.len > 0:
    withNativeConversion(s[0].kind, get):
      var data = newTensor[dtype](s.len)
      for i, x in s:
        data[i] = get(x)
      result = toColumn data

proc toNativeColumn*(c: Column, failIfImpossible: static bool = true): Column =
  ## attempts to convert the given column from `colObject` to its
  ## native type, if possible. This is mainly useful after removal
  ## of null values. If it fails (i.e. floats and strings in one
  ## col) the result stays a colObject.
  ##
  ## In the default case `failIfImpossible = true` this procedure will
  ## fail with an `AssertionDefect` if a column contains multiple datatypes.
  ## This can be disabled so that at worst the input is returned as an
  ## object type column.
  if c.kind != colObject: return c
  # assuming the column ``can`` be converted to native type, the
  # first element contains all information we need, namely the
  # value kind of ``all`` elements in the column
  # exception: first element is int, but mixed with float
  let vKind = c[0, Value].kind
  ## TODO: this can fail...
  withNativeConversion(vKind, get):
    var data = newTensor[dtype](c.len)
    let cValue = c.toTensor(Value)
    for i in 0 ..< c.len:
      when failIfImpossible:
        doAssert cValue[i].kind == vKind, "Column contains actual multiple datatypes! " &
          $vKind & " and " & $cValue[i].kind & "!"
      else:
        if cValue[i].kind != vKind:
          # not possible to convert, return input
          return c
      data[i] = get cValue[i]
    result = toColumn data

proc nullColumn*[C: ColumnLike](_: typedesc[C], num: int): C =
  ## returns an object `Column` with `N` values, which are
  ## all `VNull`
  var nullseq = newTensor[Value](num)
  for i in 0 ..< num:
    nullseq[i] = Value(kind: VNull)
  result = C.toColumn(nullseq)

#proc `*`[T: SomeNumber]*(c: Column, x: T)
proc contains*[T: float | string | int | bool | Value](c: Column, val: T): bool =
  let t = toTensor(c, T)
  result = false
  for x in t:
    if val == x:
      return true

template liftScalarToColumn*(name: untyped): untyped =
  proc `name`*(c: Column): Value =
    withNativeDtype(c):
      result = %~ `name`(c.toTensor(dtype))
liftScalarToColumn(max)

proc pretty*(c: ColumnLike): string =
  ## pretty prints a Column
  result = &"Column of type: {toNimType(c)} with length: {c.len}"
  if c.kind != colNone:
    result.add "\n"
    withNativeTensor(c, t):
      result.add &"  contained Tensor: {t}"
template `$`*(c: ColumnLike): string = pretty(c)

proc clone*(c: Column): Column =
  ## clones the given column by cloning the Tensor
  result = Column(kind: c.kind, len: c.len)
  case result.kind
  of colInt: result.iCol = c.iCol.clone()
  of colFloat: result.fCol = c.fCol.clone()
  of colString: result.sCol = c.sCol.clone()
  of colBool: result.bCol = c.bCol.clone()
  of colObject: result.oCol = c.oCol.clone()
  of colConstant: result.cCol = c.cCol # just a `Value`
  of colNone, colGeneric: discard

proc map*[T; U](c: Column, fn: (T -> U)): Column =
  ## Maps a given column given `fn` to a new column.
  ## Because `Column` is a variant type, an untyped mapping function
  ## won't compile.
  ##
  ## See the `map_inline` template below, which attempts to work around this
  ## limitation by compiling all map function bodies, which are valid for `c`.
  ##
  ## .. code-block:: nim
  ##   c.map((x: int) => x * 5)
  ##
  ## Using this is not really recommended. Use `df["x", int].map(x => x * 5)` instead!
  result = toColumn c.toTensor(T).map_inline(fn(x))

template map_inline*(c: Column, body: untyped): Column =
  ## This is a helper template, which attempts to work around this
  ## limitation by compiling all map function bodies, which are valid for `c`.
  ## However, be careful: by using the template you throw out possible compile
  ## time checking and replace it by possible exceptions in your code!
  ##
  ## .. code-block:: nim
  ##   c.map_inline(x * 5)
  ##
  ## This example will throw a runtime exception, if `* 5` is invalid for the
  ## column type that `c` actually is at runtime!
  ## Using this is not really recommended. Use `df["x", int].map_inline(x * 5)` instead!
  withNativeDtype(c):
    var res: Column
    when compiles((map(c, (x: dtype) => body))):
      res = toColumn map(c, (x: dtype) => body)
    else:
      ## Cannot raise a CT error unfortunately I think, because this branch will always be compiled
      ## for one of the column types
      raise newException(Exception, "Column is of invalid type for map body `" & $(astToStr(body)) &
        "` for dtype of column: " & $(c.toNimType))
    res

proc lag*[T](t: Tensor[T], n = 1, fill: T = default(T)): Tensor[T] {.noinit.} =
  ## Lags the input tensor by `n`, i.e. returns a shifted tensor
  ## such that it *lags* behind `t`:
  ##
  ## `lag([1, 2, 3], 1) ⇒ [null, 1, 2]`
  ##
  ## NOTE: The value of `null` is filled by `default(T)` value by default!
  ## Use the `fill` argument to change the value to be set.
  result = newTensorUninit[T](t.size)
  #result[0 ..< n] = leave unspecified for now
  let hi = t.size.int - n
  result[n ..< t.size.int] = t[0 ..< hi]
  result[0 ..< n] = fill

proc lag*[C: ColumnLike](c: C, n = 1): C =
  ## Overload of the above for columns
  withNativeDtype(c):
    result = C.toColumn lag(c.toTensor(dtype), n)

proc lead*[T](t: Tensor[T], n = 1, fill: T = default(T)): Tensor[T] {.noinit.} =
  ## Leads the input tensor by `n`, i.e. returns a shifted tensor
  ## such that it *leads* ahead of `t`:
  ##
  ## `lead([1, 2, 3], 1) ⇒ [2, 3, null]`
  ##
  ## NOTE: The value of `null` is filled by `default(T)` value by default!
  ## Use the `fill` argument to change the value to be set.
  result = newTensorUninit[T](t.size)
  #result[0 ..< n] = leave unspecified for now
  let hi = t.size.int - n
  result[0 ..< hi] = t[n ..< t.size.int]
  result[hi ..< t.size.int] = fill

proc lead*[C: ColumnLike](c: C, n = 1): C =
  ## Overload of the above for columns
  withNativeDtype(c):
    result = C.toColumn lead(c.toTensor(dtype), n)
