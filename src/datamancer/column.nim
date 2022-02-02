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

  SupportedTypes = float | char | int | bool | string | Value


import gencase
import macrocache
const TypeNames* = CacheTable"ColTypeTable" # initTable[string, NimNode]()
var FieldNames* {.compileTime.} = initTable[string, seq[string]]()

proc nodeRepr(n: NimNode): string =
  case n.kind
  of nnkIdent, nnkSym: result = n.strVal
  else: result = n.toStrLit.strVal.multiReplace([("[", "_"), ("]", "_")])

proc genFieldName*(typ: NimNode): NimNode =
  echo "typ ", typ.treerepr
  var nR = typ.nodeRepr
  if nR.startsWith("Column"):
    nR = nR.dup(removePrefix("Column"))
  result = ident("g" & nR) # & $Col

import algorithm, sugar, sequtils

proc bracketToSeq(types: NimNode): seq[NimNode] =
  doAssert types.kind == nnkBracket
  result = newSeq[NimNode]()
  for typ in types:
    result.add getInnerType(typ)

proc genCombinedTypeStr*(types: seq[NimNode]): string =
  let typStrs = types.mapIt(it.nodeRepr)
  let typClean = typStrs.filterIt(it != "Column")
  result = $(typClean.mapIt(it.dup(removePrefix("Column")).capitalizeAscii).sorted.join("_"))

proc genColNameStr*(types: seq[NimNode]): string =
  result = "Column" & genCombinedTypeStr(types)
  #result = "Column" & types.mapIt(it.nodeRepr.capitalizeAscii).join()

proc genColName*(types: seq[NimNode]): NimNode =
  let name = genColNameStr(types)
  result = genSym(nskType, name) # gensym required to make it a symbol that lasts

proc hasFieldName(col: NimNode, field: string): bool =
  let names = FieldNames[col.strVal]
  result = field in names

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

proc getInnerType*(n: NimNode, last = newEmptyNode()): NimNode =
  #echo n.repr, " of kind ", n.kind
  case n.kind
  of nnkSym:
    let nstr = n.strVal.normalize
    if nstr.len == 1 or "gensym" in nstr or "uniontype" in nstr: # generic or gensymm'd symbol, skip
      #echo n.getTypeImpl.treerepr
      if last.kind != nnkEmpty and last.strVal == n.strVal:
        # use typeimpl
        result = n.getTypeImpl.getInnerType(last = n)
      else:
        result = n.getTypeInst.getInnerType(last = n)
    else:
      result = n
  of nnkBracketExpr:
    let n0s = n[0].strVal.normalize
    if n0s notin ["tensor", "seq", "typedesc", "openarray"]:
      result = n
    else:
      result = n[1].getInnerType
  of nnkRefTy:
    result = n[0]
    if result.strVal.endsWith(":ObjectType"): ##  XXX: clean up
      var tmp = result.strVal
      tmp.removeSuffix(":ObjectType")
      result = ident(tmp)
  of nnkHiddenDeref, nnkVarTy:
    result = n[0].getInnerType()
  else:
    echo n.treerepr
    error("Invalid")
  #echo "RESULT: ", result.repr

  #n.getTypeImpl[1][1] # get inner type of `Tensor[T]`

macro patchColumn*(types: varargs[typed]): untyped =
  # get base `Column` type information
  var typImp = getTypeInst(Column).getImpl
  #echo typImp.treerepr
  var refTy = getRefType(typImp)
  #echo refTy.treerepr
  var body = getRecList(refTy)
  #echo body.treerepr
  var rec = getGenericTypeBranch(body) # get the `colGeneric` branch of the `Column` object

  let innerTyps = bracketToSeq(types)
  let colId = genColName(innerTyps)
  if colId.strVal in TypeNames:
    result = TypeNames[colId.strVal]
  else:
    TypeNames[colId.strVal] = colId

    #echo colId.repr
    #var fieldNames = newSeq[NimNode]()
    echo rec.treerepr
    echo body.treerepr
    if innerTyps.len > 1:
      rec[1] = nnkRecList.newTree()
      for typ in innerTyps:
        echo typ.treerepr
        let fieldName = genFieldName(typ)
        let tTyp = nnkBracketExpr.newTree(ident"Tensor", typ)
        rec[1].add nnkIdentDefs.newTree(fieldName, tTyp, newEmptyNode())
    else:
      let fieldName = genFieldName(innerTyps[0])
      let tTyp = nnkBracketExpr.newTree(ident"Tensor", innerTyps[0])
      rec[1] = nnkIdentDefs.newTree(fieldName, tTyp, newEmptyNode())

    #ident("Tensor[" & $typ0.strVal & "]")
    #rec[1] = nnkIdentDefs.newTree(fieldName, tTyp, newEmptyNode())
    body[7] = rec
    #echo body.treerepr
    result = refTy

    #echo result.repr
    result = quote do:
      #mixin `tTyp`
      type
        `colId` = `result`
      `colId`
    result = result.replaceSymsByIdents()


  #if true: quit()
  #echo result.repr
  #TypeNames[@[typ0.strVal]] = colId
  #FieldNames[colId.strVal] = @[fieldName.strVal]


#proc `$`[T: DataFrameLike](df: T): string =
#  result = "DF(cols: "
#  for c in df.cols:
#    echo "print ", c
#    result.add $c & ", "
#  result.add ")"

macro assignField(c, val: typed): untyped =
  # get the correct field name
  #echo val.treerepr
  #echo val.getType.treerepr
  #echo val.getTypeImpl.treerepr
  #echo val.getImpl.treerepr
  #echo val.getTypeInst[1].getImpl.treerepr
  echo "INNER START ", val.treerepr
  let typ0 = c.getInnerType()
  echo "INNER TYPE ", typ0.treerepr
  let fn = genFieldName(typ0) #FieldNames[@[typ0.strVal]]
  result = quote do:
    `c`.`fn` = `val`
  #echo fn.repr

proc getColumnImpl(n: NimNode): NimNode =
  #echo n.kind, " and ", n.repr
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
    echo n.treerepr
    error("invalid")

macro getGenericFieldType(c: typed): untyped =
  # returns the type of the generic field of the given column
  let cTyp = c.getColumnImpl()#c.getType[1].getImpl # required to check that `dtype` matches this type
  #echo "CTYP ", cTyp.treerepr
  if cTyp.kind != nnkNilLit:
    let genBranch = getGenericTypeBranch(cTyp)
    echo genBranch.treerepr
    let innerTyp = genBranch[1][1][1]
    result = quote do:
      `innerTyp`
    echo "inner type ", innerTyp.repr
  #let fn = genFieldName(typ0) # FieldNames[@[typ0.strVal]]
  #let cTyp = c.getTypeInst # required to check that `dtype` matches this type
  #
  #if cTyp.hasFieldName(fn.strVal):
  #  result = quote do:
  #    `c`.`fn`
  #else:
  #  error("The given column of type " & $cTyp.strVal & " has no generic field of type " & $typ0.strVal)

macro hasGenericField(c: typed): untyped =
  # returns the type of the generic field of the given column
  let cTyp = c.getColumnImpl()#c.getType[1].getImpl # required to check that `dtype` matches this type
  #echo "CTYP ", cTyp.treerepr
  if cTyp.kind != nnkNilLit:
    let genBranch = getGenericTypeBranch(cTyp)
    if genBranch[1].kind == nnkIdentDefs:
      result = newLit true
    else:
      result = newLit false
  else:
    result = newLit false
  echo result.treerepr

macro getField*(c: typed): untyped =
  # get the correct field name based on the (only!) generic field. Once we have more
  # generic fields (i.e. multiple new types in a single DF), need to dispatch a `case` here
  #echo c.getType.repr
  #echo c.getImpl.repr
  #if c.kind != nnkHiddenDeref:
  #  echo "BEGIN================================================================================"
  #  echo c.treerepr
  #  echo c.getType.treerepr
  #  #echo c.getImpl.treerepr
  #  echo c.getTypeImpl.treerepr
  #  echo c.getTypeInst.treerepr
  #let cTyp = c.getTypeInst.getImpl # required to check that `dtype` matches this type
  let cTyp = c.getColumnImpl()#c.getType[1].getImpl # required to check that `dtype` matches this type
  echo "uuuuhhhhh ", cTyp.treerepr

  #echo "CTYP ", cTyp.treerepr
  if cTyp.kind != nnkNilLit:
    let genBranch = getGenericTypeBranch(cTyp)
    echo genBranch.treerepr, " ??? "
    if genBranch[1].kind != nnkNilLit and genBranch[1].len > 0:
      #echo genBranch.treerepr
      var fn: NimNode
      if genBranch[1].kind == nnkIdentDefs:
        fn = genBranch[1][0]
      else:
        fn = genBranch[1][0][0]
      result = quote do:
        `c`.`fn`
    else:
      #echo genBranch.treerepr
      #error("Invalid branch. This should never happen!")
      result = quote do:
        newTensor[float](0)
  else:
    result = quote do:
      error("Invalid branch. This should never happen!")
      newTensor[float](0)
  echo result.repr

macro getField*(c, dtype: typed): untyped =
  # get the correct field name
  #echo dtype.treerepr
  #echo dtype.getInnerType().treerepr
  let typ0 = dtype.getTypeImpl[1]
  echo "DTYPE ", dtype.getTypeImpl.treerepr
  echo "KIND ", dtype.typeKind
  let fn = genFieldName(typ0) # FieldNames[@[typ0.strVal]]
  let cTyp = c.getTypeInst # required to check that `dtype` matches this type
  echo cTyp.treerepr
  #if cTyp.hasFieldName(fn.strVal):
  result = quote do:
    `c`.`fn`
  echo result.treerepr
  #else:
  #  error("The given column of type " & $cTyp.strVal & " has no generic field of type " & $typ0.strVal)

  #if cTyp.hasFieldName(fn.strVal):
  #  result = quote do:
  #    `c`.`fn`
  #else:
  #  error("The given column of type " & $cTyp.strVal & " has no generic field of type " & $typ0.strVal)


template `%~`*(v: Value): Value = v
proc pretty*(c: ColumnLike): string
proc compatibleColumns*(c1, c2: Column): bool {.inline.}
# just a no-op
template toColumn*[T: ColumnLike](c: T): T = c

func high*(c: Column): int = c.len - 1

func isConstant*(c: Column): bool = c.kind == colConstant

macro printType(t: typed): untyped =
  echo t.getType.treerepr
  echo t.getImpl.treerepr
  echo t.getTypeImpl.treerepr
  echo t.getTypeInst.treerepr

#func len*[T](t: Tensor[T]): int = t.size.int

#macro resolveAlias(t: typed):

template makeColumn(s: typed): untyped =
  #type retTyp = patchColumn(T)
  var result = patchColumn(T)(kind: colGeneric, len: s.len) #
  when typeof(s) is Tensor:
    assignField(result, s)
  else:
    let t = s.toTensor
    assignField(result, t)
  result
  #printType(result)

proc assignData*[T: ColumnLike; U](c: var T, data: Tensor[U]) =
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
                    iCol: t.asType(int),
                    len: t.size)
  elif T is SomeFloat:
    result = Column(kind: colFloat,
                    fCol: t.asType(float),
                    len: t.size)
  elif T is bool:
    result = Column(kind: colBool,
                    bCol: t,
                    len: t.size)
  elif T is string or T is char:
    result = Column(kind: colString,
                    sCol: t.asType(string),
                    len: t.size)
  elif T is Value:
    result = Column(kind: colObject,
                    oCol: t,
                    len: t.size)
  #elif T isnot seq and T isnot Tensor:
  #  ## generate a new type and return it
  #  result = makeColumn(t)

  else: error("The type " & $T & " is not supported!")

proc toColumn*[C: ColumnLike; T](t: Tensor[T], _: typedesc[C]): C =
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
    result = C(kind: colGeneric,
               len: t.size)
    assignData(result, t)

proc toColumn*[T: not SupportedTypes](t: openArray[T]): auto =
  result = makeColumn(t)

proc toColumn*[T: not SupportedTypes](t: Tensor[T]): auto =
  result = makeColumn(t)

type
  ScalarLike = concept x
    (x.float is float) or (x is SupportedTypes)
    #(%~ x) is Value

proc toColumn*[T: SupportedTypes](s: openArray[T]): Column =
  var vals = newTensor[T](s.len)
  for i, x in s:
    vals[i] = x
  result = toColumn(vals)

## XXX: We need a way to declare the following is only allowed for scalar data types. For some reason
## `T: not seq | not array | not Tensor` does not work
proc toColumn*[T: ScalarLike](x: T): Column =
  # also possible to create single row column, but inefficient
  # for `summarize` though there's no way around
  let vals = newTensorWith[T](1, x)
  result = toColumn(vals)

proc constantColumn*[T](val: T, len: int): auto =
  ## creates a constant column based on `val` and its type
  when T is SupportedTypes:
    result = Column(len: len, kind: colConstant, cCol: %~ val)
  #else:
  #  var tmp: Tensor[T]
  #  type retType = patchColumn(typeof(T))
  #  result = retType(len: len, kind: colConstant, cCol: %~ val)

proc constantToFull*[T: ColumnLike](c: T): T =
  ## creates a real constant full tensor column based on a constant column
  if c.kind != colConstant: return c
  withNative(c.cCol, val):
    result = toColumn(newTensorWith[type(val)](c.len, val), T)

proc `[]`*(c: Column, slice: Slice[int]): Column =
  case c.kind
  of colInt: result = toColumn c.iCol[slice.a .. slice.b]
  of colFloat: result = toColumn c.fCol[slice.a .. slice.b]
  of colString: result = toColumn c.sCol[slice.a .. slice.b]
  of colBool: result = toColumn c.bCol[slice.a .. slice.b]
  of colObject: result = toColumn c.oCol[slice.a .. slice.b]
  of colConstant:
    # for constant keep column, only adjust the length to the slice
    result = c
    result.len = slice.b - slice.a + 1
  of colGeneric: raise newException(Exception, "implement me")
  of colNone: raise newException(IndexError, "Accessed column is empty!")

proc newColumn*(kind = colNone, length = 0): Column =
  case kind
  of colFloat: result = toColumn newTensor[float](length)
  of colInt: result = toColumn newTensor[int](length)
  of colString: result = toColumn newTensor[string](length)
  of colBool: result = toColumn newTensor[bool](length)
  of colObject: result = toColumn newTensor[Value](length)
  of colConstant: result = constantColumn(Value(kind: VNull), length)
  of colNone: result = Column(kind: colNone, len: 0)
  of colGeneric: raise newException(Exception, "implement me")

proc newColumnLike*[T: ColumnLike](kind = colNone, length = 0): T =
  case kind
  of colFloat: result = toColumn(newTensor[float](length), T)
  of colInt: result = toColumn(newTensor[int](length), T)
  of colString: result = toColumn(newTensor[string](length), T)
  of colBool: result = toColumn(newTensor[bool](length), T)
  of colObject: result = toColumn(newTensor[Value](length), T)
  # XXX: fix constant
  #of colConstant: result = constantColumn(Value(kind: VNull), length)
  of colGeneric: result = toColumn(newTensor[getGenericFieldType(T)](length), T)
  of colNone, colConstant: result = T(kind: colNone, len: 0)

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

proc toValueKind*(colKind: ColKind): ValueKind =
  case colKind
  of colFloat: result = VFloat
  of colInt: result = VInt
  of colString: result = VString
  of colBool: result = VBool
  of colObject: result = VObject
  of colConstant: result = VObject
  of colNone: result = VNull
  of colGeneric: raise newException(Exception, "implement me")

proc toNimType*(colKind: ColKind): string =
  ## returns the string name of the underlying data type of the column kind
  case colKind
  of colFloat: result = "float"
  of colInt: result = "int"
  of colString: result = "string"
  of colBool: result = "bool"
  of colObject: result = "object"
  of colConstant: result = "constant"
  of colNone: result = "null"
  of colGeneric: result = "generic" # XXX: replace by macro at callsite

template withNativeTensor*(c: ColumnLike,
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
    let `valName` {.inject.} = getField(c)
    body
  of colNone: raise newException(ValueError, "Accessed column is empty!")

proc combinedColKind*(c: seq[ColKind]): ColKind =
  if c.allIt(it == c[0]):
    # all the same, take any
    result = c[0]
  elif c.allIt(it in {colInt, colFloat}):
    # int and float can be combined to float, since we're lenient like that
    result = colFloat
  else:
    # the rest can only be merged via object columns of `Values`.
    result = colObject

template withNative*(c: Column, idx: int,
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
  of colNone, colGeneric: raise newException(ValueError, "Accessed column is empty!")

template withNativeDtype*(c: ColumnLike, body: untyped): untyped =
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
  of colObject, colConstant:
    type dtype {.inject.} = Value
    body
  of colGeneric:
    when hasGenericField(c):
      type dtype {.inject.} = getGenericFieldType(c) ## XXX: how would this work with multi generics?
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
  of colNone, colGeneric: raise newException(ValueError, "Invalid column kind!")

proc asValue*[T](t: Tensor[T]): Tensor[Value] {.noInit.} =
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

proc toTensor*[C: ColumnLike; T](c: C, dtype: typedesc[T],
                                 dropNulls: static bool = false): Tensor[T] =
  ## `dropNulls` only has an effect on `colObject` columns. It allows to
  ## drop Null values to get (hopefully) a valid raw Tensor
  case c.kind
  of colInt:
    when T is int:
      result = c.iCol
    elif T is SomeNumber:
      result = c.iCol.asType(T)
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
      result = c.fCol.asType(T)
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
    result = c.constantToFull.toTensor(dtype, dropNulls)
  of colGeneric:
    when T isnot SupportedTypes:
      result = getField(c)
  of colNone: raise newException(ValueError, "Accessed column is empty!")

proc toTensor*[T](c: Column, slice: Slice[int], dtype: typedesc[T]): Tensor[T] =
  case c.kind
  of colInt:
    when T is int:
      result = c.iCol[slice.a .. slice.b]
    elif T is SomeNumber:
      result = c.iCol[slice.a .. slice.b].asType(T)
  of colFloat:
    when T is float:
      result = c.fCol[slice.a .. slice.b]
    elif T is SomeNumber:
      result = c.fCol[slice.a .. slice.b].asType(T)
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
  of colNone, colGeneric: raise newException(ValueError, "Accessed column is empty!")

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
      #case c.genKind
      #of gkKiloGram: result = c.gKiloGram[idx]
      when T isnot SupportedTypes:
        result = getField(c, dtype)[idx] # XXX: use dtype? means we might not find field!, dtype)
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
      echo "WARN: Accessed column is generic. Treating return value as Value of VString!"
      let val = getField(c)
      result = %~ val[idx]
    of colNone: raise newException(ValueError, "Accessed column is empty!")

proc toObjectColumn*(c: Column): Column =
  ## returns `c` as an object column
  var res = newTensor[Value](c.len)
  withNativeTensor(c, t):
    for idx in 0 ..< c.len:
      res[idx] = %~ (t[idx])
  result = toColumn res

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
    when T isnot SupportedTypes:
      static: echo "TYPE ", $T
      getField(c)[idx] = val

proc `[]=`*[T](c: var Column, slice: Slice[int], t: Tensor[T]) =
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
      c.fCol[sa .. sb] = t.asType(float)
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
  of colNone, colGeneric:
    raise newException(ValueError, "Cannot assign a tensor to an empty column.")

proc `[]=`*(c: var Column, slice: Slice[int], col: Column) =
  let sa = slice.a.int
  let sb = slice.b.int
  if c.compatibleColumns(col) and c.kind != colConstant:
    withNativeDtype(c):
      c[slice] = col.toTensor(dtype)
  elif c.kind == colConstant and col.kind == colConstant:
    if c.cCol == col.cCol: return # nothing to do
    else:
      c = c.constantToFull()
      let c2 = col.constantToFull()
      c[slice] = c2
  else:
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

proc compatibleColumns*(c1, c2: Column): bool {.inline.} =
  if c1.kind == c2.kind: result = true
  elif c1.kind in {colInt, colFloat} and
       c2.kind in {colInt, colFloat}:
    result = true
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
    let kind = combinedColKind(@[c1.kind, c2.kind])
    withDtypeByColKind(kind):
      result = c1[idx1, dtype] == c2[idx2, dtype]

proc toObject*(c: Column): Column {.inline.} =
  case c.kind
  of colObject: result = c
  of colInt: result = toColumn c.iCol.asValue
  of colFloat: result = toColumn c.fCol.asValue
  of colString: result = toColumn c.sCol.asValue
  of colBool: result = toColumn c.bCol.asValue
  of colConstant: raise newException(ValueError, "Accessed column is constant!")
  of colNone, colGeneric: raise newException(ValueError, "Accessed column is empty!")

proc add*(c1, c2: Column): Column =
  ## adds column `c2` to `c1`. Uses `concat` internally.
  if c1.isNil: return c2 # allows to add to an uninitialized column
  if c2.len == 0: return c1
  elif c1.len == 0: return c2
  if c1.kind == c2.kind:
    # just concat directly
    case c1.kind
    of colInt: result = toColumn concat(c1.iCol, c2.iCol, axis = 0)
    of colFloat: result = toColumn concat(c1.fCol, c2.fCol, axis = 0)
    of colBool: result = toColumn concat(c1.bCol, c2.bCol, axis = 0)
    of colString: result = toColumn concat(c1.sCol, c2.sCol, axis = 0)
    of colObject: result = toColumn concat(c1.oCol, c2.oCol, axis = 0)
    of colConstant:
      if c1.cCol == c2.cCol: result = c1 # does not matter which to return
      else: result = add(c1.constantToFull, c2.constantToFull)
    of colNone, colGeneric: doAssert false, "Both columns are empty!"
  elif compatibleColumns(c1, c2):
    # convert both to float
    case c1.kind
    of colInt:
      # c1 is int, c2 is float
      assert c2.kind == colFloat
      result = toColumn concat(c1.iCol.asType(float), c2.fCol, axis = 0)
    of colFloat:
      # c1 is float, c2 is int
      assert c2.kind == colInt
      result = toColumn concat(c1.fCol, c2.iCol.asType(float), axis = 0)
    else: doAssert false, "cannot happen, since not compatible!"
  elif c1.kind == colConstant or c2.kind == colConstant:
    result = add(c1.constantToFull, c2.constantToFull)
  else:
    # convert both columns to Value
    result = toColumn concat(c1.toObject.oCol, c2.toObject.oCol, axis = 0)
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

proc nullColumn*(num: int): Column =
  ## returns an object `Column` with `N` values, which are
  ## all `VNull`
  var nullseq = newTensor[Value](num)
  for i in 0 ..< num:
    nullseq[i] = Value(kind: VNull)
  result = toColumn(nullseq)

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
  result = &"Column of type: {toNimType(c.kind)} with length: {c.len}\n"
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
        "` for dtype of column: " & $(c.kind.toNimType))
    res
