import macros

import algorithm, sugar, sequtils, strutils

when (NimMajor, NimMinor) >= (1, 6):
  {.experimental: "overloadableEnums".}

import macrocache, ast_utils

const EnumNames = CacheTable"EnumNameTab"
const TypeNames = CacheTable"ColTypeNames"
const TypeImpls = CacheTable"ColTypeImpls"
# add default Column
static: TypeNames["Column"] = ident"Column"
const EnumFieldNames = CacheTable"EnumFieldTab"
const GenericFieldNames = CacheTable"GenericFieldTab"
const TypeToEnumType = CacheTable"TypeToEnumType"
const EnumCaseFieldName = "gkKind"

proc nodeRepr*(n: NimNode): string =
  case n.kind
  of nnkIdent, nnkSym: result = n.strVal
  else: result = n.toStrLit.strVal.multiReplace([("[", "_"), ("]", "_")])

from formulaExp import DtypesAll

proc columnToTypes*(s: string): seq[string] =
  var s = s
  s.removePrefix("Column")
  result = s.split("|").filterIt(it.len > 0 and it notin DtypesAll)

proc columnToTypes*(n: NimNode): seq[string] =
  var r = n.nodeRepr
  result = columnToTypes(r)

proc genCombinedTypeStr*(types: seq[string]): string =
  var typs = newSeq[string]()
  for typ in types:
    if typ.startsWith("Column"):
      typs.add columnToTypes(typ)
    elif typ notin DtypesAll:
      typs.add typ
  result = $(typs.deduplicate.sorted.join("|"))

proc genCombinedTypeStr*(types: seq[NimNode]): string =
  let typStrs = types.mapIt(it.nodeRepr)
  result = genCombinedTypeStr(typStrs)

proc genColumnTypeStr*(types: seq[NimNode]): string =
  result = "Column" & types.genCombinedTypeStr()

proc stripObject(n: NimNode): NimNode =
  result = n
  if result.kind == nnkSym and result.strVal.endsWith(":ObjectType"): ##  XXX: clean up
    var tmp = n.strVal
    tmp.removeSuffix(":ObjectType")
    result = ident(tmp)


proc getInnerType*(n: NimNode, stop = false): NimNode
proc resolveTypeDescNode(n: NimNode): NimNode =
  case n.kind
  of nnkSym: result = n.getTypeInst.getInnerType()
  of nnkBracketExpr:
    if n[0].kind in {nnkIdent, nnkSym} and n[0].strVal.normalize == "typedesc":
      # still a typedesc, one further
      result = n[1].getInnerType(stop = true)
    else:
      # the type we want
      result = n
  else:
    error("Invalid " & $n.treerepr)

proc resolveRef(n: NimNode): NimNode =
  case n.kind
  of nnkSym: result = n # if it's a refty and a symbol, done
  of nnkRefTy:
    doAssert n[0].kind in {nnkIdent, nnkSym} and n[0].strVal.normalize == "ref", "was " & $n.treerepr
    result = n[1].getInnerType()
  else:
    error("Invalid " & $n.treerepr)

proc resolveSeq(n: NimNode): NimNode =
  case n.kind
  of nnkSym: result = n.getTypeImpl.getInnerType() # if it's a refty and a symbol, done
  of nnkBracketExpr:
    doAssert n[0].kind in {nnkIdent, nnkSym} and n[0].strVal.normalize == "seq", "was " & $n.treerepr
    result = n[1] # inner type of `seq` is what we want
  else:
    error("Invalid " & $n.treerepr)

proc resolveGenericInst(n: NimNode, stop: bool): NimNode =
  case n.kind
  of nnkSym: result = n.getType.getInnerType() # if it's a refty and a symbol, done
  of nnkBracketExpr:
    if stop: #
      # want this type. We came here from `resolveTypeDesc` and already took inner type
      result = n
    else:
      doAssert n[0].kind in {nnkIdent, nnkSym}, "was " & $n.treerepr
      result = n[1] # this is what we want
  else:
    error("Invalid " & $n.treerepr)

# for simple types make sure to call `getType` if it's a `const` of some distinct version
proc resolveInt(n: NimNode): NimNode =
  result = n.getType

proc resolveFloat(n: NimNode): NimNode =
  result = n.getType

proc resolveString(n: NimNode): NimNode =
  result = n.getType

proc resolveObject(n: NimNode): NimNode =
  result = n # just the type

proc resolveDistinct(n: NimNode): NimNode =
  result = n # just the type

proc resolveAlias(n: NimNode): NimNode =
  result = n # just the type

proc resolveArray(n: NimNode): NimNode =
  ## nnkBracketExpr
  ##   Sym "array"
  ##   Infix
  ##     Ident ".."
  ##     IntLit 0
  ##     IntLit 2
  ##   Sym "int"
  result = n[^1] # array has type as last child

proc getInnerType*(n: NimNode, stop = false): NimNode =
  case n.typeKind
  of ntyTypeDesc: result = n.resolveTypeDescNode()
  of ntyRef: result = n.resolveRef()
  of ntySequence: result = n.resolveSeq()
  of ntyGenericInst: result = n.resolveGenericInst(stop)
  of ntyInt .. ntyInt64, ntyUint .. ntyUint64: result = n.resolveInt()
  of ntyFloat: result = n.resolveFloat()
  of ntyString: result = n.resolveString()
  of ntyObject: result = n.resolveObject()
  of ntyDistinct: result = n.resolveDistinct()
  of ntyAlias: result = n.resolveAlias()
  of ntyArray: result = n.resolveArray()
  else: error("Invalid: " & $n.typeKind & " for: " & $n.treerepr)

macro innerType*(t: typed): untyped =
  ## Returns the inner type of the typed symbol from a proc or the
  ## symbol of the column type
  result = t.getInnerType()

proc resolveGenerics*(n: NimNode): NimNode =
  if n.typeKind == ntyTypeDesc:
    # safe to call `getTypeImpl`
    result = n.getTypeInst[1].resolveGenerics
  elif n.typeKind == ntyRef: ## `Columns` are all ref types!
    let typ = n.getTypeImpl
    doAssert typ.kind == nnkRefTy
    result = typ[0].stripObject
  else:
    error("Invalid node kind " & $n.kind & " encountered when trying to " &
      "resolve generic type for node: " & n.repr)

proc bracketToSeq*(types: NimNode): seq[NimNode] =
  doAssert types.kind == nnkBracket
  result = newSeq[NimNode]()
  for typ in types:
    case typ.kind
    of nnkHiddenStdConv:
      doAssert typ[0].kind == nnkEmpty and typ[1].kind == nnkBracket
      result.add bracketToSeq(typ[1])
    of nnkBracket:
      result.add bracketToSeq(typ)
    else:
      result.add getInnerType(typ)

func enumFieldName*(s: string): string =
  var s = s
  s.removePrefix("Column")
  result = "gk" & s.capitalizeAscii

func genericFieldName*(s: string): string =
  var s = s
  s.removePrefix("Column")
  result = "g" & s.capitalizeAscii

proc getEnumField*(typ: string): NimNode =
  if typ in EnumFieldNames:
    result = EnumFieldNames[typ]
  else:
    # generate and add to tab
    let name = enumFieldName(typ)
    result = ident(name)
    EnumFieldNames[typ] = result

proc getEnumField*(typ: NimNode): NimNode = typ.nodeRepr.getEnumField()

proc resolveTypedesc(n: NimNode): NimNode =
  doAssert n.typeKind == ntyTypeDesc
  doAssert n.kind == nnkBracketExpr
  doAssert n[0].kind in {nnkIdent, nnkSym} and n[0].strVal.normalize == "typedesc"
  result = n[1]

proc columnToEnum*(t: NimNode): NimNode
macro enumField*(colTyp, typ: typed): untyped =
  ## Generates a fully specified enum field, i.e.
  ##
  ## `GenericFoo|BarKind.gkFoo`
  let enumType = colTyp.columnToEnum()
  let enumField = typ.getTypeInst.resolveTypedesc.getEnumField()
  result = nnkDotExpr.newTree(enumType, ident(enumField.strVal))

proc getGenericField*(typ: string): NimNode =
  if typ in GenericFieldNames:
    result = GenericFieldNames[typ]
  else:
    # generate and add to tab
    let name = genericFieldName(typ)
    result = ident(name)
    GenericFieldNames[typ] = result

proc getGenericField*(typ: NimNode): NimNode = typ.nodeRepr.getGenericField()

proc genTypeEnum*(typs: seq[NimNode]): NimNode =
  let enumName = "Generic" & genCombinedTypeStr(typs) & "Kind"
  var enumSym: NimNode
  if enumName in EnumNames:
    enumSym = EnumNames[enumName]
  else:
    enumSym = genSym(nskType, enumName)
    EnumNames[enumName] = enumSym

  result = nnkTypeDef.newTree(enumSym, newEmptyNode())
  var body = nnkEnumTy.newTree(newEmptyNode())
  for typ in typs:
    let enumField = getEnumField(typ)
    body.add enumField
  result.add body

  # wrap in type section
  result = nnkTypeSection.newTree(result)

proc getTypeEnum*(types: seq[string]): NimNode =
  let enumName = "Generic" & genCombinedTypeStr(types) & "Kind"
  if enumName in EnumNames:
    result = EnumNames[enumName]
  else:
    error("The enum of name " & $enumName & " is not known yet. Create it using `genTypeEnum`")

proc columnToEnum*(t: NimNode): NimNode =
  ## Turns the given type into the name of the generic enum kind
  result = t.getTypeInst.resolveTypedesc().columnToTypes().getTypeEnum()

proc getEnumName*(n: NimNode): NimNode =
  case n.kind
  of nnkTypeSection:
    doAssert n[0].kind == nnkTypeDef
    result = n[0][0].getEnumName()
  of nnkIdent, nnkSym:
    result = n
  else:
    error("Invalid node: " & $n.repr)

proc typesFromEnum*(typ: NimNode): seq[string] =
  ## Turns the given enum name `GenericFoo|BarKind` into a seq of type names
  result = typ.getEnumName.strVal().dup(removePrefix("Generic")).dup(removeSuffix("Kind")).split("|")

proc kindToField*(n: NimNode, toReplace, replace: NimNode): NimNode =
  ## Replaces the usage of `toReplace` by `replace` in the node `n`.
  ## This is used to replace usages of the enum *kind* field by the
  ## correct *generic* field
  case n.kind
  of nnkIdent, nnkSym:
    if n.nodeRepr == toReplace.nodeRepr: result = replace
    else: result = n
  else:
    if n.len == 0: result = n
    else:
      result = newTree(n.kind)
      for ch in n:
        result.add kindToField(ch, toReplace, replace)

proc genCaseStmt*(n, knd, enumTyp, body: NimNode): NimNode =
  ## extract types from enum name and
  ## `n` is the symbol for which to access the field from
  doAssert enumTyp.kind == nnkSym
  let typs = typesFromEnum(enumTyp)
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(n, ident(EnumCaseFieldName)))
  for typ in typs:
    let enumF = EnumFieldNames[typ]
    let genericF = GenericFieldNames[typ]
    var bodyLoc = kindToField(body, knd, genericF)
    result.add nnkOfBranch.newTree(enumF, bodyLoc)

macro fieldToType*(field: untyped): untyped =
  ## XXX: fix me, replace by proper logic that replaces the given field name
  ## by the correct type! e.g. `gKiloGram` -> `KiloGram`, `gMeasurement_float_` -> `Measurement[float]` etc
  result = ident(field.strVal[1 ..< field.strVal.len])

proc isEnumType*(t: NimNode): bool =
  if t.typeKind == ntyTypeDesc:
    result = t.resolveGenerics().isEnumType
  else:
    result = t.typeKind == ntyEnum

macro withCaseStmt*(n, knd: untyped, typ: typed, body: untyped): untyped =
  ## extract types from enum name and
  # check if `typ` is an enum type already, if not extract it
  var typ = typ.resolveGenerics()
  if not typ.isEnumType:
    if typ.strVal notin TypeToEnumType:
      doAssert typ.strVal == "Column" # means we're looking at a column. In this case do nothing
      return nnkDiscardStmt.newTree(newEmptyNode())
    typ = TypeToEnumType[typ.strVal]
  doAssert typ.kind == nnkSym
  result = genCaseStmt(n, knd, typ, body)

proc genRecCase*(enumTyp: NimNode, typs: seq[NimNode]): NimNode =
  ## Generate the `nnkRecCase` part of the resulting type using the given
  ## name for the generic enum kind that serves as the discriminator field and
  ## all corresponding types.
  doAssert enumTyp.kind == nnkSym
  let gkKind = ident(EnumCaseFieldName)
  result = nnkRecCase.newTree()
  result.add nnkIdentDefs.newTree(gkKind, enumTyp, newEmptyNode())
  # now all of branches
  for typ in typs:
    let eField = getEnumField(typ)
    let gField = getGenericField(typ)
    result.add nnkOfBranch.newTree(
      eField,
      nnkIdentDefs.newTree(
        gField, nnkBracketExpr.newTree(ident"Tensor", typ), newEmptyNode()
      )
    )

macro colType*(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types)
  let typName = "Column" & genCombinedTypeStr(typs)
  if typName in TypeNames:
    result = TypeNames[typName]
  else:
    error("The type of name " & $typName & " is not known yet. Create it using `defColumn`")

proc getTensor*[C; U](c: C, dtype: typedesc[U]): U {.inline.} =
  withCaseStmt(c, gk, C):
    when U is typeof(c.gk):
      result = c.gk
    else:
      raise newException(ValueError, "Invalid types ! " & $U & " for " & $typeof(c.gk))

proc setVal*[C; U](c: var C, idx: int, val: U) {.inline.} =
  withCaseStmt(c, gk, C):
    when Tensor[U] is typeof(c.gk):
      c.gk[idx] = val
    else:
      raise newException(ValueError, "Invalid types ! " & $U & " for " & $typeof(c.gk))

proc setTensor*[C; U](c: var C, toSet: U) {.inline.} =
  withCaseStmt(c, gk, C):
    when U is typeof(c.gk):
      c.gk = toSet
    else:
      raise newException(ValueError, "Invalid types ! " & $U & " for " & $typeof(c.gk))
