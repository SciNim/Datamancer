import macros

import algorithm, sugar, sequtils, strutils

when (NimMajor, NimMinor) >= (1, 6):
  {.experimental: "overloadableEnums".}

import macrocache, ast_utils

const EnumNames = CacheTable"EnumNameTab"
const TypeNames = CacheTable"ColTypeNames"
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
proc genCombinedTypeStr*(types: seq[string]): string =
  let typClean = types.filterIt(it != "Column" and it notin DtypesAll).deduplicate
  ## FIX UP LOGIC
  result = $(typClean.mapIt(it.dup(removePrefix("Column"))) #.capitalizeAscii)
             .sorted
             .filterIt(it.normalize() notin DtypesAll)
             .join("|"))

proc genCombinedTypeStr*(types: seq[NimNode]): string =
  let typStrs = types.mapIt(it.nodeRepr)
  result = genCombinedTypeStr(typStrs)

proc stripObject(n: NimNode): NimNode =
  result = n
  if result.kind == nnkSym and result.strVal.endsWith(":ObjectType"): ##  XXX: clean up
    var tmp = n.strVal
    tmp.removeSuffix(":ObjectType")
    result = ident(tmp)

proc columnToTypes*(n: NimNode): seq[string] =
  doAssert n.kind in {nnkSym, nnkIdent}
  var r = n.strVal
  r.removePrefix("Column")
  result = r.split("|").filterIt(it.len > 0)

proc getInnerType*(n: NimNode, last = newEmptyNode()): NimNode =
  case n.kind
  of nnkSym:
    let nstr = n.strVal.normalize
    if nstr.len == 1 or "gensym" in nstr or "uniontype" in nstr: # generic or gensymm'd symbol, skip
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
    result = result.stripObject()
  of nnkHiddenDeref, nnkVarTy:
    result = n[0].getInnerType()
  else:
    error("Invalid")

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

macro genTypeEnum*(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types)
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

proc getTypeEnumImpl*(types: seq[string]): NimNode =
  let enumName = "Generic" & genCombinedTypeStr(types) & "Kind"
  if enumName in EnumNames:
    result = EnumNames[enumName]
  else:
    error("The enum of name " & $enumName & " is not known yet. Create it using `genTypeEnum`")

macro getTypeEnum*(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types).mapIt(it.nodeRepr)
  result = getTypeEnumImpl(typs)

proc columnToEnum*(t: NimNode): NimNode =
  ## Turns the given type into the name of the generic enum kind
  result = t.getTypeInst.resolveTypedesc().columnToTypes().getTypeEnumImpl()

proc typesFromEnum*(typ: NimNode): seq[string] =
  ## Turns the given enum name `GenericFoo|BarKind` into a seq of type names
  result = typ.strVal.dup(removePrefix("Generic")).dup(removeSuffix("Kind")).split("|")

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

proc invertType(s: string): NimNode =
  ## Given a type name that was converted to a string by possibly replacing
  ## `[, ]` with `_`, performs the inverse replacement
  if "_" notin s:
    result = ident(s)
  else:
    let spl = s.split("_")
    var r = ""
    for i, el in spl:
      if el.len > 0:
        r.add el
        if i mod 2 == 0: # opening bracket
          result = nnkBracketExpr.newTree(ident(el))
          r.add "["
        else:
          result.add ident(el)
          r.add "]"
    #result = (r)

proc genRecCase*(enumTyp: NimNode): NimNode =
  ## extract types from enum name and
  doAssert enumTyp.kind == nnkSym
  let gkKind = ident(EnumCaseFieldName)
  result = nnkRecCase.newTree()
  result.add nnkIdentDefs.newTree(gkKind, enumTyp, newEmptyNode())
  # now all of branches
  let typs = typesFromEnum(enumTyp)
  for typ in typs:
    let eField = getEnumField(typ)
    let gField = getGenericField(typ)
    result.add nnkOfBranch.newTree(
      eField,
      nnkIdentDefs.newTree(
        gField, nnkBracketExpr.newTree(ident"Tensor", invertType(typ)), newEmptyNode()
      )
    )

macro genType*(enumTyp: typed): untyped =
  let comb = genCombinedTypeStr(typesFromEnum(enumTyp))
  let typName = "Foo" & $comb
  let resTyp = genSym(nskType, typName)
  TypeNames[typName] = resTyp
  TypeToEnumType[typName] = enumTyp
  result = nnkTypeDef.newTree(resTyp, newEmptyNode())
  var rec = nnkRecList.newTree()
  # some common fields
  rec.add nnkIdentDefs.newTree(ident"name", ident"string", newEmptyNode())

  # now add all enum fields
  rec.add genRecCase(enumTyp)

  var obj = nnkObjectTy.newTree(newEmptyNode(), newEmptyNode(), rec)
  result.add obj
  result = nnkTypeSection.newTree(result)

macro getColType*(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types)
  let typName = "Column" & genCombinedTypeStr(typs)
  if typName in TypeNames:
    result = TypeNames[typName]
  else:
    error("The type of name " & $typName & " is not known yet. Create it using `genType`")

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
