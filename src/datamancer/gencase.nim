import macros

import algorithm, sugar, sequtils, strutils

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
    result = result.stripObject()
  of nnkHiddenDeref, nnkVarTy:
    result = n[0].getInnerType()
  #of nnkHiddenStdConv:
  #  doAssert n[0].kind == nnkBracket
  #  result =
  else:
    echo n.treerepr
    error("Invalid")

proc resolveGenerics*(n: NimNode): NimNode =
  #echo "RESOLVE ", n.typeKind, " is ", n.treerepr
  #echo "RESOLVE ", n.getTypeImpl.treerepr, " is "
  #echo "RESOLVE ", n.getTypeInst.treerepr, " is "
  #echo "RESOLVE ", n.getType.treerepr, " is "
  #echo "RESOLVE ", n.getImpl.treerepr, " is "
  if n.typeKind == ntyTypeDesc:
    # safe to call `getTypeImpl`
    result = n.getTypeInst[1].resolveGenerics
  elif n.typeKind == ntyRef: ## `Columns` are all ref types!
    let typ = n.getTypeImpl
    doAssert typ.kind == nnkRefTy
    result = typ[0].stripObject
  else:
    error("Invalid!! " & $n.treerepr)
  echo "RESULT Resolve Generics ", result.repr

proc bracketToSeq*(types: NimNode): seq[NimNode] =
  doAssert types.kind == nnkBracket
  result = newSeq[NimNode]()
  for typ in types:
    echo typ.treerepr
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
  for f, v in EnumFieldNames:
    echo "ENUM FIELD NAMES ", f, " from ", typ

proc getEnumField*(typ: NimNode): NimNode = typ.nodeRepr.getEnumField()

proc resolveTypedesc(n: NimNode): NimNode =
  doAssert n.typeKind == ntyTypeDesc
  doAssert n.kind == nnkBracketExpr
  doAssert n[0].kind in {nnkIdent, nnkSym} and n[0].strVal.normalize == "typedesc"
  result = n[1]

macro getEnumField*(typ: typed): untyped = typ.getTypeInst.resolveTypedesc.getEnumField()

proc getGenericField*(typ: string): NimNode =
  echo "type ", typ
  if typ in GenericFieldNames:
    result = GenericFieldNames[typ]
  else:
    # generate and add to tab
    let name = genericFieldName(typ)
    echo "GENERATED ", name, " from ", typ
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
  echo "TYPS ", typs.repr
  for typ in typs:
    let enumField = getEnumField(typ)
    body.add enumField
  result.add body

  # wrap in type section
  result = nnkTypeSection.newTree(result)
  echo result.repr

macro getTypeEnum*(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types)
  let enumName = "Generic" & genCombinedTypeStr(typs) & "Kind"
  if enumName in EnumNames:
    result = EnumNames[enumName]
  else:
    error("The enum of name " & $enumName & " is not known yet. Create it using `genTypeEnum`")

#proc strTo

proc typesFromEnum*(typ: NimNode): seq[string] =
  #case typ.typeKind
  #of ntyTypeDesc:
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
    #echo "typ ", typ.repr
    let genericF = GenericFieldNames[typ]
    var bodyLoc = kindToField(body, knd, genericF)
    #bodyLoc = quote do:
    #  when
    #echo "BODY LOC ", bodyLoc.treerepr

    result.add nnkOfBranch.newTree(enumF, bodyLoc)
  #echo "CASE ", result.repr

macro fieldToType*(field: untyped): untyped =
  #echo c.treerepr
  #echo c.getTypeInst.treerepr
  #let typ = resolveGenerics(c)
  #echo typ.repr
  echo field.treerepr
  ## XXX: fix me, replace by proper logic that replaces the given field name
  ## by the correct type! e.g. `gKiloGram` -> `KiloGram`, `gMeasurement_float_` -> `Measurement[float]` etc
  result = ident(field.strVal[1 ..< field.strVal.len])
  echo "RESULT ", result.repr
  #echo field.treerepr
  #if true: quit()

proc isEnumType*(t: NimNode): bool =
  if t.typeKind == ntyTypeDesc:
    result = t.resolveGenerics().isEnumType
  else:
    result = t.typeKind == ntyEnum

macro withCaseStmt*(n, knd: untyped, typ: typed, body: untyped): untyped =
  ## extract types from enum name and
  # check if `typ` is an enum type already, if not extract it
  var typ = typ.resolveGenerics()
  echo typ.treerepr
  if not typ.isEnumType:
    if typ.strVal notin TypeToEnumType:
      doAssert typ.strVal == "Column" # means we're looking at a column. In this case do nothing
      return nnkDiscardStmt.newTree(newEmptyNode())
    typ = TypeToEnumType[typ.strVal]
  doAssert typ.kind == nnkSym
  result = genCaseStmt(n, knd, typ, body)
  echo "=============== withCaseStmt ===============\n", result.repr

proc invertType(s: string): NimNode =
  ## Given a type name that was converted to a string by possibly replacing
  ## `[, ]` with `_`, performs the inverse replacement
  if "_" notin s:
    result = ident(s)
  else:
    let spl = s.split("_")
    echo spl
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
  echo result.repr

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
  echo result.treerepr
  echo result.repr

macro getColType*(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types)
  let typName = "Column" & genCombinedTypeStr(typs)
  if typName in TypeNames:
    result = TypeNames[typName]
  else:
    error("The type of name " & $typName & " is not known yet. Create it using `genType`")

proc getTensor*[T; U](t: T, dtype: typedesc[U]): U {.inline.} =
  withCaseStmt(t, gk, T):
    when U is typeof(t.gk):
      result = t.gk
    else:
      raise newException(ValueError, "Invalid types ! " & $U & " for " & $typeof(t.gk))

proc setVal*[T; U](t: var T, idx: int, val: U) {.inline.} =
  withCaseStmt(t, gk, T):
    when Tensor[U] is typeof(t.gk):
      t.gk[idx] = val
    else:
      raise newException(ValueError, "Invalid types ! " & $U & " for " & $typeof(t.gk))

proc setTensor*[T; U](t: var T, toSet: U) {.inline.} =
  withCaseStmt(t, gk, T):
    when U is typeof(t.gk):
      t.gk = toSet
    else:
      raise newException(ValueError, "Invalid types ! " & $U & " for " & $typeof(t.gk))
