import macros

import algorithm, sugar, sequtils, strutils

{.experimental: "overloadableEnums".}

import macrocache
proc contains*(t: CacheTable, key: string): bool =
  for k, val in pairs(t):
    if k == key: return true

const EnumNames = CacheTable"EnumNameTab"
const TypeNames = CacheTable"TypeNames"
const EnumFieldNames = CacheTable"EnumFieldTab"
const GenericFieldNames = CacheTable"GenericFieldTab"
const TypeToEnumType = CacheTable"TypeToEnumType"
const EnumCaseFieldName = "gkKind"

proc nodeRepr(n: NimNode): string =
  case n.kind
  of nnkIdent, nnkSym: result = n.strVal
  else: result = n.toStrLit.strVal.multiReplace([("[", "_"), ("]", "_")])

proc genCombinedTypeStr*(types: seq[string]): string =
  let typClean = types.filterIt(it != "Column")
  result = $(typClean.mapIt(it.dup(removePrefix("Column")).capitalizeAscii).sorted.join("|"))

proc genCombinedTypeStr*(types: seq[NimNode]): string =
  let typStrs = types.mapIt(it.nodeRepr)
  result = genCombinedTypeStr(typStrs)

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

proc bracketToSeq(types: NimNode): seq[NimNode] =
  doAssert types.kind == nnkBracket
  result = newSeq[NimNode]()
  for typ in types:
    result.add getInnerType(typ)

func enumFieldName(s: string): string = "gk" & s.capitalizeAscii
func genericFieldName(s: string): string = "g" & s.capitalizeAscii

proc getEnumField(typ: string): NimNode =
  if typ in EnumFieldNames:
    result = EnumFieldNames[typ]
  else:
    # generate and add to tab
    let name = enumFieldName(typ)
    result = ident(name)
    EnumFieldNames[typ] = result

proc getEnumField(typ: NimNode): NimNode = typ.nodeRepr.getEnumField()

proc getGenericField(typ: string): NimNode =
  if typ in GenericFieldNames:
    result = GenericFieldNames[typ]
  else:
    # generate and add to tab
    let name = genericFieldName(typ)
    result = ident(name)
    GenericFieldNames[typ] = result

proc getGenericField(typ: NimNode): NimNode = typ.nodeRepr.getEnumField()

macro genTypeEnum(types: varargs[typed]): untyped =
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
  echo result.repr

macro getTypeEnum(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types)
  let enumName = "Generic" & genCombinedTypeStr(typs) & "Kind"
  if enumName in EnumNames:
    result = EnumNames[enumName]
  else:
    error("The enum of name " & $enumName & " is not known yet. Create it using `genTypeEnum`")

proc typesFromEnum(typ: NimNode): seq[string] =
  result = typ.strVal.dup(removePrefix("Generic")).dup(removeSuffix("Kind")).split("|")

proc kindToField(n: NimNode, toReplace, replace: NimNode): NimNode =
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

proc genCaseStmt(n, knd, enumTyp, body: NimNode): NimNode =
  ## extract types from enum name and
  ## `n` is the symbol for which to access the field from
  doAssert enumTyp.kind == nnkSym
  let typs = typesFromEnum(enumTyp)
  result = nnkCaseStmt.newTree(nnkDotExpr.newTree(n, ident(EnumCaseFieldName)))
  for typ in typs:
    let enumF = EnumFieldNames[typ]
    echo "typ ", typ.repr
    let genericF = GenericFieldNames[typ]
    var bodyLoc = kindToField(body, knd, genericF)
    #bodyLoc = quote do:
    #  when
    echo "BODY LOC ", bodyLoc.treerepr

    result.add nnkOfBranch.newTree(enumF, bodyLoc)
  echo "CASE ", result.repr

proc resolveGenerics(n: NimNode): NimNode =
  echo "RESOLVE ", n.typeKind, " is ", n.treerepr
  echo "RESOLVE ", n.getTypeImpl.treerepr, " is "
  echo "RESOLVE ", n.getTypeInst.treerepr, " is "
  if n.typeKind == ntyTypeDesc:
    # safe to call `getTypeImpl`
    echo "is generic : ", n.treerepr
    result = n.getTypeInst[1]
    echo "RESULT ", result.typeKind
  else:
    result = n

proc isEnumType(t: NimNode): bool =
  if t.typeKind == ntyTypeDesc:
    result = t.resolveGenerics().isEnumType
  else:
    result = t.typeKind == ntyEnum

macro withCaseStmt(n, knd: untyped, typ: typed, body: untyped): untyped =
  ## extract types from enum name and
  # check if `typ` is an enum type already, if not extract it
  var typ = typ.resolveGenerics()
  if not typ.isEnumType:
    typ = TypeToEnumType[typ.strVal]
  doAssert typ.kind == nnkSym
  result = genCaseStmt(n, knd, typ, body)
  echo result.repr

proc genRecCase(enumTyp: NimNode): NimNode =
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
    result.add nnkOfBranch.newTree(eField, nnkIdentDefs.newTree(gField, ident(typ), newEmptyNode()))
  echo result.repr

macro genType(enumTyp: typed): untyped =
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

macro getType(types: varargs[typed]): untyped =
  let typs = bracketToSeq(types)
  let typName = "Foo" & genCombinedTypeStr(typs)
  if typName in TypeNames:
    result = TypeNames[typName]
  else:
    error("The type of name " & $typName & " is not known yet. Create it using `genType`")


type
  Bar = object

genTypeEnum(float, int)
import unchained

genTypeEnum(KiloGram, Meter)
genTypeEnum(Bar, Meter)

genType(getTypeEnum(KiloGram, Meter))
genType(getTypeEnum(Bar, Meter))

let gk = gkKiloGram
#withCaseStmt(gk, getTypeEnum(KiloGram, Meter)):
#  echo "I am : ", gk


proc returnVal*[T; U](t: T, dtype: typedesc[U]): U =
  withCaseStmt(t, gk, T):
    when U is typeof(t.gk):
      result = t.gk
    else:
      raise newException(ValueError, "Invalid types ! " & $U & " for " & $typeof(t.gk))

for field in getTypeEnum(Meter, KiloGram):
  echo field

var f = getType(KiloGram, Meter)(gkKind: gkKiloGram, gKiloGram: 1.1.kg)
var g = getType(Bar, Meter)(gkKind: gkMeter, gMeter: 2.5.m)

echo returnVal(f, KiloGram)
echo returnVal(f, Meter)
echo returnVal(g, Meter)

when false:
  dumpTree:
    case gkKind
    of gkKiloGram: body
    of gkMeter: body

    type
      Foo = object
        name: string
        case gkKind: ColumnGenericKind
        of gkInt: gInt: int
        of gkFloat: gFloat: float
