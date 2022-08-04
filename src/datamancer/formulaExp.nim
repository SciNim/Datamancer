import macros, sequtils, strformat, options, sets, tables, algorithm, strutils
import formulaNameMacro

import column, value

type
  AssignKind* = enum
    byIndex, ## assign by index
    byTensor, ## by tensor
    byCustom ## custom variable declaration in preface
  ## replace occurence of nnkAccQuote, nnkCallStrLit, nnkBracketExpr(df) by:
  ReplaceByKind = enum
    rbIndex ## by call to tensor index, `tT[idx]`, in a `for` loop
    rbElement ## by single element, `tIdx` in a `forEach` call
    rbColumn ## by full tensor (df column), `colT` in `<<` formula
  ## `impure` in the context of `FormulaNode` refers to evaluation requiring
  ## a data frame. Pure formulas represent raw expressions that evaluate to
  ## a simple `Value`
  FormulaKind* = enum
    fkNone = "none" ## default value for uninitialized formula / no formula kind at CT yet
    fkVariable = "" ## Nim variable as `Value`, pure
    fkAssign = "<-" ## assignment op, pure
    fkVector = "~" ## map operation, impure
    fkScalar = "<<" ## reduce operation, impure
  ## either: `t in df["foo", int]`
  ## or: `t = df["foo", int]`
  Assign* = object
    asgnKind*: AssignKind
    node*: NimNode ## the exact node that will be replaced by this `Assign` instance
                   ## In case of `byCustom`, just the user input that will be inserted again
    element*: NimNode # e.g. `t`
    tensor*: NimNode # either `t` or `t_T` if `elmenent` used
    col*: NimNode # name of the column
    colType*: NimNode # e.g. `float`
    resType*: NimNode # the resulting type of the computation `Assign` is ``involved`` in!
    transformed*: NimNode # an (optional) user defined transformation. Wraps the `df[<col>, <dtype>]` call
  Preface* = object
    args*: seq[Assign]
    resType*: NimNode # likely combined return type. May be empty.
                      ## XXX: do we need this? or repurpose `FormulaCT` field instead?
  FormulaCT* = object
    funcKind*: FormulaKind
    preface*: Preface
    typeHint*: TypeHint # the actual type hint given in the formula
    resType*: NimNode # e.g. `ident"float"`
    name*: NimNode # name of the formula -> refers to new column / assignment name
    rawName*: string # name of the formula body as lisp
    loop*: NimNode # loop needs to be patched to remove accented quotes etc
    generateLoop*: bool # only of interest for `fkScalar`. Means instead of generating a
                        # single `res = %~ <user body>` statement, generate a for loop w/ accumulation
    df*: Option[NimNode] # the (optional) DataFrame from which to deduce the type of the closure argument DF
    dfType*: Option[NimNode] # the extracted/default type of the `DataFrame` argument to the closure
    colResType*: NimNode # the returned `Column` type of a `fkVektor` closure (usually `Column`)
  ## `Lift` stores a node which needs to be lifted out of a for loop, because it performs a
  ## reducing operation on a full DF column. It will be replaced by `liftedNode` in the loop
  ## body.
  Lift* = object
    toLift*: NimNode
    liftedNode*: NimNode

  ## The `TypeHint` and `HeuristicType` are only used for the shortform of the
  ## `Formula` syntax using `f{}`.
  ##
  ## In the general shortform `Formula` syntax `f{}` a `TypeHint` is of the form
  ## `f{float -> int: <operation>}`, where the first value is the type we use to read the
  ## DF tensors and the second the output datatype of the operation.
  ##
  ## If a `TypeHint` is found in a formula, we do attempt to heuristically determine
  ## sensible data types.
  TypeHint* = object
    inputType*: Option[NimNode]
    resType*: Option[NimNode]

  ## `HeuristicType` stores the input and output types of a formula constructed using the
  ## `f{}` syntax based on simple heuristic rules about the presence of certain operators
  ## and typed symbols (e.g. proc calls, literals). They are only used if no `TypeHint`
  ## is supplied.
  HeuristicType* = TypeHint

  ## `FormulaTypes` finally is the type used for input and output of the formula
  ## construction. Here the types *must* be set, otherwise it's a CT error (which happens
  ## if we cannot deduce a type and no hints are given)
  FormulaTypes* = object
    inputType*: NimNode
    resType*: NimNode

## Idents used for the generated code
const
  InIdent = "in"
  ResIdent = "res"
  ResultIdent = "result"
  RIdent = "r"
  DfIdent = "df"
  IdxIdent = "idx"
  ColIdent* = "Column"
  ValueIdent = "Value"
  InputDF* = "InputDataFrame" # the data frame given as input to deduce types from

const Dtypes* = ["float", "int", "string", "bool", "Value"]
const DtypesAll* = ["float", "float64", "int", "int64", "string", "bool", "Value"]

const DtypeOrderMap* = {
  "Value" : 1,
  "Tensor[Value]" : 2,
  "Tensor[T]" : 3,
  "T" : 4,
  "Tensor[string]" : 100,
  "string" : 110,
  "Tensor[int]" : 120,
  "int" : 130,
  "Tensor[int64]" : 140,
  "int64" : 150,
  "Tensor[float]" : 160,
  "float" : 170,
  "Tensor[float64]" : 180,
  "float64" : 190,
  "Tensor[bool]" : 1000,
  "bool" : 1100 # if something  can be done with `bool`, take that
}.toTable()
const DtypeOrderMapKeys = toSeq(DtypeOrderMap.keys())

proc toStrType*(n: NimNode): NimNode =
  case n.kind
  of nnkIntLit .. nnkUInt64Lit: result = ident "int"
  of nnkFloatLit .. nnkFloat128Lit: result = ident "float"
  of nnkStrLit: result = ident "string"
  of nnkIdent, nnkSym:
    if n.strVal in ["true", "false"]: result = ident "bool"
    else: result = ident(n.repr)
  of nnkBracketExpr:
    if n.typeKind == ntyTypeDesc and n[0].strVal.normalize == "typedesc":
      result = ident(n[1].repr)
    else:
      result = ident(n.repr)
  else: result = ident(n.repr)

proc sortTypes*(s: seq[string]): seq[string] =
  ## sorts the types according to our own "priority list"
  var ids = newSeq[float](s.len)
  for i, el in s:
    if el in DtypeOrderMap:
      ids[i] = DtypeOrderMap[el].float
    else:
      # Note: here the priority of other types is the absolute lowest. That is because
      # this `sortTypes` is called in the `assignType` calls during `determineTypesImpl`.
      # There we just want to use other types than known if they are not ambiguous.
      # In the `sortTypes` below though we compare possible different output types and
      # want to keep the possible return type of a not supported type
      ids[i] = 0.0 # every other type has lower priority
  result = zip(s, ids).sortedByIt(it[1]).mapIt(it[0])

proc sortTypes*(heuristic, deduced: seq[string]): seq[string] =
  ## sorts the types according to our own "priority list"
  ##
  ## This version takes a heuristic and a deduced type sequence. The idea is
  ## that a heuristic may still contain useful information. But not all heuristic
  ## information shall be allowed to override the deduced information. Where the
  ## heuristics makes lossy assumptions (math operations are float and not int)
  ## the deduced one should have preference. Therefore the type order map contains
  ## staggered values, such that taking `div 10` of them still provides overriding
  ## power for some types (against Value and not predefined ones), but float div 10
  ## yields something smaller than int for example.
  ##
  ## The exact values are not fully thought out yet!
  var ids = newSeq[float]()
  for i, el in heuristic:
    if el in DtypeOrderMap:
      ids.add DtypeOrderMap[el].float / 10.0
    else:
      ids.add 20.0 # every other type has lower priority
  for i, el in deduced:
    if el in DtypeOrderMap:
      ids.add DtypeOrderMap[el].float
    else:
      ids.add 20.0 # every other type has lower priority
  result = zip(concat(heuristic, deduced), ids).sortedByIt(it[1]).mapIt(it[0])

proc sortTypes*(s: seq[NimNode]): seq[string] =
  result = s.mapIt(it.strVal).sortTypes()

proc toStr(n: seq[NimNode]): seq[string] =
  for ch in n:
    if ch.kind != nnkEmpty:
      result.add ch.repr

proc sortTypes*(heuristic, deduced: seq[NimNode]): seq[string] =
  ## sorts the types according to our own "priority list"
  result = sortTypes(heuristic.toStr,
                     deduced.toStr)

proc accumulateTypes*(p: Preface): seq[string] =
  ## Returns a sorted sequence of all distinct types other than `DtypesAll` found in
  ## the preface input and output types.
  ##
  ## This is used to determine the required `ColumnFoo|Bar|Baz` type of the formula
  ## purely based on the used input / output types to not require the data frame
  ## argument to formulas in many cases.
  for a in p.args:
    let aC = a.colType.strVal
    if aC notin DtypesAll:
      result.add aC
    ## XXX: we should *not* accumulate the result type of each individual column, as those
    ## may be intermediate. Only the read types & the resulting type of the formula. Consider
    ## the following formula:
    ##
    ## `f{ idx("a").int8 in {1'i8, 3, 5, 7} }`
    ##
    ## here `int8` will be the `resType` of `"a"`, but it's not relevant for a `Column`!
    ##
    ## Instead of combining all `resType` we now accumulate the hopefully correct last type
    ## using `heuristicType` as a second return value in `determineTypesImpl`.
    #let aR = a.resType.strVal
    #if aR notin DtypesAll:
    #  result.add aR
  result = result.sortTypes()

proc isColumnType*(n: NimNode): bool =
  case n.kind
  of nnkBracketExpr:
    if n[0].kind in {nnkSym, nnkIdent} and n[0].strVal == "Tensor":
      result = true
  of nnkSym, nnkIdent:
    if n.strVal.startsWith("Tensor"):
      result = true
  else: discard

proc checkIdent(n: NimNode, s: string): bool =
  result = n.len > 0 and n[0].kind == nnkIdent and n[0].strVal == s

proc extractCall*(stmts: NimNode, id: string): NimNode =
  expectKind(stmts, nnkStmtList)
  for ch in stmts:
    case ch.kind
    of nnkCall:
      if checkIdent(ch, id):
        return ch
    else: continue

proc parsePreface*(n: NimNode): Preface =
  proc extractDfNode(n: NimNode): NimNode =
    ## returns the `df[<col>, <type>]` node found in `n`
    case n.kind
    of nnkInfix:
      doAssert checkIdent(n, "in")
      result = extractDfNode(n[2])
    of nnkBracketExpr:
      doAssert n[0].strVal == "df", "`in` must refer to a `df[<col>, <type>]`!"
      result = n
    else:
      if n.len == 0: return newEmptyNode() # it's not this one
      for ch in n:
        let res = extractDfNode(ch)
        if res.kind == nnkBracketExpr: return ch

  proc addInfixAssign(ch: NimNode): Assign =
    doAssert checkIdent(ch, "in")
    doAssert ch[1].kind == nnkIdent, "First element before `in` needs to be an ident!"
    let dfNode = extractDfNode(ch)
    let elId = ch[1].strVal
    let dtype = dfNode[2].strVal
    # if user applied a transformation, add a replaced by version
    let transformed = ch[2]
    doAssert dtype in Dtypes, "Column dtype " & $dtype & " not in " & $Dtypes & "!"
    result = Assign(asgnKind: byIndex,
                    node: ch,
                    element: ident(elId),
                    tensor: ident(elId & "T"),
                    col: ch[2][1],
                    colType: ident(dtype),
                    transformed: transformed
    )
  proc addAsgnAssign(ch: NimNode): Assign =
    doAssert ch[0].kind == nnkIdent, "First element before `=` needs to be an ident!"
    doAssert ch[1].kind == nnkBracketExpr, "`=` must assign from a `df[<col>, <type>]`!"
    let tId = ch[0].strVal
    let dtype = ch[1][2].strVal
    doAssert dtype in Dtypes, "Column dtype " & $dtype & " not in " & $Dtypes & "!"
    result = Assign(asgnKind: byTensor,
                    node: ch,
                    element: ident(tId & "Idx"),
                    tensor: ident(tId),
                    col: ch[1][1],
                    colType: ident(dtype))

  proc addCustomAssign(ch: NimNode): Assign =
    doAssert ch.kind in {nnkLetSection, nnkVarSection}
    result = Assign(asgnKind: byCustom,
                    node: ch)

  expectKind(n, nnkCall)
  expectKind(n[1], nnkStmtList)
  for ch in n[1]:
    case ch.kind
    of nnkInfix: result.args.add addInfixAssign(ch)
    of nnkAsgn: result.args.add addAsgnAssign(ch)
    of nnkLetSection, nnkVarSection: result.args.add addCustomAssign(ch)
    else: error("Invalid node kind " & $ch.kind & " in `preface`: " & (ch.repr))

proc parseSingle(n: NimNode): NimNode =
  expectKind(n[1], nnkStmtList)
  result = n[1][0]

proc parseLoop(n: NimNode): NimNode =
  expectKind(n[1], nnkStmtList)
  result = n[1]

func removeCallAcc(n: NimNode): NimNode =
  result = if n.kind == nnkAccQuoted: newLit(n[0].strVal)
           elif n.kind == nnkCallStrLit: n[1]
           else: n

proc convertPreface(p: Preface): NimNode =
  ## TODO:
  ## anything that contains a type of `Tensor[T]` needs to be handled differently.
  ## Instead of generating a `let colT = df["col", dType]` we need to just call
  ## the function that
  proc toLet(a: Assign): NimNode =
    var rhs: NimNode
    if a.transformed.kind == nnkNilLit:
      rhs = nnkBracketExpr.newTree(ident(DfIdent), a.col.removeCallAcc(),
                                   ident(a.colType.strVal)) #convert nnkSym to nnkIdent
    else:
      rhs = a.transformed
    result = nnkIdentDefs.newTree(
      a.tensor,
      newEmptyNode(),
      rhs
    )
  result = nnkLetSection.newTree()
  var seenTensors = initHashSet[string]()
  var customs = newStmtList()
  for arg in p.args:
    case arg.asgnKind
    of byIndex, byTensor:
      if arg.tensor.strVal notin seenTensors:
        result.add toLet(arg)
      seenTensors.incl arg.tensor.strVal
    of byCustom:
      customs.add arg.node
  result = quote do:
    `result`
    `customs`

proc convertDtype(d: NimNode): NimNode =
  result = nnkVarSection.newTree(
    nnkIdentDefs.newTree(
      ident(ResIdent),
      newEmptyNode(),
      nnkCall.newTree(
        nnkBracketExpr.newTree(ident"newTensorUninit",
                               d),
        nnkDotExpr.newTree(ident(DfIdent),
                           ident"len"))
    )
  )

proc `$`*(p: Preface): string =
  result = "Preface("
  for i, ch in p.args:
    result.add &"Assign(element: {ch.element.strVal}, "
    result.add &"asgnKind: {ch.asgnKind}, "
    result.add &"node: {ch.node.repr}, "
    result.add &"tensor: {ch.tensor.strVal}, "
    result.add &"col: {buildName(ch.col)}, "
    result.add &"colType: {buildName(ch.colType)}, "
    result.add &"resType: {buildName(ch.resType)})"
    if i < p.args.high:
      result.add ", "
  result.add ")"

proc contains(p: Preface, n: NimNode): bool =
  for arg in p.args:
    if arg.node == n:
      return true

proc `[]`(p: Preface, n: NimNode): Assign =
  for arg in p.args:
    if arg.node == n:
      return arg
  error("Could not find " & n.repr & " in preface containing " & $p)

proc delete(p: var Preface, n: NimNode) =
  var idx = 0
  while idx < p.args.len:
    if p.args[idx].node == n:
      p.args.delete(idx)
      # deleted so return
      ## TODO: we don't depend on removing all "duplicates" (same column ref), right?
      return
    inc idx

proc nodeIsDf*(n: NimNode): bool =
  if n.kind == nnkBracketExpr:
    result = n[0].kind == nnkIdent and n[0].strVal == "df"
  elif n.kind == nnkCall:
    result = n[0].kind == nnkIdent and n[0].strVal == "col"
  elif n.kind in {nnkCallStrLit, nnkAccQuoted}:
    result = true

proc nodeIsDfIdx*(n: NimNode): bool =
  if n.kind == nnkBracketExpr:
    result = n[0].kind == nnkBracketExpr and n[0][0].kind == nnkIdent and
    n[0][0].strVal == "df" and n[1].kind == nnkIdent and n[1].strVal == "idx"
  elif n.kind == nnkCall:
    result = n[0].kind == nnkIdent and n[0].strVal == "idx"
  elif n.kind in {nnkCallStrLit, nnkAccQuoted}:
    result = true

proc hasExplicitTypeHint*(n: NimNode): bool =
  result = (n.nodeIsDf or n.nodeIsDfIdx) and
    n.kind == nnkCall and
    n.len == 3 and
    n[2].kind in {nnkIdent, nnkSym} # and
    #n[2].strVal in DtypesAll
    # XXX: DtypesAll check not allowed here! otherwise overwrites `
    # explicit hints of custom types

proc get(p: var Preface, node: NimNode, useIdx: bool): NimNode =
  let n = p[node]
  p.delete(node)
  result = if n.asgnKind == byIndex:
             if useIdx:
               nnkBracketExpr.newTree(
                 n.tensor,
                 ident(IdxIdent)
               )
             else:
               n.element
           else:
             n.tensor

proc replaceByIdx(n: NimNode, preface: var Preface): NimNode =
  ## recurses the node `n` and replaces all occurences by `t[idx]` for each
  ## tensor in the loop
  # first check if an ident that is in preface we have to replace or if
  # an `nnkBracketExpr` which contains an ident from `preface`. In those cases
  # return early
  case n.kind
  of nnkIdent, nnkSym:
    if n in preface: return preface.get(n, useIdx = true)
    else: return n
  of nnkAccQuoted:
    return preface.get(n, useIdx = true)
  of nnkCallStrLit:
    return preface.get(n, useIdx = true)
  of nnkBracketExpr:
    if n[0].kind == nnkIdent and n in preface:
      return n
    # if `df["someCol"]` replace by full tensor (e.g. in a call taking tensor)
    if nodeIsDf(n) and n in preface:
      return preface.get(n, useIdx = true)
    if nodeIsDfIdx(n) and n in preface:
      return preface.get(n, useIdx = true)
  of nnkCall:
    if (nodeIsDf(n) or nodeIsDfIdx(n)) and n in preface:
      return preface.get(n, useIdx = true)
  else: result = n
  if n.len > 0:
    result = newTree(n.kind)
    for ch in n:
      result.add replaceByIdx(ch, preface)

proc replaceByElement(n: NimNode, preface: var Preface): NimNode =
  ## recurses the node `n` and replaces all occurences by `t` for each
  ## tensor in the loop
  # first check if an ident that is in preface we have to replace or if
  # an `nnkBracketExpr` which contains an ident from `preface`. In those cases
  # return early
  case n.kind
  of nnkIdent, nnkSym:
    if n in preface: return preface.get(n, useIdx = false)
    else: return n
  of nnkAccQuoted:
    return preface.get(n, useIdx = false)
  of nnkCallStrLit:
    return preface.get(n, useIdx = false)
  of nnkBracketExpr:
    if n[0].kind == nnkIdent and n in preface:
      return preface.get(n, useIdx = false)
    # for `df["someCol"]` replace by full tensor, e.g. for call taking tensor
    if nodeIsDf(n) and n in preface:
      return preface.get(n, useIdx = false)
    if nodeIsDfIdx(n) and n in preface:
      return preface.get(n, useIdx = false)
  of nnkCall:
    if (nodeIsDf(n) or nodeIsDfIdx(n)) and n in preface:
      return preface.get(n, useIdx = false)
  else: result = n
  if n.len > 0:
    result = newTree(n.kind)
    for ch in n:
      result.add replaceByElement(ch, preface)

proc replaceByColumn(n: NimNode, preface: var Preface): NimNode =
  ## recurses the node `n` and replaces all occurences by full `col` (i.e. field `tensor`) for each
  ## tensor in the loop
  case n.kind
  of nnkIdent, nnkSym:
    if n in preface: return preface[n].tensor
    else: return n
  of nnkAccQuoted:
    return preface[n].tensor
  of nnkCallStrLit:
    return preface[n].tensor
  of nnkBracketExpr:
    if n[0].kind == nnkIdent and n in preface:
      return preface[n].tensor
    # for `df["someCol"]` replace by full tensor, e.g. for call taking tensor
    if nodeIsDf(n) and n in preface:
      return preface[n].tensor
    if nodeIsDfIdx(n) and n in preface:
      error("Invalid usage of `idx` in a reducing formula! Access: " & $(n.repr))
  of nnkCall:
    if (nodeIsDf(n) or nodeIsDfIdx(n)) and n in preface:
      return preface[n].tensor
  else: result = n
  if n.len > 0:
    result = newTree(n.kind)
    for ch in n:
      result.add replaceByColumn(ch, preface)

proc fixupTensorIndices(loopStmts: NimNode, preface: var Preface,
                        fkKind: FormulaKind, # to handle scalar and vector separately & safely
                        rbKind: ReplaceByKind): NimNode =
  ## If `toElements` is true, we rewrite everything by `t` (where `t` is an
  ## element of `tT` (Tensor). This includes
  expectKind(loopStmts, nnkStmtList)
  case rbKind
  of rbIndex:
    case fkKind
    of fkVector:
      let loop = loopStmts[0].replaceByIdx(preface)
      case loop.kind
      of nnkAsgn:
        doAssert loop[0].kind == nnkBracketExpr and
          loop[0][0].kind == nnkIdent and loop[0][0].strVal == "r" and
          loop[0][1].kind == nnkIdent and loop[0][1].strVal == "idx"
        ## TODO: make this prettier / fix this
      else:
        # turn this into an nnkAsgn node with `res` as LHS and `nnkAsgn` on RHS
        result = nnkAsgn.newTree(
          nnkBracketExpr.newTree(ident(ResIdent), ident(IdxIdent)),
          loop)
    of fkScalar:
      # replace by indices for scalar w/ explicit for loop.
      result = loopStmts[0].replaceByIdx(preface)
    else: doAssert false, "Impossible branch"
  of rbElement:
    case fkKind
    of fkVector:
      let loop = loopStmts[0].replaceByElement(preface)
      case loop.kind
      of nnkAsgn: doAssert loop[0].kind == nnkIdent and loop[0].strVal == RIdent
      else:
        # turn this into an nnkAsgn node with `res` as LHS and `nnkAsgn` on RHS
        result = nnkAsgn.newTree(ident(RIdent), loop)
    of fkScalar:
      # replace by indices for scalar w/ explicit for loop.
      result = loopStmts[0].replaceByElement(preface)
    else: doAssert false, "Impossible branch"
  of rbColumn:
    # always fkScalar
    let loop = loopStmts[0].replaceByColumn(preface)
    case loop.kind
    of nnkAsgn: doAssert loop[0].kind == nnkIdent and loop[0].strVal == ResIdent
    else:
      # turn this into an `nnkVarSection` node with `res` as LHS and `loop` as RHS
      result = nnkVarSection.newTree(
        nnkIdentDefs.newTree(
          ident(ResIdent),
          newEmptyNode(),
          loop)
      )

proc hasResIdent(p: Preface): bool =
  ## Checks if the `Preface` has a `byCustom` `Assign` that refers to the
  ## `ResIdent` (== `res`) node
  for arg in p.args:
    if arg.asgnKind == byCustom and arg.node[0][0].strVal == ResIdent:
      return true

proc convertLoop(p: Preface, dtype, fctColResType, loop: NimNode,
                 fnKind: FormulaKind,
                 generateLoop: bool): NimNode =
  let memCopyable = ["float", "int", "bool"]
  let isMemCopyable = dtype.strVal in memCopyable and
    p.args.allIt(it.colType.strVal in memCopyable)
  proc genForLoop(p: Preface, loop: NimNode, fkKind: FormulaKind): NimNode =
    var mpreface = p
    let loopIndexed = fixupTensorIndices(loop, mpreface,
                                         fkKind = fkKind,
                                         rbKind = rbIndex)
    let idx = ident(IdxIdent)
    let df = ident(DfIdent)
    var loop = quote do:
      for `idx` in 0 ..< `df`.len:
        `loopIndexed`
    result = newStmtList(loop)

  proc genForEach(p: Preface, loop: NimNode, fkKind: FormulaKind): NimNode =
    var mpreface = p
    let loopElements = fixupTensorIndices(loop, mpreface,
                                          fkKind = fkKind,
                                          rbKind = rbElement)
    var forEach = nnkCommand.newTree(ident"forEach")
    if fkKind == fkVector: ## add the `r in res` argument as first in case of vector (mutable assign)
      forEach.add nnkInfix.newTree(ident(InIdent), ident(RIdent), ident(ResIdent))
    for arg in p.args:
      if arg.asgnKind in {byIndex, byTensor}: # `byCustom` does not generate something to loop over!
        forEach.add nnkInfix.newTree(ident(InIdent), arg.element, arg.tensor)
    forEach.add nnkStmtList.newTree(loopElements)
    result = newStmtList(forEach)

  proc addResultVector(): NimNode =
    let resId = ident(ResIdent)
    let resultId = ident(ResultIdent)
    result = quote do:
      `resultId` = toColumn(`fctColResType`, `resId`)

  case fnKind
  of fkVector:
    if not isMemCopyable:
      result = genForLoop(p, loop, fkVector)
      result.add addResultVector()
    else:
      result = genForEach(p, loop, fkVector)
      result.add addResultVector()
  of fkScalar:
    var mpreface = p
    var loopImpl: NimNode
    if generateLoop: # despite being `fkScalar` generate an (accumulating) for loop
      if not isMemCopyable:
        loopImpl = genForLoop(p, loop, fkScalar)
      else:
        loopImpl = genForEach(p, loop, fkScalar)
    else:
      loopImpl = fixupTensorIndices(loop, mpreface,
                                    fkKind = fkScalar,
                                    rbKind = rbColumn)
    let resultId = ident(ResultIdent)
    let resId = ident(ResIdent)
    if generateLoop:
      ## raise error if no `Assign` known as  `ResIdent`
      if not p.hasResIdent:
        error("Generating an explicit reducing (`<<`) formula failed, as the " &
          "`res` variable was not declared in the preface. Add a\n" &
          "preface:\n" &
          "  var res = <init value>\n" &
          "part to your formula.")
      result = quote do:
        `loopImpl`
        `resultId` = %~ `resId`
    else:
      result = quote do:
        `loopImpl`
        `resultId` = %~ `resId`
  else:
    error("Invalid FormulaKind `" & $(fnKind.repr) & "` in `convertLoop`. Already handled " &
      "in `compileFormula`!")

proc parseFormulaCT(stmts: NimNode): FormulaCT =
  let preface = parsePreface(extractCall(stmts, "preface"))
  ## TODO: if `dtype` not given: auto determine
  let dtype = parseSingle(extractCall(stmts, "dtype"))
  let name = parseSingle(extractCall(stmts, "name"))
  let loop = parseLoop(extractCall(stmts, "loop"))
  result = FormulaCT(preface: preface,
                     resType: dtype,
                     name: name,
                     loop: loop)

proc generateClosure*(fct: FormulaCT): NimNode =
  var procBody = newStmtList()
  procBody.add getAst(convenienceValueComparisons()) # add convenience comparison ops Value ⇔ T
  procBody.add convertPreface(fct.preface)
  if fct.funcKind == fkVector:
    procBody.add convertDtype(fct.resType)
  procBody.add convertLoop(fct.preface, fct.resType, fct.colResType, fct.loop, fct.funcKind, fct.generateLoop)
  result = procBody
  let dfTyp = fct.colResType
  var params: array[2, NimNode]
  case fct.funcKind
  of fkVector:
    params = [fct.colResType,
              nnkIdentDefs.newTree(ident(DfIdent),
                                   nnkBracketExpr.newTree(ident"DataTable", dfTyp),
                                   newEmptyNode())]
  of fkScalar:
    when (NimMajor, NimMinor, NimPatch) < (1, 5, 0):
      let valueId = ident(ValueIdent)
    else:
      let valueId = nnkDotExpr.newTree(ident"value", ident(ValueIdent))
    # to avoid clashes with other `Value` objects, fully clarify we mean ours
    params = [valueId,
              nnkIdentDefs.newTree(ident(DfIdent),
                                   nnkBracketExpr.newTree(ident"DataTable", dfTyp),
                                   newEmptyNode())]
  else:
    error("Invalid FormulaKind `" & $(fct.funcKind.repr) & "` in `convertLoop`. Already handled " &
      "in `compileFormula`!")
  result = newProc(newEmptyNode(),
                   params = params,
                   body = procBody,
                   procType = nnkLambda)

proc compileFormula(stmts: NimNode): NimNode {.used.} =
  let fct = parseFormulaCT(stmts)
  result = generateClosure(fct)

macro formula(y: untyped): untyped {.used.} =
  ## TODO: add some ability to explicitly create formulas of
  ## different kinds more easily! Essentially force the type without
  ## a check to avoid having to rely on heuristics.
  ## Use
  ## - `<-` for assignment
  ## - `<<` for reduce operations, i.e. scalar proc?
  ## - `~` for vector like proc
  ## - formula without any of the above will be considered:
  ##   - `fkVariable` if no column involved
  ##   - `fkVector` else
  ## - `<type>: <actualFormula>`: simple type hint for tensors in closure
  ## - `<type> -> <resDtype>: <actualFormula>`: full type for closure.
  ##   `<type>` is the dtype used for tensors, `<resDtype>` the resulting type
  ## - `df[<someIdent/Sym>]`: to access columns using identifiers / symbols
  ##   defined in the scope
  ## - `idx`: can be used to access the loop iteration index
  result = compileFormula(y)

when false: # isMainModule:
  import math
  import arraymancer / laser / strided_iteration / foreach
  let f1 = formula:
    preface:
      t in df["foo", int] # t refers to each element of `foo` in the loop
      u in df["bar", float]
      v = df["baz", int] # v refers to the ``Tensor`` `baz`
    dtype: float
    name: "fooBar"
    loop:
      t.float * u + v[idx].float

  let f2 = f{ parseInt(`t`) > 5 }


#let f2 = fn:
#  preface:
#    t in df["foo", int] # t refers to each element of `foo` in the loop
#    u in df["bar", float]
#    v = df["baz", int] # v refers to the ``Tensor`` `baz`
#    #r in result
#  dtype: bool
#  name: "filterme"
#  loop:
#    t.float > u and v[idx].float < 2.2
#
#let f3 = fn:
#  preface:
#    t in df["foo", float] # t refers to each element of `foo` in the loop
#  dtype: bool
#  name: "noNan"
#  loop:
#    not (classify(t) == fcNan)
