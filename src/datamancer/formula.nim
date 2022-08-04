import macros, tables, sequtils, sets, options, strutils, hashes
import value, column, df_types
# formulaNameMacro contains a macro and type based on the fallback `FormulaNode`,
# which is used to generate the names of each `FormulaNode` in lisp representation
import formulaNameMacro
export formulaNameMacro

import formulaExp
export formulaExp

import arraymancer / laser / strided_iteration / foreach
export foreach

type
  ## NOTE: type of formula must only be single generic and must always match the
  ## *output* type!
  Formula*[C: ColumnLike] = object
    name*: string # stringification of whole formula. Only for printing and
                  # debugging
    case kind*: FormulaKind
    of fkVariable:
      # just some constant value. Result of a simple computation as a `Value`
      # This is mainly used to rename columns / provide a constant value
      val*: Value
    of fkAssign:
      lhs*: string # can this be something else?
      rhs*: Value
    of fkVector:
      colName*: string
      resType*: ColKind
      fnV*: proc(df: DataTable[C]): C
    of fkScalar:
      valName*: string
      valKind*: ValueKind
      fnS*: proc(c: DataTable[C]): Value
    of fkNone: discard

  FormulaNode* = Formula[Column]

  FormulaMismatchError* = object of CatchableError

type
  ## These are internal types used in the macro
  TypeKind = enum
    tkNone, tkExpression, tkProcedure

  PossibleTypes = object
    isGeneric: bool
    asgnKind: Option[AssignKind]
    case kind: TypeKind
    of tkExpression:
      types: seq[NimNode]
    of tkProcedure:
      ## procedure types encountered are separate
      procTypes: seq[ProcType]
    else: discard

  ProcType = object
    argId: int # argument number of the "input" type
    isGeneric: bool
    inputTypes: seq[NimNode] # types of all arguments
    resType: Option[NimNode]

proc hash*[C: ColumnLike](fn: Formula[C]): Hash =
  result = hash(fn.kind.int)
  result = result !& hash(fn.name)
  case fn.kind
  of fkVariable:
    result = result !& hash(fn.val)
  of fkAssign:
    result = result !& hash(fn.lhs)
    result = result !& hash(fn.rhs)
  of fkVector:
    result = result !& hash(fn.resType)
    result = result !& hash(fn.fnV)
  of fkScalar:
    result = result !& hash(fn.valKind)
    result = result !& hash(fn.fnS)
  of fkNone: discard

proc raw*[C: ColumnLike](node: Formula[C]): string =
  ## prints the raw stringification of `node`
  result = node.name

proc toUgly*[C: ColumnLike](result: var string, node: Formula[C]) =
  ## This is the formula stringification, which can be used to access the corresponding
  ## column of in a DF that corresponds to the formula
  case node.kind:
  of fkVariable:
    result = $node.val
  of fkAssign:
    result.add "(<- "
    result.add $node.lhs & " "
    result.add $node.rhs & ")"
  of fkVector:
    result = $node.colName
  of fkScalar:
    result = $node.valName
  of fkNone: discard

proc `$`*[C: ColumnLike](node: Formula[C]): string =
  ## Converts `node` to its string representation
  result = newStringOfCap(1024)
  toUgly(result, node)

proc add(p: var PossibleTypes, pt: ProcType) =
  doAssert p.kind in {tkProcedure, tkNone}
  if p.kind == tkNone:
    p = PossibleTypes(kind: tkProcedure)
  p.procTypes.add pt

proc add(p: var PossibleTypes, p2: PossibleTypes) {.used.} =
  doAssert p.kind == p2.kind
  case p.kind
  of tkExpression: p.types.add p2.types
  of tkProcedure: p.procTypes.add p2.procTypes
  else: discard

proc add(p: var Preface, p2: Preface) =
  ## Adds the Assign fields of `p2` to `p`
  p.args.add p2.args
  p.resType = p2.resType

func isColIdxCall(n: NimNode): bool =
  (n.kind == nnkCall and n[0].kind == nnkIdent and n[0].strVal in ["idx", "col"])
func isColCall(n: NimNode): bool =
  (n.kind == nnkCall and n[0].kind == nnkIdent and n[0].strVal == "col")
func isIdxCall(n: NimNode): bool =
  (n.kind == nnkCall and n[0].kind == nnkIdent and n[0].strVal == "idx")

proc isGeneric(n: NimNode): bool =
  ## given a node that represents a type, check if it's generic by checking
  ## if the symbol or bracket[symbol] is notin `Dtypes`
  case n.kind # assume generic is single symbol. Will fail for longer!
  of nnkSym, nnkIdent:
    ## the generic check for an ident / sym checks for `[` and `]` and / or single
    ## generic type name. This is a bit brittle for user defined types with a single letter
    ## of course, but for now...
    let nStr = n.strVal
    if "[" in nStr:
      let idx = find(nStr, "[")
      doAssert nStr.len > idx + 2
      if nStr[idx + 2] == ']': result = true
    elif nStr.len == 1:
      result = true
  of nnkBracketExpr: result = n[1].strVal.len == 1 # notin DtypesAll
  of nnkEmpty: result = true # sort of generic...
  else: error("Invalid call to `isGeneric` for non-type like node " &
    $(n.treeRepr) & "!")

proc reorderRawTilde(n: NimNode, tilde: NimNode): NimNode =
  ## a helper proc to reorder an nnkInfix tree according to the
  ## `~` contained in it, so that `~` is at the top tree.
  ## (the actual result is simply the tree reordered, but without
  ## the tilde. Reassembly must happen outside this proc)
  ##
  ## TODO: For a formula like:
  ##       let fn = fn2 { "Test" ~ max idx("a"), "hello", 5.5, someInt() }
  ## we reconstruct:
  ## Curly
  ##   Infix
  ##     Ident "~"
  ##     StrLit "Test"
  ##     Command
  ##       Ident "max"
  ##       Call
  ##         Ident "idx"
  ##         StrLit "a"
  ##   StrLit "hello"
  ##   FloatLit 5.5
  ##   Call
  ##     Ident "someInt"
  ## so the tilde is still nested one level too deep.
  ## However it seems to be rather an issue of `recurseFind`?
  result = copyNimTree(n)
  for i, ch in n:
    case ch.kind
    of nnkIdent, nnkStrLit, nnkIntLit .. nnkFloat64Lit, nnkPar, nnkCall, nnkCommand,
       nnkAccQuoted, nnkCallStrLit, nnkBracketExpr, nnkStmtList:
      discard
    of nnkInfix:
      if ch == tilde:
        result[i] = tilde[2]
      else:
        result[i] = reorderRawTilde(ch, tilde)
    else:
      error("Unsupported kind " & $ch.kind)

proc recurseFind(n: NimNode, cond: NimNode): NimNode =
  ## a helper proc to find a node matching `cond` recursively
  for i, ch in n:
    if ch == cond:
      result = n
      break
    else:
      let found = recurseFind(ch, cond)
      if found.kind != nnkNilLit:
        result = found

proc compileVectorFormula(fct: FormulaCT): NimNode =
  let fnClosure = generateClosure(fct)
  # given columns
  let rawName = newLit(fct.rawName)
  var colName = if fct.name.kind == nnkNilLit: rawName else: fct.name
  let dtype = fct.resType
  let dfTyp = fct.dfType
  let colResType = fct.colResType
  result = quote do:
    Formula[`colResType`](name: `rawName`,
                          colName: `colName`, kind: fkVector,
                          resType: toColKind(type(`dtype`)),
                          fnV: `fnClosure`)
  when defined(echoFormulas):
    echo result.repr

proc compileScalarFormula(fct: FormulaCT): NimNode =
  let fnClosure = generateClosure(fct)
  let rawName = newLit(fct.rawName)
  let valName = if fct.name.kind == nnkNilLit: rawName else: fct.name
  let dtype = fct.resType
  let C = ident(ColIdent)
  result = quote do:
    Formula[`C`](name: `rawName`,
                 valName: `valName`, kind: fkScalar,
                 valKind: toValKind(`dtype`),
                 fnS: `fnClosure`)
  when defined(echoFormulas):
    echo result.repr

type
  TupRes = tuple[isInt: bool,
                 isFloat: bool,
                 isString: bool,
                 isBool: bool]

proc checkDtype(body: NimNode,
                floatSet: HashSet[string],
                stringSet: HashSet[string],
                boolSet: HashSet[string]):
                  TupRes =
  func assignResult(r: var TupRes, res: TupRes) =
    r = (isInt: r.isInt or res.isInt,
         isFloat: r.isFloat or res.isFloat,
         isString: r.isString or res.isString,
         isBool: r.isBool or res.isBool)
  case body.kind
  of nnkIdent:
    # check
    result = (isInt: result.isInt,
              isFloat: body.strVal in floatSet or result.isFloat,
              isString: body.strVal in stringSet or result.isString,
              isBool: body.strVal in boolSet or result.isBool)
  of nnkCallStrLit, nnkAccQuoted, nnkCall:
    # skip this node completely, don't traverse further, since it (might) represent
    # a column!
    return
  of nnkStrLit, nnkTripleStrLit, nnkRStrLit:
    result.isString = true
  of nnkIntLit .. nnkUInt64Lit:
    result.isInt = true
  of nnkFloatLit, nnkFloat64Lit:
    result.isFloat = true
  of nnkIfStmt: # exclude if statements
    var res: tuple[isInt: bool,
                   isFloat: bool,
                   isString: bool,
                   isBool: bool]
    for branch in body:
      if branch.kind == nnkElifBranch:
        res = checkDtype(branch[0], floatSet, stringSet, boolSet)
        res.isBool = false # ignore bool here, argument [0] to `if / elif` is obv. bool
        result.assignResult(res)
        res = checkDtype(branch[1], floatSet, stringSet, boolSet)
        result.assignResult(res)
      elif branch.kind == nnkElse:
        res = checkDtype(branch, floatSet, stringSet, boolSet)
        result.assignResult(res)
  else:
    for ch in body:
      let res = checkDtype(ch, floatSet, stringSet, boolSet)
      result.assignResult(res)

var TypedSymbols {.compileTime.}: Table[string, Table[string, NimNode]]
var Formulas {.compileTime.}: Table[string, FormulaCT]

macro addSymbols(tabName, nodeName: string, n: typed): untyped =
  let nStr = tabName.strVal
  let nodeStr = nodeName.strVal
  if nStr notin TypedSymbols:
    TypedSymbols[nStr] = initTable[string, NimNode]()
  TypedSymbols[nStr][nodeStr] = n


macro typedChecker(n: typed): untyped = discard
macro checkSymbolIsValid(n: untyped): untyped =
  ## I've tried to avoid this as long as I could, but I don't know an alternative
  ## at the moment. The issue is if we have something like:
  ## `f{isNaN(idx("foo"))}`
  ## the the ident `isNan` cannot call `addSymbols`, because the compiler will complain
  ## that the symbol is `None`.
  ## All I can think of is to emit a `when compiles` that calls a dummy checker
  ## ("can it be made typed?" essentially) :(
  result = quote do:
    when compiles(typedChecker(`n`)):
      true
    else:
      false

proc isPureTree(n: NimNode): bool
proc extractSymbols(n: NimNode): seq[NimNode] =
  if n.isPureTree:
    return @[n]
  case n.kind
  of nnkIdent, nnkSym:
    # take any identifier or symbol
    if n.strVal notin ["df", "idx"]: # these are reserved identifiers
      result.add n
  of nnkIntLit .. nnkFloat64Lit, nnkStrLit:
    result.add n
  of nnkBracketExpr:
    # iff this is not a column access recurse and look at children
    if n.nodeIsDf or n.nodeIsDfIdx:
      return
    for i in 0 ..< n.len:
      result.add extractSymbols(n[i])
  of nnkDotExpr:
    ## If `DotExpr` consists only of Idents during the untyped pass,
    ## it's either field access or multiple calls taking no arguments.
    ## In that case we can just keep the chain and pass it to the typed
    ## macro. In case other things are contained (possibly `df[<...>]` or
    ## a regular call) take the individual fields.
    ## For something like `ms.trans` in ggplotnim (`trans` field of a scale)
    ## we need to pass `ms.trans` to typed macro!
    proc isAllIdent(n: NimNode): bool =
      result = true
      case n.kind
      of nnkIdent: discard
      of nnkDotExpr:
        if n[1].kind != nnkIdent: return false
        result = isAllIdent(n[0])
      else: return false
    let allIdent = isAllIdent(n)
    if allIdent:
      result.add n
    else:
      # add all identifiers found
      for ch in n:
        result.add extractSymbols(ch)
  of nnkCall:
    # check if it's a call of `idx(someCol)` or `col(someCol)`. Else recurse.
    if n.isColIdxCall():
      return
    for i in 0 ..< n.len:
      result.add extractSymbols(n[i])
  of nnkAccQuoted, nnkCallStrLit:
    # do not look at these, since they are untyped identifiers referring to
    # DF columns
    return
  of nnkIfStmt: # ignore the actual `if` and only look at the bodies of each node)
    for branch in n:
      for ch in branch:
        result.add extractSymbols(ch)
  else:
    for i in 0 ..< n.len:
      result.add extractSymbols(n[i])

const FloatSet = toHashSet(@["+", "-", "*", "/", "mod"])
const StringSet = toHashSet(@["&", "$"])
const BoolSet = toHashSet(@["and", "or", "xor", ">", "<", ">=", "<=", "==", "!=",
                            "true", "false", "in", "notin", "not"])

proc determineHeuristicTypes(body: NimNode,
                             typeHint: TypeHint,
                             name: string): TypeHint =
  ## checks for certain ... to  determine both the probable
  ## data type for a computation and the `FormulaKind`
  doAssert body.len > 0, "Empty body unexpected in `determineFuncKind`!"
  # if more than one element, have to be a bit smarter about it
  # we use the following heuristics
  # - if `+, -, *, /, mod` involved, return as `float`
  #   `TODO:` can we somehow leave pure `int` calcs as `int`?
  # - if `&`, `$` involved, result is string
  # - if `and`, `or`, `xor`, `>`, `<`, `>=`, `<=`, `==`, `!=` involved
  #   result is considered `bool`
  # The priority of these is,
  # - 1. bool
  # - 2. string
  # - 3. float
  # which allows for something like
  # `"10." & "5" == $(val + 0.5)` as a valid bool expression
  # walk tree and check for symbols
  let (isInt, isFloat, isString, isBool) = checkDtype(body, FloatSet, StringSet, BoolSet)
  var typ: TypeHint
  if isInt:
    typ.inputType = some(ident"int")
    typ.resType = some(ident"int")
  if isFloat:
    # overrides int if it appears
    typ.inputType = some(ident"float")
    typ.resType = some(ident"float")
  if isString:
    # overrides float if it appears
    typ.inputType = some(ident"string")
    typ.resType = some(ident"string")
  if isBool:
    # overrides float and string if it appears
    if isString:
      typ.inputType = some(ident"string")
    elif isFloat:
      typ.inputType = some(ident"float")
    elif isInt:
      typ.inputType = some(ident"int")
    else:
      # is bool tensor
      typ.inputType = some(ident"bool")
    # result is definitely bool
    typ.resType = some(ident"bool")

  # apply typeHint if available (overrides above)
  if typeHint.inputType.isSome:
    let dtype = typeHint.inputType
    if isBool:
      # we don't override bool result type.
      # in cases like:
      # `f{int: x > 4}` the are sure of the result, apply to col only
      typ.inputType = dtype
    elif isFloat or isString or isInt:
      # override dtype, result still clear
      typ.inputType = dtype
    else:
      # set both
      typ.inputType = dtype
      typ.resType = dtype
  if typeHint.resType.isSome:
    # also assign result type. In this case override regardless of automatic
    # determination
    typ.resType = typeHint.resType
  result = typ

proc genColSym(name, s: string): NimNode =
  ## custom symbol generation from `name` (may contain characters that are
  ## invalid Nim symbols) and `s`
  var name = name
  if name.len == 0 or name[0] notin IdentStartChars:
    name = "col" & name
  result = ident(name & s)

proc addColRef(n: NimNode, typeHint: FormulaTypes, asgnKind: AssignKind): seq[Assign] =
  let (dtype, resType) = (typeHint.inputType, typeHint.resType)
  case n.kind
  of nnkAccQuoted:
    let name = n[0].strVal
    result.add Assign(asgnKind: asgnKind,
                      node: n,
                      element: ident(name & "Idx"),
                      tensor: ident(name),
                      col: newLit(name),
                      colType: dtype,
                      resType: resType)
  of nnkCallStrLit:
    # call str lit needs to be handled indendently, because it may contain
    # symbols that are invalid for a Nim identifier
    let name = buildName(n)
    let colName = genColSym(name, "T")
    let colIdxName = genColSym(name, "Idx")
    let nameCol = newLit(name)
    result.add Assign(asgnKind: asgnKind,
                      node: n,
                      element: colIdxName,
                      tensor: colName,
                      col: nameCol,
                      colType: dtype,
                      resType: resType)
  of nnkBracketExpr:
    if nodeIsDf(n):
      # `df["someCol"]`
      let name = n[1]
      let colName = genColSym(buildName(name), "T")
      let colIdxName = genColSym(buildName(name), "Idx")
      result.add Assign(asgnKind: byTensor,
                        node: n,
                        element: colIdxName,
                        tensor: colName,
                        col: n[1],
                        colType: dtype,
                        resType: resType)
    elif nodeIsDfIdx(n):
      # `df["someCol"][idx]`
      let name = n[0][1]
      let colName = genColSym(buildName(name), "T")
      let colIdxName = genColSym(buildName(name), "Idx")
      result.add Assign(asgnKind: byIndex,
                        node: n,
                        element: colIdxName,
                        tensor: colName,
                        col: n[0][1],
                        colType: dtype,
                        resType: resType)
    else:
      error("Invalid nnkBracketNode. Might contain a column reference, but " &
        "is not a raw colunm reference!")
  of nnkCall:
    # - `col(someCol)` referring to full column access
    # - `idx(someCol)` referring to column index access
    let name = buildName(n[1])
    let colName = genColSym(name, "T")
    let colIdxName = genColSym(name, "Idx")
    var dtypeOverride = dtype
    var resTypeOverride = resType
    if n.len == 3:
      ## XXX: Since we now cannot base the valid types on the known valid types, instead we
      ## should add this to something so that we can either:
      ## - extend the required Column type (e.g. user wants to read `Foo`, then Column must be
      ##   `ColumnFoo*`)
      ## - error if the determined Column type does not allow for this.
      ## Latter seems illogical to me right now, as the formula itself doesn't know anything about
      ## types (that's why we have a DF argument to `compileFn` after all).
      ## Could check for that DF type though!
      ##
      ## TODO: write test checking that we can hand a DF to compileFn with a type X and we try
      ## to read a type Y. Should CT error iff a DF is handed. Else extend notion of required
      ## type?
      dtypeOverride = n[2]
      if resTypeOverride.kind == nnkEmpty:
        # use input type as return type as well
        resTypeOverride = dtypeOverride
    result.add Assign(asgnKind: asgnKind,
                      node: n,
                      element: colIdxName,
                      tensor: colName,
                      col: n[1],
                      colType: dtypeOverride,
                      resType: resTypeOverride)
  else:
    discard

proc countArgs(n: NimNode): tuple[args, optArgs: int] =
  ## counts the number of arguments this procedure has as well
  ## as the number of default arguments
  ## Arguments are a `nnkFormalParams`. The first child node refers
  ## to the return type.
  ## After that follows a bunch of `nnkIdentDefs`, with typically
  ## 3 child nodes. However if we have a proc
  ## `proc foo(a, b: int): int`
  ## the formal params only have 2 child nodes and a `nnkIdentDefs` with
  ## 4 instead of 3 children (due to the `,`).
  ## An optional value is stored in the last node. If no optional parameters
  ## that node is empty.
  expectKind(n, nnkFormalParams)
  # skip the first return type node
  for idx in 1 ..< n.len:
    let ch = n[idx]
    let chLen = ch.len
    inc result.args, chLen - 2 # add len - 2, since 3 by default.
                               #Any more is same type arg
    if ch[ch.len - 1].kind != nnkEmpty:
      inc result.optArgs, chLen - 2

func isTensorType(n: NimNode): bool =
  n[0].kind in {nnkSym, nnkIdent} and n[0].strVal == "Tensor"

import sugar
proc typeAcceptable(n: NimNode): bool =
  case n.kind
  of nnkIdent, nnkSym:
    let nStr = n.strVal
    let typIsGeneric = n.isGeneric
    if not typIsGeneric: # in DtypesAll:
      result = true
    elif nStr.startsWith("Tensor") and not typIsGeneric: # and
      #   nStr.dup(removePrefix("Tensor["))[0 ..< ^1] in DtypesAll:
      ## XXX: DtypesAll not allowed here, otherwise might override explicit type hints!
      # stringified type `Tensor[int, float, ...]`. Check is a bit of a hack
      result = true
  of nnkBracketExpr:
    if n.isTensorType() and not n.isGeneric:
      result = true
  else: discard

proc determineTypeFromProc(n: NimNode, numArgs: int): Option[ProcType] =
  # check if args matches our args
  var res = ProcType()
  let params = if n.kind == nnkProcTy: n[0]
               else: n.params
  let (hasNumArgs, optArgs) = countArgs(params)
  if (hasNumArgs - numArgs) <= optArgs and numArgs <= hasNumArgs:
    res.isGeneric = (not (n.kind == nnkProcTy)) and n[2].kind != nnkEmpty
    res.resType = some(params[0].toStrType)
    for idx in 1 ..< params.len:
      # skip index 0, cause that's the output type
      let pArg = params[idx]
      let numP = pArg.len - 2 # number of arguments in this `nnkIdentDefs`. By default 3, but more
                              # if multiple like `a, b: float` (4 in this case)
      # if empty, means proc has a default value, but not exact type, e.g.:
      # IdentDefs
      #   Sym "n"
      #   Sym "m"
      #   Empty        <- pArg.len - 2
      #   IntLit 1     <- pArg.len - 1
      var typ: NimNode
      case pArg[numP].kind
      of nnkEmpty:
        typ = pArg[pArg.len - 1].getType # use the default values type
      else: # else param has a specific type
        typ = pArg[pArg.len - 2].toStrType # use the arguments type as a type
      for j in 0 ..< numP: # now add a type for *each* of the possible N arguments of the same type
        res.inputTypes.add typ
    if res.resType.isSome or res.inputTypes.len > 0:
      result = some(res)

proc maybeAddSpecialTypes(possibleTypes: var PossibleTypes, n: NimNode) =
  ## These don't appear as overloads sometimes?
  if n.kind in {nnkSym, nnkIdent}:
    if n.strVal in ["<", ">", ">=", "<=", "==", "!="]:
      for dtype in Dtypes:
        possibleTypes.add ProcType(inputTypes: @[ident(dtype),
                                                 ident(dtype)],
                                   isGeneric: false,
                                   resType: some(ident("bool")))

proc findType(n: NimNode, numArgs: int): PossibleTypes =
  ## This procedure tries to find type information about a given NimNode.
  var possibleTypes = PossibleTypes()
  case n.kind
  of nnkIntLit .. nnkFloat64Lit, nnkStrLit:
    return PossibleTypes(isGeneric: false, kind: tkExpression, types: @[n.toStrType],
                         asgnKind: some(byIndex))
  of nnkSym:
    ## TODO: chck if a node referring to our types
    if n.strVal in DtypesAll:
      return PossibleTypes(isGeneric: false, kind: tkExpression, types: @[n.toStrType],
                           asgnKind: some(byIndex))
    else:
      ## TODO: check if a proc by using `getImpl`
      let tImpl = n.getImpl
      case tImpl.kind
      of nnkProcDef, nnkFuncDef:
        let pt = determineTypeFromProc(tImpl, numArgs)
        if pt.isSome:
          possibleTypes.add pt.get
      of nnkTemplateDef:
        # cannot deduce from template
        result.maybeAddSpecialTypes(n)
        return
      else:
        # should be a symbol of a pure tree. Should have a well defined type
        ## TODO: is this branch likely?
        ## Should happen, yes. E.g. just a variable defined in local scope?
        ##
        let typ = n.getType.toStrType
        if typ.kind != nnkEmpty:
          return PossibleTypes(isGeneric: false, kind: tkExpression,
                               types: @[typ], asgnKind: some(byIndex))
        when false:
          warning("How did we stumble over " & $(n.treeRepr) & " with type " &
            $(tImpl.treeRepr))
        #return
  of nnkCheckedFieldExpr:
    let impl = n.getTypeImpl
    expectKind(impl, nnkProcTy)
    ## TODO: fix to actually use proc type!
    let inputType = impl[0][1][1]
    let resType = impl[0][0]
    let pt = ProcType(inputTypes: @[inputType.toStrType],
                      resType: some(resType.toStrType))
    possibleTypes.add pt
  of nnkClosedSymChoice, nnkOpenSymChoice:
    for ch in n:
      let tImpl = ch.getImpl
      case tImpl.kind
      of nnkProcDef, nnkFuncDef:
        let pt = determineTypeFromProc(tImpl, numArgs)
        if pt.isSome:
          possibleTypes.add pt.get
      of nnkMacroDef, nnkTemplateDef:
        # skip macro defs, e.g. like Unchained defining `*`, ... macros
        continue
      else:
        error("How did we stumble over " & $(ch.treeRepr) & " with type " &
          $(tImpl.treeRepr))
  else:
    ## Else we deal with a pure node from which we can extract the type
    ## TODO: Clarify what this is for better. Write down somewhere that we try to
    ## determine types up to pure nodes, which means we may end up with arbitrary
    ## nim nodes that have a type
    let typ = n.getTypeInst
    case typ.kind
    of nnkProcDef, nnkFuncDef, nnkProcTy:
      let pt = determineTypeFromProc(typ, numArgs)
      if pt.isSome:
        possibleTypes.add pt.get
    else:
      return PossibleTypes(isGeneric: false, kind: tkExpression,
                           types: @[typ.toStrType], asgnKind: some(byIndex))

  ## possibly add special types
  possibleTypes.maybeAddSpecialTypes(n)
  result = possibleTypes

proc isPureTree(n: NimNode): bool =
  ## checks if this node tree is a "pure" tree. That means it does ``not``
  ## contain any column references
  result = true
  if n.nodeIsDf or n.nodeIsDfIdx:
    return false
  for ch in n:
    result = isPureTree(ch)
    if not result:
      return

proc getTypeIfPureTree(tab: Table[string, NimNode], n: NimNode, numArgs: int): PossibleTypes =
  let lSym = buildName(n)
  if n.isPureTree and lSym in tab:
    let nSym = tab[lSym]
    result = findType(nSym, numArgs = numArgs)
  else:
    ## "hack" to get the correct type of the last node in case this is impure.
    ## Needed in some cases like dotExpressions from an infix so that we know
    ## the result of the full expression
    if n.len > 0:
      case n.kind
      of nnkInfix, nnkCall, nnkPrefix, nnkCommand: # type we need is of 0 arg
        result = tab.getTypeIfPureTree(n[0], numArgs)
      of nnkDotExpr: # type we need is of last arg
        result = tab.getTypeIfPureTree(n[^1], numArgs)
      else:
        # else we have no type info?
        #result = tab.getTypeIfPureTree(n[^1], numArgs)
        return

  ## TODO: there are cases where one can extract type information from impure trees.
  ## `idx("a").float` is a nnkDotExpr that is impure, but let's us know that the output
  ## type will be `float`.
  ## The thing is this information will appear on the next recursion anyway. But for
  ## certain cases (e.g. infix before such a impure dotExpr) we could use the information
  ## already.

proc typesMatch(n, m: NimNode): bool =
  result = if n.kind in {nnkSym, nnkIdent, nnkBracketExpr} and
              m.kind in {nnkSym, nnkIdent, nnkBracketExpr}:
             n.repr == m.repr
           else: false

proc toTypeSet(s: seq[NimNode]): HashSet[string] =
  result = initHashSet[string]()
  for x in s:
    result.incl x.repr

proc toTypeSet(p: seq[ProcType], inputs: bool): HashSet[string] =
  result = initHashSet[string]()
  for pt in p:
    if inputs:
      for it in pt.inputTypes:
        result.incl it.repr
    else:
      if pt.resType.isSome:
        result.incl pt.resType.get.repr

proc matchingTypes(t, u: PossibleTypes): seq[NimNode] =
  ## Checks if the types match.
  ## If considering a chain of expressions, `t` is considered on the LHS so that
  ## it's output will be the input of `u`.
  var ts: HashSet[string]
  var us: HashSet[string]
  if t.kind == tkExpression:
    ts = t.types.toTypeSet
  elif t.kind == tkProcedure:
    ts = t.procTypes.toTypeSet(false)
  if u.kind == tkExpression:
    us = u.types.toTypeSet
  elif u.kind == tkProcedure:
    us = u.procTypes.toTypeSet(true)
  if ts.card > 0 and us.card > 0:
    result = intersection(ts, us).toSeq.mapIt(ident(it))

proc assignType(heuristicType: FormulaTypes, types: seq[NimNode], resType = newEmptyNode()): FormulaTypes =
  if types.len == 1:
    result = FormulaTypes(inputType: types[0],
                          resType: heuristicType.resType)
    if result.resType.kind == nnkEmpty:
      result.resType = resType
  elif types.len > 1:
    ## TODO: apply heuristic rules to pick "most likely"? Done in `assignType` below
    result = heuristicType
  else:
    result = heuristicType

proc assignType(heuristicType: FormulaTypes, typ: PossibleTypes, arg = 0): FormulaTypes =
  case typ.kind
  of tkExpression:
    if typ.types.len > 0:
      # take the type with the highest priority as the input type
      let typs = typ.types.sortTypes()
      if typs.len > 0:
        result = FormulaTypes(inputType: heuristicType.inputType,
                              resType: ident(typs[^1]))
      else:
        result = heuristicType
    else:
      result = heuristicType
  of tkProcedure:
    if typ.procTypes.len > 0:
      # access the `arg` (by default 0) argument to the command / ... to get its type
      # filter out all possible input types and use it
      var inTypes = newSeq[NimNode]()
      for el in typ.procTypes:
        if el.inputTypes.len > arg:
          inTypes.add el.inputTypes[arg]
      let inTypsSorted = inTypes.sortTypes()
      if inTypsSorted.len > 0:
        result = FormulaTypes(inputType: ident(inTypsSorted[^1]),
                              resType: heuristicType.resType)
      else:
        result = heuristicType
      if result.resType.kind == nnkEmpty:
        # only use output type if not set and pick highest priority one
        var outTyps = newSeq[NimNode]()
        for el in typ.procTypes:
          if el.resType.isSome:
            outTyps.add el.resType.get
        let outTypsSorted = outTyps.sortTypes()
        if outTypsSorted.len > 0:
          result.resType = ident(outTypsSorted[^1])
    else:
      result = heuristicType
  else:
    result = heuristicType

proc detNumArgs(n: NimNode): int =
  case n.kind
  of nnkCall, nnkCommand, nnkPrefix:
    # the `"command"` is 1 we need to subtract
    result = n.len - 1
  of nnkInfix:
    result = 2
  of nnkDotExpr:
    result = 1
  else:
    result = 1

proc argsValid(pt: ProcType, args: seq[PossibleTypes]): bool =
  ## This procedure removes all `ProcTypes` from the input `pt` that do not match the given
  ## `args` (excluding the impure indices!)
  ## The `ProcTypes` need to contain all input types (even ones we do not support as DFs)
  ## and we simply check if the args (possibly not of allowed types in DF due to being local vars)
  ## match these types. If a mismatch is found, the entry is deleted.
  ## Note: The arguments may be procedures themselves. In that case we check if the output types
  ## of these procedures match the inputs.
  ## If something has multiple overloads in the args (shouldn't be possible *I think*), we simply
  ## check for `any` match.
  result = true
  if pt.inputTypes.len < args.len: return false
  for i, inArg in pt.inputTypes:
    # `impure` arguments are `tkNone`. Even might have impure indices for which we could determine
    # type information!
    if i >= args.len: return true # either we have already returned or we
                                  # return here, as we lack arguments. This is the case
                                  # for procs with *defaults*. A default is always true.
    let arg = args[i]
    case arg.kind
    of tkExpression:
      var anyTyp = false
      for t in arg.types:
        if typesMatch(inArg, t):
          anyTyp = true
          break
      if not anyTyp:
        return false
    of tkProcedure:
      for argPt in arg.procTypes:
        var anyTyp = false
        if argPt.resType.isSome and typesMatch(inArg, argPt.resType.get):
          anyTyp = true
        if not anyTyp:
          return false
    else:
      discard

proc filterValidProcs(pTypes: var PossibleTypes, n: NimNode,
                      chTyps: seq[PossibleTypes]) =
  ## removes all proc types form `pTypes` that do not pass the conditions on
  ## the other arguments in form of the child types `chTyps` and the
  ## wildcards in form of "impure" indices. For impure indices the `PossibleType` is
  ## most likely `tkNone` (but may have type information for certain trees).
  if pTypes.kind == tkProcedure:
    var idx = 0
    while idx < pTypes.procTypes.len:
      let pt = pTypes.procTypes[idx]
      if not pt.argsValid(chTyps):
        pTypes.procTypes.delete(idx)
        continue
      inc idx
  # else there's nothing to remove

proc determineChildTypesAndImpure(n: NimNode, tab: Table[string, NimNode]): (seq[int], seq[PossibleTypes]) =
  var impureIdxs = newSeq[int]()
  var chTyps = newSeq[PossibleTypes]()
  for i in 1 ..< n.len:
    let typ = tab.getTypeIfPureTree(n[i], detNumArgs(n[i]))
    chTyps.add typ
    ## add as impure iff it is actually pure and we could ``not`` determine a type
    if not n[i].isPureTree: # and typ.kind == tkNone:
      # i - 1 is impure idx, because i == 0 is return type of procedure
      impureIdxs.add i - 1
  result = (impureIdxs, chTyps)

proc determineTypesImpl(n: NimNode, tab: Table[string, NimNode], heuristicType: var FormulaTypes): seq[Assign] =
  ## This procedure tries to determine type information from the typed symbols stored in `TypedSymbols`,
  ## so that we can override the `heuristicType`, which was determined in a first pass. This is to then
  ## create `Assign` objects, which store the column / index references and give them the type information
  ## that is required. That way we can automatically determine types for certain operations. For example:
  ##
  ## .. code-block:: nim
  ##         ## ```
  ##    proc max(x: int, y: string, z: float, b: int)
  ##    f{ max(idx("a"), "hello", 5.5, someInt()) }
  ##
  ## will automatically determine that column `a` needs to be read as an integer due to the placement
  ## as first argument of the procedure `max`. `max` is chosen because it is a common overload.
  # `localTypes` stores the local deduced type so that we can keep track of the last
  # type encountered in the AST
  var localTypes = heuristicType
  if n.isPureTree:
    return
  case n.kind
  of nnkCall, nnkCommand, nnkPrefix:
    if n.isColCall:
      result.add addColRef(n, heuristicType, byTensor)
    elif n.isIdxCall:
      result.add addColRef(n, heuristicType, byIndex)
    else:
      ## in this case is a regular call
      ## determine type information from the procedure / w/e. May be `tkNone` if symbol is e.g. generic
      var cmdTyp = tab.getTypeIfPureTree(n[0], detNumArgs(n))
      if not n[0].isPureTree:
        let res = determineTypesImpl(n[0], tab, heuristicType)
        result.add res
      else:
        doAssert n[0].isPureTree, "If this wasn't a pure tree, it would be a col reference!"
        ## for each argument to the call / cmd get the type of the argument.
        ## find then find the procedure / cmd /... that satisfies all requirements
        ## e.g.
        ## ```
        ## proc max(x: int, y: string, z: float, b: int)
        ## f{ max(idx("a"), "hello", 5.5, someInt()) }
        ## ```
        ## needs to restrict to this specific `max` thanks to the arguments `y, z, b`
        ## Arguments are only looked at for their *output* type, because that is the input to
        ## the command / call / ...
        # first extract all possible types for the call/cmd/... arguments
        let (impureIdxs, chTyps) = determineChildTypesAndImpure(n, tab)
        # remove all mismatching proc types
        cmdTyp.filterValidProcs(n, chTyps)
        # can use the type for the impure argument
        for idx in impureIdxs:
          localTypes = assignType(heuristicType, cmdTyp, arg = idx)
          heuristicType = localTypes
          result.add determineTypesImpl(
            # idx + 1 because we shift it down by 1 when adding to `impureIdxs`
            n[idx + 1], tab,
            heuristicType)
  of nnkAccQuoted, nnkCallStrLit, nnkBracketExpr:
    if n.nodeIsDf or n.nodeIsDfIdx:
      if n.nodeIsDf and not n.nodeIsDfIdx:
        result.add addColRef(n, heuristicType, byTensor)
      elif heuristicType.inputType.isColumnType():
        result.add addColRef(n, heuristicType, byTensor)
      else:
        result.add addColRef(n, heuristicType, byIndex)
    else:
      for ch in n:
        result.add determineTypesImpl(ch, tab, heuristicType)
    ## TODO: need to handle regular `nnkBracketExpr`. Can this appear? If pure we wouldn't be here
  of nnkInfix:
    let lSym = buildName(n[0])
    var infixType: PossibleTypes
    if lSym in tab: # the symbol should really be in `tab`. Let's try to continue otherwise
      let nSym = tab[lSym]
      doAssert not (n[1].isPureTree and n[2].isPureTree), "Both infix subtrees cannot be pure. We wouldn't have entered"
      # determine type of infix symbol
      infixType = nSym.findType(numArgs = detNumArgs(n))
    # first extract all possible types for the infix arguments
    let (impureIdxs, chTyps) = determineChildTypesAndImpure(n, tab)
    case infixType.kind
    of tkProcedure:
      infixType.filterValidProcs(n, chTyps)
      # can use the type for the impure argument
      for idx in impureIdxs:
        localTypes = assignType(heuristicType, infixType, arg = idx)
        heuristicType = localTypes
        result.add determineTypesImpl(
          # idx + 1 because we shift it down by 1 when adding to `impureIdxs`
          n[idx + 1], tab,
          heuristicType)
    of tkExpression, tkNone:
      ## TODO: we can remove this, right? There can never be a result here I think
      let typ1 = tab.getTypeIfPureTree(n[1], detNumArgs(n))
      let typ2 = tab.getTypeIfPureTree(n[2], detNumArgs(n))
      let matching1 = matchingTypes(typ1, infixType)
      let matching2 = matchingTypes(typ2, infixType)
      doAssert matching1.len == 0 and matching2.len == 0, " this is not useless ??"
      localTypes = assignType(heuristicType, matching2)
      heuristicType = localTypes
      result.add determineTypesImpl(n[1], tab,
                                    heuristicType)
      localTypes = assignType(heuristicType, matching1)
      heuristicType = localTypes
      result.add determineTypesImpl(n[2], tab,
                                    heuristicType)

  of nnkDotExpr:
    ## dot expression is similar to infix, but only has "one argument".
    ## index 0 is our "operator" and index 1 our "argument"
    ## In essence the impure node can never be the last node, right? That would mean something like
    ## `a.myCall().b.idx("a")`
    ## which does not really make sense.
    doAssert not (n[0].isPureTree and n[1].isPureTree), "Not both trees can be pure"
    # let typ0 = tab.getTypeIfPureTree(n[0], detNumArgs(n))
    let typ1 = tab.getTypeIfPureTree(n[1], detNumArgs(n))
    doAssert n[1].isPureTree, "Impure tree as second child to `nnkDotExpr` does not make sense"
    # extract types from `typ1`. Since `typ1` receives `n[0]` as its input, we can use
    # it's type or input (argument 0 technically only!) as the type for the impure branch
    localTypes = assignType(heuristicType, typ1)
    heuristicType = localTypes
    result.add determineTypesImpl(n[0], tab,
                                  heuristicType)
  of nnkIfStmt:
    # Could add `ifExpr` because there we know that result type is type of argument. But better to rely on
    # type hints here (at least for now).
    # check all branches
    for branch in n:
      result.add determineTypesImpl(branch, tab, heuristicType)
  else:
    for ch in n:
      result.add determineTypesImpl(ch, tab, heuristicType)

  # if we are not looking at a StmtList assign the heuristic the current localTypes. It
  # acts as a secondary return type
  if n.kind != nnkStmtList:
    heuristicType = localTypes

proc determineTypes(loop: NimNode, tab: Table[string, NimNode]): Preface =
  ## we give an empty node as return to fill it in a top down way. Result is
  ## determined at top level. We go down until we find a result type, if any.
  ## otherwise we will use the heuristics in the main code below.
  var heuristicType = FormulaTypes(inputType: newEmptyNode(),
                                   resType: newEmptyNode())
  let args = determineTypesImpl(loop, tab, heuristicType)
  result = Preface(args: args, resType: heuristicType.resType)

proc getGenericDataFrameType(n: NimNode): NimNode =
  case n.kind
  of nnkBracketExpr:
    if n[0].strVal.normalize in ["datatable"]:
      result = n[1]
    else:
      error("Invalid args : " & $n.treerepr)
  of nnkSym:
    if n.strVal.normalize == "dataframe":
      result = ident("Column")
    else:
      result = n.getTypeInst.getGenericDataFrameType()
  else: error("Invalid arg: " & $n.treerepr)

proc extractDataFrameType(nOpt: Option[NimNode]): Option[NimNode] =
  if nOpt.isSome:
    result = some(nOpt.get.getGenericDataFrameType())

proc parseOptionValue(n: NimNode): Option[FormulaKind] {.used.} =
  ## parses the AST of a `FormulaKind` into an `Option[T]` at CT
  ## Note: shouldn't there be an easier way?...
  expectKind n, nnkObjConstr
  doAssert n[0][0].kind == nnkSym and n[0][0].strVal == "Option"
  doAssert n[0][1].kind == nnkSym and n[0][1].strVal == "FormulaKind"
  doAssert n.len == 3
  if n[2].kind == nnkExprColonExpr and n[2][1].kind == nnkSym:
    if n[2][1].strVal == "true":
      # parse the number
      doAssert n[1][1].kind == nnkCall
      doAssert n[1][1][0].kind == nnkSym and n[1][1][0].strVal == "FormulaKind"
      result = some(FormulaKind(n[1][1][1].intVal))
    else:
      result = none(FormulaKind)
  else:
    error("Bad input node " & $n.repr & " in `parseOptionValue`.")

import macrocache # needed only here
const TypeNames = CacheTable"ColTypeNames"
proc genClosureRetType(preface: Preface, resType: NimNode, dfType: Option[NimNode]): NimNode =
  let typs = if dfType.isSome:
               dfType.get.columnToTypes()
             else:
               preface.accumulateTypes()
  ## replace mapIt!
  let name = genColNameStr(concat(typs.mapIt(ident(it)), @[resType]))
  if name != "Column" and name notin TypeNames:
    error("The column type `" & $name & "` has not been generated yet. If you haven't added " &
      "a column using this type to a DF yet, call `patchColumn` with the type.")
  result = TypeNames[name]

macro compileFormulaImpl*(rawName: static string,
                          funcKind: static FormulaKind): untyped =
  ## Second stage of formula macro. The typed stage of the macro. It's important that the macro
  ## is typed, as otherwise we risk that it is evaluated ``before`` the `addSymbols` calls, if
  ## we are within a generic procedure. That leads to the CT tables being empty. By making it
  ## typed (which we can do, because we store all problematic AST into the CT tables), we
  ## force evaluation to the same compilation stage as `addSymbols`.
  ##
  ## Extracts the typed symbols from `TypedSymbols` CT table and uses it to determine possible
  ## types for column references.
  var fct = Formulas[rawName]
  var typeTab = initTable[string, NimNode]()
  if rawName in TypedSymbols:
    typeTab = TypedSymbols[rawName]
  # extract df if any, (possibly) use it to determine `DataFrame` argument type
  fct.df = if InputDF in typeTab: some(typeTab[InputDF]) else: none[NimNode]()
  # generate the `preface`
  ## generating the preface is done by extracting all references to columns,
  ## using their names as `tensor` names (not element, since we in the general
  ## formula syntax can only refer to full columns)
  ## Explicit `df` usage (`df["col"][idx]` needs to be put into a temp variable,
  ## `genSym("col", nskVar)`)
  fct.preface.add determineTypes(fct.loop, typeTab)
  # use heuristics to determine a possible input / output type. Input type hint used to
  # possibly set return type if heuristics don't provide anything
  var typ = determineHeuristicTypes(fct.loop, typeHint = fct.typeHint,
                                    name = fct.rawName)

  var resTypeFromSymbols = newEmptyNode()
  var allScalar = true
  var allAgree = true
  ## Modify the result type in case all Assigns agree on one type
  ## TODO: need to think the assignment of `resTypeFromSymbols` over again. Idea is simply to
  ## use the `Assign` result types in case they all agree. Make sure this is correct.
  for arg in mitems(fct.preface.args):
    if typ.inputType.isSome and not arg.colType.typeAcceptable:
      arg.colType = typ.inputType.get
    if typ.resType.isSome and not arg.resType.typeAcceptable:
      arg.resType = typ.resType.get
    if resTypeFromSymbols.kind == nnkEmpty:
      resTypeFromSymbols = arg.resType
    elif resTypeFromSymbols.repr != arg.resType.repr:
      allAgree = false
    if arg.asgnKind == byIndex:
      allScalar = false
    # apply user given type hints rigorously
    if fct.typeHint.inputType.isSome and not arg.node.hasExplicitTypeHint:
      arg.colType = fct.typeHint.inputType.get
    if fct.typeHint.resType.isSome:
      arg.resType = fct.typeHint.resType.get

    ## XXX: extend to check whether we have an input DF for type information. If so and if
    ## user has given explicit type hint for an idx/col call, check that the two pieces of
    ## info match. Else CT error!

    # check if any is `Empty` or column type not acceptable, if so error out at CT
    if arg.colType.kind == nnkEmpty or arg.resType.kind == nnkEmpty:
      error("Could not determine data types of tensors in formula:\n" &
        "  name: " & $fct.name & "\n" &
        "  formula: " & $fct.loop.repr & "\n" &
        "  data type: " & $arg.colType.repr & "\n" &
        "  output data type: " & $arg.resType.repr & "\n" &
        "Consider giving type hints via: `f{T -> U: <theFormula>}`")
    elif not arg.colType.typeAcceptable:
      error("Input type for column " & $arg.node.repr & " in formula " &
        $fct.rawName & " is ambiguous.\n" &
        "Column type determined to be: " & $arg.colType.repr & "\n" &
        "Consider giving type hints via: `f{T -> U: <theFormula>}` where " &
        "`T` is the input type (`U` might not be required).")

  fct.resType = if fct.typeHint.resType.isSome:
                  fct.typeHint.resType.get
                elif resTypeFromSymbols.kind != nnkEmpty and allAgree and
                     typ.resType.isSome and
                     fct.preface.resType.typeAcceptable: # the determined type must be acceptable (i.e. not generic)
                  # Take the highest priority type between symbol deduced one and
                  # heuristic one
                  let typOrdered = sortTypes(
                    heuristic = @[typ.resType.get],
                    deduced = @[fct.preface.resType])
                  ident(typOrdered[^1])
                elif resTypeFromSymbols.kind != nnkEmpty and allAgree:
                  resTypeFromSymbols
                else: typ.resType.get
  # check if result type still not acceptable, if so error out
  if not fct.resType.typeAcceptable:
    error("Output type for formula " & $fct.rawName & " is ambiguous.\n" &
      "Result type determined to be: " & $fct.resType.repr & "\n" &
      "Consider giving type hints via: `f{T -> U: <theFormula>}` where" &
      "`U` is the output type (`T`, input type, is required as well).")

  # possibly overwrite funcKind
  if funcKind != fkNone:
    ## raise error in case given function kind does not match what we expect
    if allScalar and funcKind != fkScalar:
      warning("Formula " & $fct.rawName & " has a mismatch between given formula " &
        "kind:\n\t`" & $funcKind & "` (mapping)\nand automatically determined formula kind:\n\t" &
        "<< (reducing)\nPlease adjust the given kind to `<<`.")
    elif not allScalar and funcKind == fkScalar:
      ## user seems to be accessing a tensor in context of a scalar body. Probably wants
      ## to accumulate with some condition. Generate a for loop with explicit accumulation
      fct.generateLoop = true
    # use the user given formula kind
    fct.funcKind = funcKind
  else:
    fct.funcKind = if allScalar: fkScalar else: fkVector

  # set the column return type
  fct.dfType = fct.df.extractDataFrameType()
  fct.colResType = genClosureRetType(fct.preface, fct.resType, fct.dfType)
  case fct.funcKind
  of fkVector: result = compileVectorFormula(fct)
  of fkScalar: result = compileScalarFormula(fct)
  else: error("Unreachable branch. `fkAssign` and `fkVariable` are already handled!")

proc flattenStmtList(n: NimNode): NimNode =
  ## remove stmt lists from n at top level
  case n.kind
  of nnkStmtList:
    doAssert n.len == 1
    result = flattenStmtList(n[0])
  else:
    result = copyNimTree(n)

proc parseTypeHint(n: var NimNode): TypeHint =
  ## extracts possible type hints from the node `T -> U: ...`
  proc parseTypeHintStmt(n: NimNode): TypeHint =
    case n.kind
    of nnkIdent:
      # simple type hint for tensor input type
      result = TypeHint(inputType: some(n))
      # resType is `None`
    of nnkInfix:
      doAssert n.len == 3
      doAssert eqIdent(n[0], ident"->")
      # type hint of tensor + result
      result = TypeHint(inputType: some(n[1]),
                        resType: some(n[2]))
    else: error("Unsupported type hint: " & $n.repr)
  case n.kind
  of nnkExprColonExpr:
    result = parseTypeHintStmt(n[0])
    n = flattenStmtList(n[1])
  of nnkStmtList:
    result = parseTypeHintStmt(n[0])
  else: discard # no type hint

proc isPureFormula(n: NimNode): bool =
  ## Checks if the input tree `n` is a pure formula. A pure formula is any Nim AST
  ## that does not contain a column reference.
  result = true
  if n.len > 0:
    for ch in n:
      result = result and isPureFormula(ch)
      if not result:
        return result
  case n.kind
  of nnkAccQuoted, nnkCallStrLit: result = false
  of nnkBracketExpr:
    if nodeIsDf(n) or nodeIsDfIdx(n):
      result = false
  of nnkCall:
    if nodeIsDf(n) or nodeIsDfIdx(n):
      result = false
  else: discard

proc compileFormula(n: NimNode, fullNode = false, df: NimNode = newEmptyNode()): NimNode =
#macro compileFormula*(n: untyped, df = newEmptyNode()): untyped =
  ## Preprocessing stage of formula macro. Performs preprocessing steps and extracts
  ## basic information:
  ## - possible type hints
  ## - possible AST reordering if `~` involved
  ## - extracts possible `~`, `<<`, `<-` symbols
  ## - generates result column name (from possible LHS)
  ## - generates formula name
  ## - extracts pure subtrees and adds them to `TypedSymbols` CT table
  ## - calls second stage `compileFormulaImpl`

  ## Generate a preliminary `FormulaCT` for the information we can collect in this
  ## stage already
  var fct = FormulaCT()
  # starting with a possible preface
  var node = n
  ##
  ## If `df` is given, use the generic type of the DF to fill the closure argument's
  ## type field. Otherwise default to `DataTable[Column]`
  var isAssignment = false
  var isReduce = false
  var isVector = false
  var typeHint: TypeHint
  if fullNode:
    doAssert n.kind == nnkStmtList
    let prefaceNode = extractCall(n, "preface")
    if prefaceNode.kind != nnkNilLit:
      fct.preface = parsePreface(extractCall(n, "preface"))
    # get the `typeHint:` part including the `nnkStmtList`
    var typeHintNode = extractCall(node, "typeHint")
    if typeHintNode.kind != nnkNilLit:
      typeHintNode = typeHintNode[1]
      typeHint = typeHintNode.parseTypeHint
    node = extractCall(node, "loop")[1][0]
  else:
    typeHint = parseTypeHint(node)
  let tilde = recurseFind(node,
                          cond = ident"~")

  var formulaName = newNilLit()
  var formulaRhs = newNilLit()
  if tilde.kind != nnkNilLit and node[0].strVal != "~":
    # only reorder the tree, if it does contain a tilde and the
    # tree is not already ordered (i.e. nnkInfix at top with tilde as
    # LHS)
    let replaced = reorderRawTilde(node, tilde)
    formulaName = buildResultColName(tilde[1])
    formulaRhs = replaced
    isVector = true
  elif tilde.kind != nnkNilLit:
    # already tilde at level 0: infix(~, arg1, arg2)
    formulaName = buildResultColName(node[1])
    formulaRhs = node[2]
    isVector = true
  else:
    # no tilde in node
    # check for `<-` assignment
    if node.len > 0 and eqIdent(node[0], ident"<-"):
      formulaName = buildResultColName(node[1])
      formulaRhs = node[2]
      isAssignment = true
    # check for `<<` reduction
    elif node.len > 0 and eqIdent(node[0], ident"<<"):
      formulaName = buildResultColName(node[1])
      formulaRhs = node[2]
      isReduce = true
    else:
      formulaRhs = node

  let fnName = buildName(node)
  let rawName = newLit fnName
  if isPureFormula(formulaRhs) and tilde.kind == nnkNilLit:
    # simply output a pure formula node that does not contain a `~`
    # (and thus forces a constant mapping)
    if not isAssignment:
      ## TODO: allow in formulaExp.nim
      let C = ident"Column"
      result = quote do:
        Formula[`C`](kind: fkVariable,
                     name: `rawName`,
                     val: %~ `formulaRhs`)
    else:
      ## TODO: allow in formulaExp.nim
      let C = ident"Column"
      result = quote do:
        Formula[`C`](kind: fkAssign,
                     name: `rawName`,
                     lhs: `formulaName`,
                     rhs: %~ `formulaRhs`)
  elif isAssignment:
    error("Assignment of unpure formulas (column reference in formula body) is " &
      "unsupported. Use a reducing `<<` or mapping `~` formula.")
  else:
    ## The `funcKind` here is the ``preliminary`` determination of our
    ## FunctionKind. It may be overwritten at a later time in case the
    ## formula does not use explicit `~`, `<<` or `<-`, i.e. `f{<someOperation>}`
    ## without LHS.
    ## We have 2 pieces of information to go by
    ## -`df["<someCol>"]` in the body, refers to an operation on an explicit column,
    ##   -> should imply `fkScalar` (and has to be an arg of a proc call)
    ## - type information of all symbols that are not column references, which
    ##   might be reducing operations (`mean(df["someCol"])` etc.).
    let funcKind = if isReduce: fkScalar
               elif isVector: fkVector
               else: fkNone

    # assign the name
    fct.name = if formulaName.kind != nnkNilLit: formulaName else: newLit(fnName)
    fct.rawName = fnName
    # assign the loop
    fct.loop = if formulaRhs.kind == nnkStmtList: formulaRhs
               else: newStmtList(formulaRhs)
    fct.typeHint = typeHint
    # `fct.df` is only assigned after typed pass is done (in `compileFormulaImpl`)
    ## assign to global formula CT table
    Formulas[fct.rawName] = fct

    result = newStmtList()
    let syms = extractSymbols(formulaRhs)
    for s in syms:
      let sName = buildName(s)
      result.add quote do:
        when checkSymbolIsValid(`s`):
          addSymbols(`rawName`, `sName`, `s`)
    # now add input data frame if any
    if df.kind != nnkEmpty:
      result.add quote do:
        addSymbols(`rawName`, `InputDF`, `df`)
    var cpCall = nnkCall.newTree(ident"compileFormulaImpl",
                                 rawName,
                                 newLit funcKind)
    result.add cpCall

macro dfFn*(df, fn: untyped): untyped =
  var fn = fn
  if fn.kind == nnkCurlyExpr:
    fn = fn[1]
  result = compileFormula(fn, df = df)

macro `{}`*(x: untyped{ident}, y: untyped): untyped =
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
  ## - `<type> -> <resType>: <actualFormula>`: full type for closure.
  ##   `<type>` is the dtype used for tensors, `<resType>` the resulting type
  ## - `df[<someIdent/Sym>]`: to access columns using identifiers / symbols
  ##   defined in the scope
  ## - `idx`: can be used to access the loop iteration index
  if x.strVal == "f":
    result = compileFormula(y)

macro `fn`*(x: untyped): untyped =
  let arg = if x.kind == nnkStmtList: x[0] else: x
  doAssert arg.kind in {nnkCurly, nnkTableConstr}
  result = compileFormula(arg[0])

macro formula*(n: untyped): untyped =
  result = compileFormula(n, true)
