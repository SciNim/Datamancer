import dataframe, value, column

import memfiles, streams, strutils, tables, parsecsv, sequtils
# for reading CSV files from URLs
import httpclient
# for `showBrowser`
import browsers, strformat, os

proc checkHeader(s: Stream, fname, header: string, colNames: seq[string]): bool =
  ## checks whether the given file contains the header `header`
  result = true
  if header.len > 0:
    var headerBuf: string
    if s.peekLine(headerBuf):
      result = headerBuf.startsWith(header)
    else:
      raise newException(IOError, "The input file " & $fname & " seems to be empty.")
  elif colNames.len > 0:
    # given some column names and a "header" without a symbol means we assume
    # there is no real header. If there is a real header in addition, user has
    # to use `skipLines = N` to skip it.
    result = false

proc readCsv*(s: Stream,
              sep = ',',
              header = "",
              skipLines = 0,
              colNames: seq[string] = @[],
              fname = "<unknown>"): OrderedTable[string, seq[string]] =
  ## returns a `Stream` with CSV like data as a table of `header` keys vs. `seq[string]`
  ## values, where idx 0 corresponds to the first data value
  ## The `header` field can be used to designate the symbol used to
  ## differentiate the `header`. By default `#`.
  ## `colNames` can be used to provide custom names for the columns.
  ## If any are given and a header is present with a character indiciating
  ## the header, it is automatically skipped. ``However``, if custom names are
  ## desired and there is a real header without any starting symbol (i.e.
  ## `header.len == 0`), please use `skipLines = N` to skip it manually!
  # first check if the file even has a header of type `header`
  let hasHeader = checkHeader(s, fname, header, colNames)

  var parser: CsvParser
  open(parser, s, fname, separator = sep, skipInitialSpace = true)

  if colNames.len > 0:
    # if `colNames` available, use as header
    parser.headers = colNames
    if hasHeader:
      # and skip the real header
      discard parser.readRow()
  elif hasHeader:
    # read the header and use it
    parser.readHeaderRow()
  else:
    # file has no header nor user gave column names, raise
    raise newException(IOError, "Input neither has header starting with " &
      $header & " nor were column names provided!")

  result = initOrderedTable[string, seq[string]]()
  # filter out the header, delimiter, if any
  parser.headers.keepItIf(it != header)

  # possibly strip the headers and create the result table of columns
  var colHeaders: seq[string]
  for colUnstripped in items(parser.headers):
    let col = colUnstripped.strip
    colHeaders.add col
    result[col] = newSeqOfCap[string](5000) # start with a reasonable default cap

  # parse the actual file using the headers
  var lnCount = 0
  while readRow(parser):
    if lnCount < skipLines:
      inc lnCount
      continue
    for i, col in parser.headers:
      parser.rowEntry(col).removePrefix({' '})
      parser.rowEntry(col).removeSuffix({' '})
      result[colHeaders[i]].add parser.rowEntry(col)
  parser.close()

template copyBuf(data: ptr UncheckedArray[char], buf: var string,
                 idx, colStart: int): untyped =
  let nIdx = idx - colStart
  if nIdx > 0:
    buf.setLen(nIdx) # will auto reallocate if `len` is larger than capacity!
    copyMem(buf[0].addr, data[colStart].addr, nIdx)
  else:
    buf.setLen(0)

template parseHeaderCol(data: ptr UncheckedArray[char], buf: var string,
                        colNames: var seq[string],
                        header: string, sep, quote: char,
                        idx, colStart: int): untyped =
  copyBuf(data, buf, idx, colStart)
  if col == 0:
    if not buf.startsWith(header):
      raise newException(IOError, "Unexpected column name at column 0, missing " &
        "expected header `" & header & "`. Found " & buf)
    else:
      buf.removePrefix(header)
      # and remove possible whitespace
      buf = buf.strip(chars = Whitespace + {quote})
  let bufStripped = buf.strip(chars = Whitespace + {quote})
  if bufStripped.len == 0 and sep in {' ', '\t'}:
    # don't add any name because we are dealing with a space before the
    # first column. We don't care about the `col` being off while parsing headers as
    # we do not use it to access data.
    # This is required over the `if` in the `parseLine` separator, because of possible
    # files using header symbols e.g. '#'
    discard
  elif bufStripped.len == 0:
    # in case a column does not have a name, we use `Unnamed` similar to pandas
    let numUnknown = colNames.filterIt(it.startsWith("Unnamed"))
    colNames.add("Unnamed" & $numUnknown.len)
  else:
    colNames.add bufStripped

template guessType(data: ptr UncheckedArray[char], buf: var string,
                   colTypes: var seq[ColKind],
                   col, idx, colStart, numCols: untyped): untyped =
  # only determine types for as many cols as in header
  if col < numCols:
    copyBuf(data, buf, idx, colStart)
    if colTypes[col] == colNone: # do not overwrite if already set
      if buf.len == 0:
        # inconclusive, need to look at next line
        colTypes[col] = colNone
      elif buf.isInt:
        colTypes[col] = colInt
      elif buf.isNumber:
        colTypes[col] = colFloat
      elif buf.isBool:
        colTypes[col] = colBool
      else:
        colTypes[col] = colString

proc i64(c: char): int {.inline.} = int(ord(c) - ord('0'))

proc pow10(e: int): float {.inline.} =
  const p10 = [1e-22, 1e-21, 1e-20, 1e-19, 1e-18, 1e-17, 1e-16, 1e-15, 1e-14,
               1e-13, 1e-12, 1e-11, 1e-10, 1e-09, 1e-08, 1e-07, 1e-06, 1e-05,
               1e-4, 1e-3, 1e-2, 1e-1, 1.0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7,
               1e8, 1e9]                        # 4*64B cache lines = 32 slots
  if -22 <= e and e <= 9:
    return p10[e + 22]                          # common case=small table lookup
  result = 1.0
  var base = 10.0
  var e = e
  if e < 0:
    e = -e
    base = 0.1
  while e != 0:
    if (e and 1) != 0:
      result *= base
    e = e shr 1
    base *= base

type
  RetType = enum
    rtInt, rtFloat, rtNaN, rtInf, rtError

func normalizeChar(c: char): char =
  # normalize uppercase chars to lowercase
  if c in {'A' .. 'Z'}:
    chr(ord(c) + (ord('a') - ord('A')))
  else:
    c

func tryParse(toEat: seq[char], data: ptr UncheckedArray[char], idx: var int,
              sep: char,
              retTyp: RetType, retVal: float, floatVal: var float): RetType =
  ## tries to parse certain strings `NaN`, `Inf` into floats
  ##
  ## Returns `rtError` if it cannot
  var eatIdx = 0
  while data[idx] != '\0' and                     # end if end of buffer
        data[idx] != sep and                      # end if separator
        data[idx].normalizeChar == toEat[eatIdx]: # continue if still expected
    inc eatIdx
    inc idx
  if eatIdx == toEat.len:                         # matched exactly `toEat`
    floatVal = retVal                             # assign expected value to return
    return retTyp
  else:
    return rtError


proc parseNumber(data: ptr UncheckedArray[char],
                 sep: char, # if this sep is found parsing ends
                 idxIn: int,
                 intVal: var int, floatVal: var float): RetType {.inline, noinit.} =
  ## this code is taken and adapted from @c-blake's code in Nim PR #16055.
  # Parse/validate/classify all at once, returning the type we parsed into
  # and if not `rtError` the `intVal/floatVal` will store the parsed number
  if data[idxIn] in {sep, '\n', '\r', '\0'}:    # empty field in CSV
    floatVal = NaN
    return rtNaN
  const Sign = {'+', '-'} # NOTE: `parseFloat` can generalize this to INF/NAN.
  var idx = idxIn
  var noDot = false
  var exp = 0
  var p10 = 0
  var pnt = -1                                  # find '.' (point); do digits
  var nD = 0
  var giant = false
  intVal = 0                                    # build intVal up from zero..
  if data[idx] in Sign:
    idx.inc                                     # skip optional sign
  while data[idx] != '\0':                      # ..and track scale/pow10.
    if data[idx] notin Digits:
      if data[idx] != '.' or pnt >= 0:
        break                                   # a second '.' is forbidden
      pnt = nD                                  # save location of '.' (point)
      nD.dec                                    # undo loop's nD.inc
    elif nD < 18:                               # 2**63==9.2e18 => 18 digits ok
      intVal = 10 * intVal + data[idx].i64      # core ASCII->binary transform
    else:                                       # 20+ digits before decimal
      giant = true #XXX condition should be more precise than "18 digits"
      p10.inc                                   # any digit moves implicit '.'
    idx.inc
    nD.inc
  if data[idxIn] == '-':
    intVal = -intVal                            # adjust sign

  if pnt < 0:                                   # never saw '.'
    if nD == 0 and
       (data[idx] == '\0' or data[idx] == sep): # just a sign `+`, `-`
      return rtError
    pnt = nD; noDot = true                      # so set to number of digits
  elif nD == 1 or (pnt == 0 and nD == 0):
    return rtError                              # ONLY "[+-]*\.*"

  # `\0` is necessary to support parsing until the end of the file in case of no line break
  if data[idx] notin {'\0', sep, '\n', '\r', 'e', 'E'}: ## TODO: generalize this?
    # might be "nan", "inf" or "-inf" or some other invalid string
    var ret = tryParse(@['n', 'a', 'n'], data, idx,
                       sep,
                       rtNaN,                   # return rtNaN if parsed
                       NaN,                     # assign NaN
                       floatVal)                # to `floatVal` if true
    if ret == rtNaN: return ret
    ret = tryParse(@['i', 'n', 'f'], data, idx,
                   sep,
                   rtInf,                       # return rtInf if parsed
                   Inf,                         # assign Inf
                   floatVal)                    # to `floatVal` if true
    if ret == rtInf:
      if data[idxIn] == '-': floatVal = -Inf    # invert sign
      return ret

    return ret # else can return as it will be `rtError`

  if data[idx] in {'E', 'e'}:                   # optional exponent
    if idx == idxIn: return rtError             # starts with `E` / `e`. Not a valid float
                                                # important for any string starting with `E`/`e` as well
    idx.inc
    let i0 = idx
    if data[idx] in Sign:
      idx.inc                                   # skip optional sign
    while data[idx] in Digits:                  # build exponent
      exp = 10 * exp + data[idx].i64
      idx.inc
    if data[i0] == '-':
      exp = -exp                                # adjust sign
  elif noDot: # and intVal < (1'i64 shl 53'i64) ? # No '.' & No [Ee]xponent
    ## TODO: handle giant?
    #if giant:
    #  return rtError
    #  #copyBuf(data, strVal, idx, idxIn)
    return rtInt                                # mark as integer
  exp += pnt - nD + p10                         # combine explicit&implicit exp
  floatVal = intVal.float * pow10(exp)          # has round-off vs. 80-bit
  ## TODO: handle giant?
  #if giant:
  #  return rtError
  #  #copyBuf(data, strVal, idx, idxIn)
  result = rtFloat                              # mark as float

template parseCol(data: ptr UncheckedArray[char], buf: var string,
                  col: var Column,
                  sep: char,
                  colTypes: seq[ColKind], colIdx, idx, colStart, row, numCols: int,
                  intVal: var int, floatVal: var float, rtType: var RetType): untyped =
  ## if there are more `,` in a row than in the header, skip it
  if likely(colIdx < numCols):
    case colTypes[colIdx]
    of colInt:
      retType = parseNumber(data, sep, colStart, intVal, floatVal)
      case retType
      of rtInt: col.iCol[row] = intVal
      of rtFloat, rtNaN, rtInf:
        # before we copy everything check if can be parsed to float, this branch will only
        # be called a single time
        col = toColumn col.iCol.astype(float)
        col.fCol[row] = floatVal # `floatVal` may be NaN, Inf or regular value
        colTypes[colIdx] = colFloat
      of rtError:
        # object column
        copyBuf(data, buf, idx, colStart)
        col = toObjectColumn col
        colTypes[colIdx] = colObject
        col.oCol[row] = %~ buf
    of colFloat:
      retType = parseNumber(data, sep, colStart, intVal, floatVal)
      case retType
      of rtInt: col.fCol[row] = intVal.float
      of rtFloat, rtNaN, rtInf: col.fCol[row] = floatVal # `floatVal` may be NaN, Inf or regular value
      of rtError:
        # object column
        copyBuf(data, buf, idx, colStart)
        col = toObjectColumn col
        colTypes[colIdx] = colObject
        col.oCol[row] = %~ buf
    of colBool:
      copyBuf(data, buf, idx, colStart)
      try:
        col.bCol[row] = parseBool buf
      except ValueError:
        # object column
        col = toObjectColumn col
        colTypes[colIdx] = colObject
        col.oCol[row] = %~ buf
    of colString:
      copyBuf(data, buf, idx, colStart)
      col.sCol[row] = buf
    of colObject:
      # try to parse as number
      retType = parseNumber(data, sep, colStart, intVal, floatVal)
      case retType
      of rtInt: col.oCol[row] = %~ intVal
      of rtFloat, rtInf: col.oCol[row] = %~ floatVal
      of rtNaN: col.oCol[row] = Value(kind: VNull)
      of rtError:
        copyBuf(data, buf, idx, colStart)
        col.oCol[row] = %~ buf
    of colConstant: discard # already set
    of colNone, colGeneric:
      raise newException(IOError, "Invalid column type to parse into: `colNone`. " &
        "This shouldn't have happened! row = " & $row & ", col = ")# & $col)

template advanceToNextRow() {.dirty.} =
  ## The steps done after a line break is found & we advance to the next row.
  ##
  ## Stored in a dirty template as we also use it while guessing types.
  inc row
  col = 0
  if data[idx] == eat and data[idx + 1] == lineBreak:
    inc idx
  colStart = idx + 1
  rowStart = idx + 1
  lastWasSep = false

template parseLine(data: ptr UncheckedArray[char], buf: var string,
                   sep, quote, lineBreak, eat: char,
                   col, idx, colStart, row, rowStart: var int,
                   lastWasSep, inQuote: var bool,
                   toBreak: static bool,
                   fnToCall: untyped): untyped =
  if unlikely(data[idx] == quote):
    inQuote = not inQuote
  elif unlikely(inQuote):
    inc idx
    # skip ahead in case we start quote
    continue
  elif unlikely(data[idx] in {lineBreak, eat}) and rowStart == idx:
    # empty line, skip
    colStart = idx + 1
    rowStart = idx + 1
  elif unlikely(data[idx] in {lineBreak, eat}):
    fnToCall
    advanceToNextRow()
    when toBreak:
      inc idx
      break
  elif unlikely(skipInitialSpace and lastWasSep and data[idx] == ' '):
    colStart = idx + 1
  elif unlikely(data[idx] == sep):
    # convert last column to data
    if (idx - colStart > 0 or col > 0 or sep notin {' ', '\t'}):
      # only parse if: we have characters to parse, unless we are not in the first
      # column and unless our separator is not "spaces" like. Idea is only ignore
      # empty (only spaces) first columns iff we are dealing with space separated files.
      # For a proper separator like ',' empty inputs are allowed at the beginning.
      fnToCall
      inc col
    colStart = idx + 1
    lastWasSep = true
  elif unlikely(data[idx] in toSkip):
    colStart = idx + 1
    lastWasSep = false
  elif unlikely(lastWasSep):
    lastWasSep = false
  else:
    discard
  inc idx

proc allColTypesSet(colTypes: seq[ColKind]): bool =
  ## checks if all column types are determined, i.e. not `colNone` the default
  result = colTypes.allIt(it != colNone)

proc readCsvTypedImpl(data: ptr UncheckedArray[char],
                      size: int,
                      lineCnt: int,
                      sep: char = ',',
                      header: string = "",
                      skipLines = 0,
                      toSkip: set[char] = {},
                      colNamesIn: seq[string] = @[],
                      skipInitialSpace = true,
                      quote = '"',
                      maxGuesses = 20,
                      lineBreak = '\n', eat = '\r'): DataFrame =
  ## Implementation of the CSV parser that works on a data array of chars.
  ##
  ## `maxGuesses` is the maximum number of rows to look at before we give up
  ## trying to determine the datatype of the column and set it to 'object'.
  result = newDataFrame()
  var
    idx = 0
    row = 0
    col = 0
    colStart = 0
    rowStart = 0
    lastWasSep = false
    inQuote = false
    buf = newStringOfCap(80)

  # 1. first parse the header
  var colNames = colNamesIn
  if colNames.len == 0:
    while idx < size:
      parseLine(data, buf, sep, quote, lineBreak, eat, col, idx, colStart, row, rowStart, lastWasSep, inQuote, toBreak = true):
        parseHeaderCol(data, buf, colNames, header, sep, quote, idx, colStart)

  if colNamesIn.len > 0 and colNamesIn.len != colNames.len:
    raise newException(IOError, "Input data contains " & $colNames.len & " columns, but " &
      "given " & $colNamesIn.len & " column names given: " & $colNamesIn)
  elif colNamesIn.len > 0:
    colNames = colNamesIn
    # reset index and row back to 0
    row = 0
    idx = 0
    col = 0

  # 1a. if `header` is set, skip all additional lines starting with header
  if header.len > 0:
    while idx < size:
      parseLine(data, buf, sep, quote, lineBreak, eat, col, idx, colStart, row, rowStart, lastWasSep, inQuote, toBreak = false):
        if col == 0 and data[colStart] != header[0]:
          break

  let numCols = colNames.len
  # 1b. skip `skipLines`
  let rowDataStart = row
  if skipLines > 0:
    while idx < size:
      parseLine(data, buf, sep, quote, lineBreak, eat, col, idx, colStart, row, rowStart, lastWasSep, inQuote, toBreak = false):
        if row - rowDataStart == skipLines:
          break
  # compute the number of skipped lines in total
  let skippedLines = row
  # reset row to 0
  row = 0

  # 2. peek the first line to determine the data types
  var colTypes = newSeq[ColKind](numCols)
  var lastIdx = idx
  var lastColStart = colStart
  var lastRow = row
  var dataColsIdx = 0
  var guessAttempts = 0
  const maxGuesses = 20
  while idx < size:
    parseLine(data, buf, sep, quote, lineBreak, eat, col, idx, colStart, row, rowStart, lastWasSep, inQuote, toBreak = true):
      guessType(data, buf, colTypes, col, idx, colStart, numCols)
      # if we see the end of the line, store the current column number
      if data[idx] in {'\n', '\r', '\l'}:
        if lastWasSep and sep in {' ', '\t'}:
          dec col # don't count "empty space columns" at end
        dataColsIdx = col
        inc guessAttempts
        if not allColTypesSet(colTypes) and # manually perform steps to go to next line and skip
           guessAttempts < maxGuesses:              # `when toBreak` logic
          advanceToNextRow()
          inc idx
          continue

  if dataColsIdx + 1 != numCols:
    raise newException(IOError, "Input data contains " & $(dataColsIdx + 1) & " in the data portion, but " &
      $numCols & " columns in the header.")
  # 2a. revert the indices (make it a peek)
  col = 0 # reset `col` to 0 regardless
  idx = lastIdx
  colStart = lastColStart
  row = lastRow

  # 2b. for columns we did not correctly determine the type, set to object
  # Note: for a *fully* empty column, we *could* also assign a constant value of VNull
  if not allColTypesSet(colTypes):
    for c in mitems(colTypes):
      if c == colNone:
        c = colObject

  # 3. create the starting columns
  var cols = newSeq[Column](numCols)
  let dataLines = lineCnt - skippedLines
  for i in 0 ..< colTypes.len:
    # create column of length:
    # lines in file - header - skipLines
    cols[i] = newColumn(colTypes[i], dataLines)
  # 4. parse the actual data
  doAssert row >= 0, "Parsing the header failed"
  var
    retType: RetType
    intVal: int
    floatVal: float
  while idx < size:
    parseLine(data, buf, sep, quote, lineBreak, eat, col, idx, colStart, row, rowStart, lastWasSep, inQuote, toBreak = false):
      parseCol(data, buf, cols[col], sep, colTypes, col, idx, colStart, row, numCols,
               intVal, floatVal, retType)
  if row + skippedLines < lineCnt:
    # missing linebreak at end of last line
    doAssert row + skippedLines == lineCnt - 1, "Line counts mismatch. " &
      $(row + skippedLines) & " lines read, expected " & $(lineCnt - 1) &
      ". Is your file using non unix line breaks? Try switching the `lineBreak` " &
      "and `eat` options to `readCsv`."
    parseCol(data, buf, cols[col], sep, colTypes, col, idx, colStart, row, numCols,
             intVal, floatVal, retType)
  for i, col in colNames:
    result[col] = cols[i]
  result.len = dataLines

func countNonEmptyLines(s: string): int =
  var idx = 0
  var lineStart = idx
  while idx < s.len:
    case s[idx]
    of '\n', '\r':
      if abs(lineStart - idx) > 0: # only count lines with data
        inc result
      if idx < s.high and s[idx] == '\r' and s[idx + 1] == '\l':
        inc idx
      inc idx
      lineStart = idx # store start of line as reference
    else: inc idx
  if lineStart != idx:
    inc result # ended with valid line w/o newline at end

proc parseCsvString*(csvData: string,
                     sep: char = ',',
                     header: string = "",
                     skipLines = 0,
                     toSkip: set[char] = {},
                     colNames: seq[string] = @[],
                     skipInitialSpace = true,
                     quote = '"',
                     maxGuesses = 20,
                     lineBreak = '\n',
                     eat = '\r'
                    ): DataFrame =
  ## Parses a `DataFrame` from a string containing CSV data.
  ##
  ## `toSkip` can be used to skip optional characters that may be present
  ## in the data. For instance if a CSV file is separated by `,`, but contains
  ## additional whitespace (`5, 10, 8` instead of `5,10,8`) this can be
  ## parsed correctly by setting `toSkip = {' '}`.
  ##
  ## `header` designates the symbol that defines the header of the CSV file.
  ## By default it's empty meaning that the first line will be treated as
  ## the header. If a header is given, e.g. `"#"`, this means we will determine
  ## the column names from the first line (which has to start with `#`) and
  ## skip every line until the first line starting without `#`.
  ##
  ## `skipLines` is used to skip `N` number of lines at the beginning of the
  ## file.
  ##
  ## `maxGuesses` is the maximum number of rows to look at before we give up
  ## trying to determine the datatype of the column and set it to 'object'.
  ##
  ## `lineBreak` is the character used to detect if a new line starts. `eat`
  ## on the other hand is simply ignore. For unix style line endings the defaults
  ## are fine. In principle for windows style endings `\r\n` the defaults *should*
  ## work as well, but in rare cases the default causes issues with mismatched
  ## line counts. In those cases try to switch `lineBreaks` and `eat` around.
  result = newDataFrame()

  ## we're dealing with ASCII files, thus each byte can be interpreted as a char
  var data = cast[ptr UncheckedArray[char]](csvData[0].unsafeAddr)
  result = readCsvTypedImpl(data, csvData.len, countNonEmptyLines(csvData),
                            sep, header, skipLines, toSkip, colNames,
                            skipInitialSpace, quote, maxGuesses, lineBreak, eat)

proc readCsvFromUrl(url: string,
              sep: char = ',',
              header: string = "",
              skipLines = 0,
              toSkip: set[char] = {},
              colNames: seq[string] = @[],
              skipInitialSpace = true,
              quote = '"'
             ): DataFrame =
  ## Reads a DF from a web URL (which must contain a CSV file)
  var client = newHttpClient()
  return parseCsvString(client.getContent(url), sep, header, skipLines, toSkip, colNames,
                        skipInitialSpace, quote)

proc readCsv*(fname: string,
              sep: char = ',',
              header: string = "",
              skipLines = 0,
              toSkip: set[char] = {},
              colNames: seq[string] = @[],
              skipInitialSpace = true,
              quote = '"',
              maxGuesses = 20,
              lineBreak = '\n',
              eat = '\r'
             ): DataFrame =
  ## Reads a DF from a CSV file or a web URL using the separator character `sep`.
  ##
  ## `fname` can be a local filename or a web URL. If `fname` starts with
  ## "http://" or "https://" the file contents will be read from the selected
  ## web server. No caching is performed so if you plan to read from the same
  ## URL multiple times it might be best to download the file manually instead.
  ## Please note that to download files from https URLs you must compile with
  ## the -d:ssl option.
  ##
  ## `toSkip` can be used to skip optional characters that may be present
  ## in the data. For instance if a CSV file is separated by `,`, but contains
  ## additional whitespace (`5, 10, 8` instead of `5,10,8`) this can be
  ## parsed correctly by setting `toSkip = {' '}`.
  ##
  ## `header` designates the symbol that defines the header of the CSV file.
  ## By default it's empty meaning that the first line will be treated as
  ## the header. If a header is given, e.g. `"#"`, this means we will determine
  ## the column names from the first line (which has to start with `#`) and
  ## skip every line until the first line starting without `#`.
  ##
  ## `skipLines` is used to skip `N` number of lines at the beginning of the
  ## file.
  ##
  ## `colNames` can be used to overwrite (or supply if none in file!) names of the
  ## columns in the header. This is also useful if the header is not conforming
  ## to the separator of the file. Note: if you `do` supply custom column names,
  ## but there `is` a header in the file, make sure to use `skipLines` to skip
  ## that header, as we will not try to parse any header information if `colNames`
  ## is supplied.
  ##
  ## `maxGuesses` is the maximum number of rows to look at before we give up
  ## trying to determine the datatype of the column and set it to 'object'.
  ##
  ## `lineBreak` is the character used to detect if a new line starts. `eat`
  ## on the other hand is simply ignore. For unix style line endings the defaults
  ## are fine. In principle for windows style endings `\r\n` the defaults *should*
  ## work as well, but in rare cases the default causes issues with mismatched
  ## line counts. In those cases try to switch `lineBreaks` and `eat` around.
  if fname.startsWith("http://") or fname.startsWith("https://"):
    return readCsvFromUrl(fname, sep=sep, header=header, skipLines=skipLines,
                          toSkip=toSkip, colNames=colNames)

  result = newDataFrame()
  var ff = memfiles.open(fname)
  var lineCnt = 0
  for slice in memSlices(ff, delim = lineBreak, eat = eat):
    if slice.size > 0:
      inc lineCnt

  ## we're dealing with ASCII files, thus each byte can be interpreted as a char
  var data = cast[ptr UncheckedArray[char]](ff.mem)
  result = readCsvTypedImpl(data, ff.size, lineCnt, sep, header, skipLines, toSkip, colNames,
                            skipInitialSpace, quote, maxGuesses, lineBreak, eat)
  ff.close()

proc readCsvAlt*(fname: string,
                 sep = ',',
                 header = "",
                 skipLines = 0,
                 colNames: seq[string] = @[]): OrderedTable[string, seq[string]] =
  ## returns a CSV file as a table of `header` keys vs. `seq[string]`
  ## values, where idx 0 corresponds to the first data value
  ## The `header` field can be used to designate the symbol used to
  ## differentiate the `header`. By default `#`.
  ## `colNames` can be used to provide custom names for the columns.
  ## If any are given and a header is present with a character indiciating
  ## the header, it is automatically skipped. ``However``, if custom names are
  ## desired and there is a real header without any starting symbol (i.e.
  ## `header.len == 0`), please use `skipLines = N` to skip it manually!
  var s = newFileStream(fname, fmRead)
  if s == nil:
    raise newException(IOError, "Input file " & $fname & " does not exist! " &
     "`readCsv` failed.")
  result = s.readCsv(sep, header, skipLines, colNames, fname = fname)
  s.close()

proc writeCsv*[C: ColumnLike](df: DataTable[C], filename: string, sep = ',', header = "",
               precision = 4) =
  ## writes a DataFrame to a "CSV" (separator can be changed) file.
  ## `sep` is the actual separator to be used. `header` indicates a potential
  ## symbol marking the header line, e.g. `#`
  var data = newStringOfCap(df.len * 8) # for some reserved space
  # add header symbol to first line
  data.add header
  let keys = getKeys(df)
  data.add join(keys, $sep) & "\n"
  var idx = 0
  for row in df:
    idx = 0
    for x in row:
      if idx > 0:
        data.add $sep
      data.add pretty(x, precision = precision)
      inc idx
    data.add "\n"
  writeFile(filename, data)

proc showBrowser*[C: ColumnLike](df: DataTable[C], fname = "df.html", path = getTempDir(), toRemove = false) =
  ## Displays the given DataFrame as a table in the default browser.
  ##
  ## Note: the HTML generation is not written for speed at this time. For very large
  ## dataframes expect bad performance.
  const tmpl = """
<!DOCTYPE html>
<html>
<head>
<style>
table {
  font-family: arial, sans-serif;
  border-collapse: collapse;
  width: 100%;
}

td, th {
  border: 1px solid #dddddd;
  text-align: left;
  padding: 8px;
}

tr:nth-child(even) {
  background-color: #dddddd;
}
</style>
</head>
<body>

<h2> $# </h2>

<table>
  $#
</table>

</body>
</html>
"""
  var
    header: string
    body: string
  header = "<thead>\n<tr>"
  header.add &"<th> Index </th>"
  for k in df.getKeys:
    header.add &"<th> {k} <br><br> {df[k].toNimType} </th>"
  header.add "</tr>\n</thead>"
  body = "<tbody>"
  var idx = 0
  for row in df:
    body.add "<tr>\n"
    # first add column for index
    body.add &"<td>{idx}</td>"
    for x in row:
      body.add &"<td>{pretty(x)}</td>"
    body.add "\n</tr>"
    inc idx
  body.add "</tbody>"
  let fname = path / fname
  writeFile(fname, tmpl % [fname, header & body])
  openDefaultBrowser(fname)
  if toRemove:
    # opening browsers may be slow, so wait a long time before we delete (file still needs to
    # be there when the browser is finally open. Thus default is to keep the file
    sleep(1000)
    removeFile(fname)
