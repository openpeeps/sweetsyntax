# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[strutils, memfiles, tables, algorithm]
import pkg/openparser/regex

import ./config

type
  SweetTokenKind* = enum
    ## Basic token kinds
    tkEOF
    tkIdentifier = "ident"
    tkInt = "int"
    tkFloat = "float"
    tkChar = "char"
    tkString = "string"
    tkPunct = "punct"
    tkComment = "comment"
    tkDocComment = "doc_comment"

  FilterHit = object
    start, stop: int  # stop is exclusive
    attr: string

  SweetLexer* = ref object
    ## Represents the state of the lexer
    input: string
    mf: MemFile
    data: ptr UncheckedArray[char]
    len: int
    line, col, pos: int
    current: char
    usingMemFile: bool
    spec: SweetSpec
    filtersReady: bool
    filterHits: seq[FilterHit]
    filterScanIdx: int

  SweetTokenRange* = ref object
    ## Represents a token with its kind, position, and
    ## optional attributes
    kind*: SweetTokenKind
    line*, col*, pos*: int
    start*, stop*: int
    attr*: seq[string]
      # Optional, user-defined attributes for this token, e.g. keyword type or operator name

  SweetLexerError* = object of CatchableError

proc isDelimiterPunct(c: char): bool {.inline.} =
  c in {'{','}','(',')','[',']',',',';'}

proc isOperatorPunct(c: char): bool {.inline.} =
  c in {':','.','?','~','+','-','*','/','%','<','>','=','!','&','|','^','#'}

proc isAnyPunct(c: char): bool {.inline.} =
  isDelimiterPunct(c) or isOperatorPunct(c)

proc charAt(l: SweetLexer, idx: int): char {.inline.} =
  if idx < 0 or idx >= l.len: return '\0'
  if l.data != nil: l.data[idx] else: l.input[idx]

proc peek(l: SweetLexer, offset: int = 1): char {.inline.} =
  l.charAt(l.pos + offset)

proc advance(l: var SweetLexer): char {.inline.} =
  result = l.current
  if l.current == '\0':
    return
  inc l.pos
  if result == '\n':
    inc l.line
    l.col = 1
  else:
    inc l.col
  l.current = l.charAt(l.pos)

proc isUtf8Cont(c: char): bool {.inline.} =
  let b = uint8(ord(c))
  (b and 0b1100_0000'u8) == 0b1000_0000'u8

proc utf8SeqLen(c: char): int {.inline.} =
  let b = uint8(ord(c))
  if b < 0b1000_0000'u8: 1
  elif (b and 0b1110_0000'u8) == 0b1100_0000'u8: 2
  elif (b and 0b1111_0000'u8) == 0b1110_0000'u8: 3
  elif (b and 0b1111_1000'u8) == 0b1111_0000'u8: 4
  else: 1

proc advanceUtf8Char(l: var SweetLexer): int =
  ## Consume one UTF-8 scalar worth of bytes (best effort).
  if l.current == '\0': return 0
  let n = utf8SeqLen(l.current)
  discard l.advance() # lead byte (or ASCII)
  result = 1
  var i = 1
  while i < n and isUtf8Cont(l.current):
    discard l.advance()
    inc i
    inc result

proc isIdentStart(c: char): bool {.inline.} =
  c.isAlphaAscii or c == '_' or c == '$'

proc isIdentPart(c: char): bool {.inline.} =
  c.isAlphaNumeric or c == '_' or c == '$'

proc skipLineContinuation(l: var SweetLexer) =
  # Handles backslash-newline and backslash-CRLF as one logical line splice
  while l.current == '\\' and (
    l.peek() == '\n' or (l.peek() == '\r' and l.peek(2) == '\n')
  ):
    discard l.advance() # '\'
    if l.current == '\r':
      discard l.advance() # '\r'
    if l.current == '\n':
      discard l.advance() # '\n'

proc skipWhitespace(l: var SweetLexer) =
  while true:
    if l.current in {' ', '\t', '\r'}:
      discard l.advance()
    elif l.current == '\\' and l.peek() == '\n':
      l.skipLineContinuation()
    elif l.current == '\n':
      discard l.advance()
    else:
      break

proc getLexeme*(l: SweetLexer, startPos, stopPos: int): string =
  if l.data != nil:
    let n = stopPos - startPos
    result = newString(n)
    copyMem(addr result[0], addr l.data[startPos], n)
  else:
    result = l.input[startPos..<stopPos]


proc getFullInput(l: SweetLexer): string =
  ## Returns full source text as string (needed for regex filters).
  if l.data != nil:
    if l.len <= 0: return ""
    result = newString(l.len)
    copyMem(addr result[0], addr l.data[0], l.len)
  else:
    result = l.input

proc addAttrOnce(attrs: var seq[string], a: string) {.inline.} =
  if a.len > 0 and a notin attrs:
    attrs.add(a)

proc overlap(aStart, aStop, bStart, bStop: int): bool {.inline.} =
  aStart < bStop and bStart < aStop

proc lookupAttrByLexeme(tbl: Table[string, string], lexeme: string): string =
  ## Supports both YAML styles:
  ## - lexeme -> attr
  ## - attr   -> lexeme
  if tbl.hasKey(lexeme):
    return tbl[lexeme]
  for k, v in tbl.pairs:
    if v == lexeme:
      return k
  ""

proc resolveGroupRange(m: MatchResult, groupIdx: int): tuple[s, e: int] =
  if groupIdx <= 0:
    return (m.start, m.stop)

  if groupIdx > m.groupCount():
    return (m.start, m.stop)

  let g = m.group(groupIdx)
  if not g.matched:
    return (m.start, m.stop)

  (g.start, g.stop)

proc cmpFilterHit(a, b: FilterHit): int =
  ## Sort by start, then stop (both ascending)
  result = cmp(a.start, b.start)
  if result == 0:
    result = cmp(a.stop, b.stop)


proc prepareFilters(l: SweetLexer) =
  if l.filtersReady:
    return

  l.filtersReady = true
  l.filterHits.setLen(0)
  l.filterScanIdx = 0

  when compiles(l.spec.filters):
    if l.spec.filters.len == 0:
      return
  else:
    return

  let src = l.getFullInput()
  if src.len == 0:
    return

  for f in l.spec.filters:
    if f.attr.len == 0:
      continue

    var prog: Program
    try:
      prog = compile(f.pattern)
    except:
      continue

    var vm = initRegexVM(prog)
    let groupIdx = f.group
    let matches = vm.findAll(src)

    for m in matches:
      let r = resolveGroupRange(m, groupIdx)
      if r.e > r.s:
        l.filterHits.add(FilterHit(start: r.s, stop: r.e, attr: f.attr))

  if l.filterHits.len > 1:
    l.filterHits.sort(cmpFilterHit)


proc applyFilterAttrs(l: SweetLexer, tok: var SweetTokenRange) =
  if l.filterHits.len == 0:
    return

  while l.filterScanIdx < l.filterHits.len and l.filterHits[l.filterScanIdx].stop <= tok.start:
    inc l.filterScanIdx

  var i = l.filterScanIdx
  while i < l.filterHits.len and l.filterHits[i].start < tok.stop:
    let h = l.filterHits[i]
    if overlap(tok.start, tok.stop, h.start, h.stop):
      tok.attr.addAttrOnce(h.attr)
    inc i

proc makeRange(l: SweetLexer, k: SweetTokenKind, startPos, startLine, startCol: int): SweetTokenRange {.inline.} =
  result = SweetTokenRange(
    kind: k,
    line: startLine,
    col: startCol,
    pos: startPos,
    start: startPos,
    stop: l.pos
  )

  let lexeme =
    block:
      let stopPos = l.pos
      if stopPos <= startPos:
        ""
      else:
        l.getLexeme(startPos, stopPos)

  if k == tkIdentifier:
    let identAttr = lookupAttrByLexeme(l.spec.identifiers, lexeme)
    if identAttr.len > 0:
      result.attr.addAttrOnce(identAttr)
  elif k == tkPunct:
    let symAttr = lookupAttrByLexeme(l.spec.symbols, lexeme)
    if symAttr.len > 0:
      result.attr.addAttrOnce(symAttr)

  l.applyFilterAttrs(result)

proc getToken*(l: var SweetLexer): SweetTokenRange =
  ## Retrieve the next token from the input stream, advancing the lexer's position
  l.prepareFilters()
  l.skipWhitespace()

  let startPos = l.pos
  let startLine = l.line
  let startCol = l.col

  if l.current == '\0':
    return SweetTokenRange(kind: tkEOF, line: startLine, col: startCol, pos: startPos, start: startPos, stop: startPos)


  if isIdentStart(l.current) or ord(l.current) >= 0x80:
    if ord(l.current) >= 0x80:
      discard l.advanceUtf8Char()
    else:
      discard l.advance()
    while true:
      if isIdentPart(l.current):
        discard l.advance()
      elif ord(l.current) >= 0x80:
        discard l.advanceUtf8Char()
      else:
        break
    return l.makeRange(tkIdentifier, startPos, startLine, startCol)

  if l.current.isDigit:
    var isFloat = false
    while l.current.isDigit: discard l.advance()
    if l.current == '.' and l.peek().isDigit:
      isFloat = true
      discard l.advance()
      while l.current.isDigit: discard l.advance()
    if l.current in {'e', 'E'}:
      let p = l.peek()
      let p2 = l.peek(2)
      if p.isDigit or ((p == '+' or p == '-') and p2.isDigit):
        isFloat = true
        discard l.advance()
        if l.current == '+' or l.current == '-': discard l.advance()
        while l.current.isDigit: discard l.advance()
    return l.makeRange(if isFloat: tkFloat else: tkInt, startPos, startLine, startCol)

  if l.current == '"' or l.current == '\'':
    let quote = l.current
    discard l.advance()
    var escaped = false
    while l.current != '\0':
      if escaped:
        escaped = false
        discard l.advance()
        continue
      if l.current == '\\':
        escaped = true
        discard l.advance()
        continue
      if l.current == quote:
        discard l.advance()
        return l.makeRange(tkString, startPos, startLine, startCol)
      discard l.advance()
    return l.makeRange(tkString, startPos, startLine, startCol) # unterminated, but safe

  if isDelimiterPunct(l.current):
    discard l.advance()
    return l.makeRange(tkPunct, startPos, startLine, startCol)

  if isOperatorPunct(l.current):
    while isOperatorPunct(l.current):
      discard l.advance()
    return l.makeRange(tkPunct, startPos, startLine, startCol)

  # Fallback: consume one UTF-8 char so lexer never stalls or returns nil
  discard l.advanceUtf8Char()
  return l.makeRange(tkPunct, startPos, startLine, startCol)

proc initLexerFromFile*(spec: SweetSpec, path: string): SweetLexer =
  ## Initialize lexer from a file using memfiles for efficient access.
  result = SweetLexer(
    input: path,
    mf: memfiles.open(path, fmRead),
    data: nil,
    len: 0,
    line: 1,
    col: 1,
    pos: 0,
    spec: spec,
    usingMemFile: true,
    filtersReady: false,
    filterHits: @[],
    filterScanIdx: 0
  )
  result.data = cast[ptr UncheckedArray[char]](result.mf.mem)
  result.len = result.mf.size
  result.current = result.charAt(0)

proc initLexer*(spec: SweetSpec, input: sink string): SweetLexer =
  ## Initialize lexer from raw source text, this is efficient for small inputs
  result = SweetLexer(
    input: input,
    data: nil,
    len: input.len,
    line: 1,
    col: 1,
    pos: 0,
    current: '\0',
    spec: spec,
    filtersReady: false,
    filterHits: @[],
    filterScanIdx: 0
  )
  if result.len > 0:
    result.current = result.charAt(0)

proc closeLexer*(l: var SweetLexer) =
  if l != nil and l.usingMemFile:
    l.mf.close()
  reset(l)
