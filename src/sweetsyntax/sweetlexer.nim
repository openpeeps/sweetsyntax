# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[strutils, memfiles, tables, algorithm, options]
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
    line*, col*, pos*: int # meta information for error reporting and token metadata
    current*: char
    usingMemFile: bool
    spec*: SweetSpec
      ## The syntax specification that defines how to tokenize the input, including
      ## the symbols, identifiers, and filters to apply.
    enableFilters: bool
    filtersReady: bool
    filterHits: seq[FilterHit]
    filterScanIdx: int

  Token* = ref object
    ## Represents a token with its kind, position, and
    ## optional attributes
    kind*: SweetTokenKind
    line*, col*, pos*: int
    start*, stop*: int
    attr*: seq[string]
      # Optional, user-defined attributes for this token, e.g. keyword type or operator name

  SweetLexerError* = object of CatchableError

proc charAt(l: SweetLexer, idx: int): char {.inline.} =
  # Returns the character at the given index, or '\0' if out of bounds
  if idx < 0 or idx >= l.len: return '\0'
  if l.data != nil: l.data[idx] else: l.input[idx]

proc getContext*(l: SweetLexer, posOverride: int = -1): string =
  # Show the full current line and place caret at exact token position.
  let rawPos = if posOverride >= 0: posOverride else: l.pos
  let atPos = max(0, min(rawPos, l.len))

  var lineStart = atPos
  while lineStart > 0 and l.charAt(lineStart - 1) != '\n':
    dec lineStart

  var lineEnd = atPos
  while lineEnd < l.len and l.charAt(lineEnd) notin {'\n', '\r'}:
    inc lineEnd

  var snippet: string
  if l.input.len > 0:
    snippet = l.input[lineStart ..< lineEnd]
  else:
    snippet = newStringOfCap(max(0, lineEnd - lineStart))
    for i in lineStart ..< lineEnd:
      snippet.add(l.charAt(i))

  let markerPos = max(0, min(snippet.len, atPos - lineStart))
  result = snippet & "\n" & " ".repeat(markerPos) & "^"


proc isDelimiterPunct(c: char): bool {.inline.} =
  # Common delimiter punctuation characters, this can be customized per language if needed
  c in {'{','}','(',')','[',']',',',';'}

proc isOperatorPunct(c: char): bool {.inline.} =
  # Common operator characters, this can be customized per language if needed
  c in {':','.','?','~','+','-','*','/','%','<','>','=','!','&','|','^','#'}

proc isAnyPunct(c: char): bool {.inline.} =
  # Delimiter and operator punctuation are often treated differently in languages
  isDelimiterPunct(c) or isOperatorPunct(c)

proc peek(l: SweetLexer, offset: int = 1): char {.inline.} =
  # Lookahead character at current position + offset, returns '\0' if out of bounds
  l.charAt(l.pos + offset)

proc advance(l: var SweetLexer): char {.inline.} =
  # Move to the next character, updating line and column info,
  # returns the current char before advancing or '\0' if at end of input
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
  # Checks if the character is a UTF-8 continuation byte (10xxxxxx)
  let b = uint8(ord(c))
  (b and 0b1100_0000'u8) == 0b1000_0000'u8

proc utf8SeqLen(c: char): int {.inline.} =
  # Determines the length of a UTF-8 sequence based on the lead byte
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
  # Skips over whitespace characters and line continuations, updating position accordingly
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
  # Extracts the substring from startPos to stopPos (exclusive) as the lexeme for the current token.
  if l.data != nil:
    let n = stopPos - startPos
    result = newString(n)
    copyMem(addr result[0], addr l.data[startPos], n)
  else:
    result = l.input[startPos..<stopPos]

proc getTokenValue*(l: SweetLexer, tok: Token): string {.inline.} =
  ## Returns the source text for the given token.
  l.getLexeme(tok.start, tok.stop)

proc getFullInput(l: SweetLexer): string =
  ## Returns full source text as string (needed for regex filters).
  if l.data != nil:
    if l.len <= 0: return ""
    result = newString(l.len)
    copyMem(addr result[0], addr l.data[0], l.len)
  else:
    result = l.input

proc addAttrOnce(attrs: var seq[string], a: string) {.inline.} =
  # Adds an attribute to the list if it's not already present, ensuring no duplicates.
  if a.len > 0 and a notin attrs:
    attrs.add(a)

proc overlap(aStart, aStop, bStart, bStop: int): bool {.inline.} =
  # Checks if the ranges [aStart, aStop) and [bStart, bStop) overlap
  aStart < bStop and bStart < aStop

proc lookupAttrByLexeme(tbl: Table[string, string], lexeme: string): string =
  # Supports both YAML styles:
  # - lexeme -> attr
  # - attr   -> lexeme
  if tbl.hasKey(lexeme):
    return tbl[lexeme]
  for k, v in tbl.pairs:
    if v == lexeme:
      return k
  ""

proc resolveGroupRange(m: MatchResult, groupIdx: int): tuple[s, e: int] =
  # Given a regex match result and a group index, returns the start and end positions of that group.
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
  # Prepares the filter hits by running all regex filters against the
  # input and storing their matches
  if l.filtersReady: return

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


proc applyFilterAttrs(l: SweetLexer, tok: var Token) =
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

proc makeRange(l: SweetLexer, k: SweetTokenKind, startPos, startLine, startCol: int): Token {.inline.} =
  result = Token(
    kind: k,
    line: startLine,
    col: startCol,
    pos: startPos,
    start: startPos,
    stop: l.pos
  )

  let stopPos = l.pos
  var lexeme =
    if stopPos <= startPos:
      ""
    else:
      l.getLexeme(startPos, stopPos)
  # For comments, store the comment content without the syntax markers
  if k == tkComment:
    # Strip inline comment syntax (e.g., "//")
    if l.spec.inlineComment.isSome():
      let commentSyntax = l.spec.inlineComment.get()
      if lexeme.startsWith(commentSyntax):
        # Store only the comment text, not the "//"
        result.start = startPos + commentSyntax.len
        # also, ensure the comment line does not start with whitespace
        while result.start < stopPos and l.charAt(result.start) == ' ':
          inc result.start
  elif k == tkDocComment:
    # Strip block comment syntax (e.g., "/**" and "*/")
    let startSyntax = l.spec.blockComment[0]
    let endSyntax = l.spec.blockComment[1]
    if lexeme.startsWith(startSyntax):
      result.start = startPos + startSyntax.len
    if lexeme.endsWith(endSyntax):
      result.stop = result.stop - endSyntax.len
  elif k == tkIdentifier:
    let identAttr = lookupAttrByLexeme(l.spec.identifiers, lexeme)
    if identAttr.len > 0:
      result.attr.addAttrOnce(identAttr)
  elif k == tkPunct:
    let symAttr = lookupAttrByLexeme(l.spec.symbols, lexeme)
    if symAttr.len > 0:
      result.attr.addAttrOnce(symAttr)

  l.applyFilterAttrs(result)

proc getToken*(l: var SweetLexer): Token =
  ## Retrieve the next token from the input stream, advancing the lexer's position
  if l.enableFilters: l.prepareFilters() # Ensure filters are prepared if enabled
  l.skipWhitespace()

  let startPos = l.pos
  let startLine = l.line
  let startCol = l.col

  if l.current == '\0':
    return Token(kind: tkEOF, line: startLine, col: startCol, pos: startPos, start: startPos, stop: startPos)

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

  # Check for block comments FIRST (before inline comments and operators)
  if l.spec.blockComment[0].len > 0 and l.current == l.spec.blockComment[0][0]:
    let commentStart = l.pos
    let startSyntax = l.spec.blockComment[0]
    let endSyntax = l.spec.blockComment[1]
    var matchesStart = true
    for i in 0 ..< startSyntax.len:
      if l.charAt(l.pos + i) != startSyntax[i]:
        matchesStart = false
        break
    if matchesStart:
      # Check if this is a doc comment (/** or /*!)
      let isDocComment = startSyntax == "/*" and (l.peek(2) == '*' or l.peek(2) == '!')
      
      # Consume start syntax
      for i in 0 ..< startSyntax.len:
        discard l.advance()
      
      # Find end syntax
      while l.current != '\0':
        var matchesEnd = false
        if l.current == endSyntax[0]:
          matchesEnd = true
          for j in 0 ..< endSyntax.len:
            if l.charAt(l.pos + j) != endSyntax[j]:
              matchesEnd = false
              break
        
        if matchesEnd:
          # Consume end syntax
          for i in 0 ..< endSyntax.len:
            discard l.advance()
          return l.makeRange(
            if isDocComment: tkDocComment else: tkComment,
            commentStart, startLine, startCol
          )
        discard l.advance()
      
      # Unterminated block comment
      return l.makeRange(
        if isDocComment: tkDocComment else: tkComment,
        commentStart, startLine, startCol
      )

  # Check for inline comments (must come before operator check!)
  if l.spec.inlineComment.isSome():
    let commentSyntax = l.spec.inlineComment.get()
    if commentSyntax.len > 0 and l.current == commentSyntax[0]:
      var matchesSyntax = true
      for i in 0 ..< commentSyntax.len:
        if l.charAt(l.pos + i) != commentSyntax[i]:
          matchesSyntax = false
          break
      
      if matchesSyntax:
        let commentStart = l.pos
        # Consume the comment syntax
        for i in 0 ..< commentSyntax.len:
          discard l.advance()
        
        # Consume rest of line
        while l.current != '\0' and l.current != '\n':
          discard l.advance()
        
        return l.makeRange(tkComment, commentStart, startLine, startCol)

  # Check for punctuation
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

proc initLexerFromFile*(spec: SweetSpec, path: string, enableFilters: bool = false): SweetLexer =
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
    enableFilters: enableFilters,
    usingMemFile: true,
    filtersReady: false,
    filterHits: @[],
    filterScanIdx: 0
  )
  result.data = cast[ptr UncheckedArray[char]](result.mf.mem)
  result.len = result.mf.size
  result.current = result.charAt(0)

proc initLexer*(spec: SweetSpec, input: sink string, enableFilters: bool = false): SweetLexer =
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
    enableFilters: enableFilters,
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
