# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module implements a generic lexer for tokenizing source code based on a syntax specification.
## The lexer supports various token kinds, including identifiers, literals, punctuation, comments, and regexes.
## It also allows for user-defined attributes and filters to enhance token classification.

import std/[strutils, memfiles, tables, algorithm, options, sets]
import pkg/openparser/regex

import ./config

type
  SweetTokenKind* = enum
    ## Basic token kinds
    tkEOF
    tkIdentifier = "ident"
    tkInt = "int"
    tkFloat = "float"
    tkHex         ## hex literal: 0xFF
    tkOctal       ## octal literal: 0o777
    tkBinary      ## binary literal: 0b1010
    tkBigInt      ## bigint literal: 42n, 0xFFn
    tkImag        ## imaginary literal: 1i, 1.5i, 0x1p-2i
                  ## (only with `extended_numbers`, e.g. Go)
    tkChar = "char"
    tkString = "string"
    tkPunct = "punct"
    tkComment = "comment"
    tkDocComment = "doc_comment"
    tkRegex = "regex"

  FilterHit = object
    start, stop: int  # stop is exclusive
    attr: string

  SweetLexer* = ref object
    ## Represents the state of the lexer
    input: string
    mf: MemFile
    data: ptr UncheckedArray[char]
    len*: int
    line*, col*, pos*: int # meta information for error reporting and token metadata
    current*: char
    usingMemFile: bool
    symbols*: Table[string, string]
    identifiers*: Table[string, string]
    keywordScopes*: Table[string, string]
      # lexeme -> TextMate scope, inverted from the spec's `keyword_scopes`.
      # Lets the renderers classify a keyword without carrying any vocabulary
      # of their own. Empty when the spec declares no scopes.
    inlineComment*: Option[string]
    blockComment*: array[2, string]
    hashComments*: bool
      # whether '#' starts an inline comment (e.g. PHP), unless followed by '['
      # (PHP 8 attributes)
    trailingBangQuestion*: bool
      # whether identifiers may end with '?' or '!' (e.g. Ruby method names)
    rawStrings*: bool
      # whether backquotes delimit raw string literals that may span lines
      # with no escapes or interpolation (e.g. Go). Without this, backquotes
      # lex as Nim quoted identifiers or JS template literals.
    extendedNumbers*: bool
      # Go-style number literals: imaginary suffix (`1i`, `0x1p-2i`),
      # hex floats (`0x1p-2`), trailing-dot floats (`1.`)
    intSuffixes*: bool
      # C-style integer/float suffixes folded into number tokens
      # (`1U`, `100ULL`, `0xFFL`, `1.5f`)
    heredocs*: bool
      # whether `<<NAME` opens a here-document (Ruby, PHP, shell). Off for
      # languages where `<<` is only a shift operator.
    stringPrefixes*: seq[string]
      # identifier prefixes glued to a quote to form one string token
      # (C++ `u8"x"`, `L'c'`, `R"tag(...)tag"`; Rust `b"x"`)
    rawStringDelims*: bool
      # whether an `R`-style prefix introduces a delimited raw string
      # (`R"tag(...)tag"`, C++17)
    percentLiterals*: bool
      # whether `%w[..]`, `%i(..)`, `%q{..}` and friends are percent string
      # literals (Ruby) rather than the `%` operator
    filtersSkipLiterals*: bool
      # when true, filter attrs are not applied to string, char, regex,
      # comment or doc-comment tokens, so a filter describing code structure
      # cannot restyle a literal that merely looks like code. Off by default:
      # Markdown filters deliberately reach inside code spans.
    longBrackets*: bool
      # whether `[[ ... ]]`, `[=[ ... ]=]` open a string literal (Lua) rather
      # than two `[` delimiters
    heredocOpenerPunctuation*: bool
      # whether `;`/`,` may follow a heredoc opener before the newline
      # (Perl's `print <<"EOF";`). Off by default: the opener must end the
      # line, which is what keeps `arr << 5` from opening a heredoc named `5`.
    inferRegex*: bool
      # when true, decide `/regex/` vs division from the previous significant
      # token and the spec's `expect_regex_after` lists. Only for consumers
      # with no parser to supply the hint (e.g. `highlight`); the parser sets
      # `expectRegex` itself and must not enable this.
    expectRegexTokens*: HashSet[string]
      # `expect_regex_after` tokens after which a `/` may start a regex
    expectRegexKeywords*: HashSet[string]
      # `expect_regex_after` keywords after which a `/` may start a regex
    lastTokKind*: SweetTokenKind
      # kind of the last significant token returned by `getToken`
    lastTokValue*: string
      # lexeme of the last significant token returned by `getToken`
    openTag*: Option[string]
    closeTag*: Option[string]
    features*: set[LanguageFeature]
    allOps*: seq[string]
    filters*: seq[SweetFilter]
    enableFilters: bool
    filtersReady: bool
    filterHits: seq[FilterHit]
    filterScanIdx: int
    expectRegex*: bool
    tagTerminated*: bool
      # set to true when the last fetched token was preceded by a close tag
      # (e.g. PHP's `?>`), which terminates the current statement
    symbolsRev*, identifiersRev*: Table[string, string]
      ## lazily-built reverse tables (attr -> lexeme) for reversed YAML styles
    reverseAttrLookup*: bool
      ## when true, attr lookup also probes a reverse (attr -> lexeme) table.
      ## Off by default: no bundled language spec uses reversed-style mappings.

  Token* = ref object
    ## Represents a token with its kind, position, and
    ## optional attributes
    kind*: SweetTokenKind
    line*, col*, pos*: int
    start*, stop*: int
    attr*: seq[string]
      # Optional, user-defined attributes for this token, e.g. keyword type or operator name

  SweetLexerError* = object of CatchableError
    ## Represents an error that can occur during lexing,
    ## such as invalid UTF-8 sequences or unterminated strings

proc charAt*(l: SweetLexer, idx: int): char {.inline.} =
  # Returns the character at the given index, or '\0' if out of bounds
  if idx < 0 or idx >= l.len: return '\0'
  if l.data != nil: l.data[idx] else: l.input[idx]

proc getContext*(l: SweetLexer, posOverride: int = -1, maxContext: int = 80): string =
  ## Show a window around the error position, capped to `maxContext` chars on each side.
  ## Prevents dumping entire minified files on error.
  let rawPos = if posOverride >= 0: posOverride else: l.pos
  let atPos = max(0, min(rawPos, l.len))

  var lineStart = atPos
  while lineStart > 0 and l.charAt(lineStart - 1) != '\n':
    dec lineStart

  var lineEnd = atPos
  while lineEnd < l.len and l.charAt(lineEnd) notin {'\n', '\r'}:
    inc lineEnd

  # Cap the window around the error position
  let windowStart = max(lineStart, atPos - maxContext)
  let windowEnd = min(lineEnd, atPos + maxContext)

  var snippet: string
  if l.data == nil and l.input.len > 0:
    snippet = l.input[windowStart ..< windowEnd]
  else:
    # MemFile-backed (or empty) input: `input` holds a path, not source,
    # so read through charAt which covers both buffers.
    snippet = newStringOfCap(max(0, windowEnd - windowStart))
    for i in windowStart ..< windowEnd:
      snippet.add(l.charAt(i))

  let markerPos = max(0, min(snippet.len, atPos - windowStart))

  # Add ellipsis if we truncated
  var prefix = ""
  var suffix = ""
  if windowStart > lineStart:
    prefix = "... "
  if windowEnd < lineEnd:
    suffix = " ..."

  result = prefix & snippet & suffix & "\n" & " ".repeat(prefix.len + markerPos) & "^"


proc isDelimiterPunct(c: char): bool {.inline.} =
  # Common delimiter punctuation characters, this can be customized per language if needed
  c in {'{','}','(',')','[',']',',',';',':','#'}

proc isOperatorPunct(c: char): bool {.inline.} =
  # Common operator characters, this can be customized per language if needed
  c in {'.','?','~','+','-','*','/','%','<','>','=','!','&','|','^','\\', '@'}

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
  if stopPos <= startPos:
    return ""
  if l.data != nil:
    let n = stopPos - startPos
    result = newString(n)
    copyMem(addr result[0], addr l.data[startPos], n)
  else:
    result = l.input[startPos..<stopPos]

proc getTokenValue*(l: SweetLexer, tok: Token): string {.inline.} =
  ## Returns the source text for the given token.
  l.getLexeme(tok.start, tok.stop)

type
  LexerMark* = object
    ## Opaque snapshot of the lexer's mutable scan state, for read-only
    ## lookahead (e.g. the C cast-vs-group paren scan).
    pos*, line*, col*: int
    current*: char
    expectRegex*, tagTerminated*: bool
    filterScanIdx*, filterHitsLen*: int
    lastTokKind*: SweetTokenKind
    lastTokValue*: string

proc markLexer*(l: SweetLexer): LexerMark {.inline.} =
  ## Snapshot the current scan state. Only valid while no filter
  ## configuration changes (filter hits are append-only during `getToken`).
  LexerMark(pos: l.pos, line: l.line, col: l.col, current: l.current,
    expectRegex: l.expectRegex, tagTerminated: l.tagTerminated,
    filterScanIdx: l.filterScanIdx, filterHitsLen: l.filterHits.len,
    lastTokKind: l.lastTokKind, lastTokValue: l.lastTokValue)

proc restoreLexer*(l: var SweetLexer, m: LexerMark) {.inline.} =
  ## Rewind the lexer to a snapshot from `markLexer`, discarding any
  ## tokens scanned since (parser `prev`/`curr`/`next` must be restored
  ## by the caller as well).
  l.pos = m.pos
  l.line = m.line
  l.col = m.col
  l.current = m.current
  l.expectRegex = m.expectRegex
  l.tagTerminated = m.tagTerminated
  l.filterScanIdx = m.filterScanIdx
  l.filterHits.setLen(m.filterHitsLen)
  l.lastTokKind = m.lastTokKind
  l.lastTokValue = m.lastTokValue

proc getFullInput*(l: SweetLexer): string =
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

proc buildRevTable(tbl: Table[string, string]): Table[string, string] =
  ## Builds the reverse (attr -> lexeme) mapping of `tbl`.
  for k, v in tbl.pairs:
    result[v] = k

proc lookupAttrByLexeme(l: SweetLexer, lexeme: string, isIdentTable: bool): string =
  # Supports both YAML styles:
  # - lexeme -> attr (fast path, forward table)
  # - attr   -> lexeme (only when `reverseAttrLookup` is enabled)
  if isIdentTable:
    if l.identifiers.hasKey(lexeme):
      return l.identifiers[lexeme]
    if l.reverseAttrLookup:
      if l.identifiers.len > 0 and l.identifiersRev.len == 0:
        l.identifiersRev = buildRevTable(l.identifiers)
      result = l.identifiersRev.getOrDefault(lexeme)
  else:
    if l.symbols.hasKey(lexeme):
      return l.symbols[lexeme]
    if l.reverseAttrLookup:
      if l.symbols.len > 0 and l.symbolsRev.len == 0:
        l.symbolsRev = buildRevTable(l.symbols)
      result = l.symbolsRev.getOrDefault(lexeme)

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

  if l.filters.len == 0:
    return

  let src = l.getFullInput()
  if src.len == 0:
    return

  for f in l.filters:
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

  # A filter that describes code structure must not restyle a literal or a
  # comment that merely contains the same text, e.g. a preprocessor filter
  # matching `#if` inside `"#if DEBUG"`. Specs opt in via
  # `filters_skip_literals`; Markdown's code-span filters do not.
  if l.filtersSkipLiterals and tok.kind in
      {tkString, tkChar, tkRegex, tkComment, tkDocComment}:
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
    # Strip block comment markers (e.g., "/*" and "*/")
    if l.blockComment[0].len > 0 and lexeme.startsWith(l.blockComment[0]):
      result.start = startPos + l.blockComment[0].len
      if lexeme.endsWith(l.blockComment[1]):
        result.stop = result.stop - l.blockComment[1].len
    # Strip inline comment syntax (e.g., "//")
    elif l.hashComments and lexeme.startsWith("#"):
      # Strip the '#' and leading whitespace
      result.start = startPos + 1
      while result.start < stopPos and l.charAt(result.start) == ' ':
        inc result.start
    elif l.inlineComment.isSome():
      let commentSyntax = l.inlineComment.get()
      if lexeme.startsWith(commentSyntax):
        # Store only the comment text, not the "//"
        result.start = startPos + commentSyntax.len
        # also, ensure the comment line does not start with whitespace
        while result.start < stopPos and l.charAt(result.start) == ' ':
          inc result.start
    # A comment with no trailing content (e.g. bare "//", "/* */" or "#")
    # must not collapse into a zero-width token. Fall back to the full
    # comment span so it is still recognized as a comment.
    if result.start >= result.stop:
      result.start = startPos
      result.stop = stopPos
  elif k == tkDocComment:
    # Strip block comment syntax (e.g., "/**" and "*/")
    let startSyntax = l.blockComment[0]
    let endSyntax = l.blockComment[1]
    if lexeme.startsWith(startSyntax):
      result.start = startPos + startSyntax.len
      # Also skip the doc marker character (* or !) after /*
      if l.charAt(result.start) in {'*', '!'}:
        inc result.start
    if lexeme.endsWith(endSyntax):
      result.stop = result.stop - endSyntax.len
    # Empty doc comment (e.g. "/**/") must not collapse into a negative or
    # zero-width span.
    if result.start >= result.stop:
      result.start = startPos
      result.stop = stopPos
  elif k == tkIdentifier:
    let identAttr = lookupAttrByLexeme(l, lexeme, true)
    if identAttr.len > 0:
      result.attr.addAttrOnce(identAttr)
  elif k == tkPunct:
    let symAttr = lookupAttrByLexeme(l, lexeme, false)
    if symAttr.len > 0:
      result.attr.addAttrOnce(symAttr)
  # elif k == tkRegex:
    # echo "Matched regex: '", lexeme, "' at line ", startLine, " col ", startCol

  l.applyFilterAttrs(result)

proc isHeredocIdentChar(c: char): bool {.inline.} =
  c.isAlphaAscii or c == '_' or c.isDigit()

proc scanHeredoc(l: var SweetLexer, startPos, startLine, startCol: int): Token =
  ## Try to lex a Ruby (`<<EOS`, `<<-EOS`, `<<~EOS`, `<<"EOS"`, `<<'EOS'`,
  ## "<<`EOS`") or PHP (`<<<EOT`, `<<<'EOT'`, `<<<"EOT"`) heredoc starting
  ## at `l.pos`. Returns nil when the text is not a heredoc (e.g. the `<<`
  ## shift operator or `<<=`), so the caller falls back to normal operator
  ## scanning. Lookahead is pure (via charAt) until a terminator line is
  ## confirmed; the lexer only advances on success, which also keeps
  ## shift expressions like `a<<b` safe (no lone `b` line means no match).
  ## The opener must end the line (a trailing `#` comment is allowed);
  ## inline uses such as `foo(<<A, x)` stay on the operator path.
  ## The token is a `tkString` spanning opener..terminator with a
  ## `heredoc` attr, so parsers and renderers work unchanged.
  ## Only reached when the spec sets `heredocs: true` (Ruby, PHP, shell), so
  ## languages that merely shift with `<<` cannot trigger a bogus heredoc.
  # Caller guarantees current == '<' and peek == '<'.
  if l.charAt(l.pos + 2) == '=':
    return nil # `<<=` assignment, not a heredoc
  var i = l.pos + 2
  var allowIndent = false
  var isPhp = false
  if l.charAt(i) == '<':
    # PHP style: `<<<EOT`, `<<<'EOT'`, `<<<"EOT"`
    isPhp = true
    allowIndent = true
    i += 1
  elif l.charAt(i) == '-' or l.charAt(i) == '~':
    # Ruby style: `-` (indented terminator) or `~` (squiggly) marker
    allowIndent = true
    i += 1
  var quote = '\0'
  if l.charAt(i) in {'"', '\'', '`'}:
    # Backtick form is Ruby-only (`<<`EOS``); reject it for `<<<`.
    if isPhp and l.charAt(i) == '`':
      return nil
    quote = l.charAt(i)
    i += 1
  let nameStart = i
  while isHeredocIdentChar(l.charAt(i)):
    i += 1
  if i == nameStart:
    return nil # `<< ` shift, `<<1`, `<<(` etc.
  var terminator = newStringOfCap(i - nameStart)
  for k in nameStart ..< i:
    terminator.add(l.charAt(k))
  if quote != '\0':
    if l.charAt(i) != quote:
      return nil
    i += 1
  var j = i
  while l.charAt(j) == ' ' or l.charAt(j) == '\t':
    j += 1
  if l.charAt(j) == '#':
    while l.charAt(j) != '\0' and l.charAt(j) != '\n':
      j += 1
  # Perl terminates a heredoc opener with `;` or `,` on the same line. Only
  # specs that opt in accept that, so Ruby/PHP keep the strict end-of-line rule
  # that stops `arr << 5` from opening a heredoc.
  if l.heredocOpenerPunctuation:
    while l.charAt(j) in {' ', '\t', ';', ','}:
      j += 1
  if l.charAt(j) == '\r' and l.charAt(j + 1) == '\n':
    j += 2
  elif l.charAt(j) == '\n':
    j += 1
  else:
    return nil # trailing code after the opener: not a v1 heredoc
  # Search for the terminator line.
  var lineStart = j
  var termStop = -1
  while lineStart < l.len:
    var lineEnd = lineStart
    while lineEnd < l.len and l.charAt(lineEnd) != '\n':
      lineEnd += 1
    var contentEnd = lineEnd
    if contentEnd > lineStart and l.charAt(contentEnd - 1) == '\r':
      contentEnd -= 1
    var s = lineStart
    if allowIndent:
      while s < contentEnd and (l.charAt(s) == ' ' or l.charAt(s) == '\t'):
        s += 1
    var ok = (contentEnd - s) >= terminator.len
    if ok:
      for k in 0 ..< terminator.len:
        if l.charAt(s + k) != terminator[k]:
          ok = false
          break
    if ok:
      var rest = s + terminator.len
      if isPhp and l.charAt(rest) == ';':
        rest += 1
      while rest < contentEnd and (l.charAt(rest) == ' ' or l.charAt(rest) == '\t'):
        rest += 1
      if rest == contentEnd:
        if isPhp:
          # Leave a trailing `;` to the statement parser: the token
          # stops right after the terminator identifier.
          termStop = s + terminator.len
        else:
          termStop = if lineEnd < l.len: lineEnd + 1 else: lineEnd
        break
    lineStart = lineEnd + 1
  if termStop < 0:
    return nil # unterminated: leave `<<` to the operator scanner
  while l.pos < termStop:
    discard l.advance()
  result = l.makeRange(tkString, startPos, startLine, startCol)
  result.attr.addAttrOnce("heredoc")

proc scanIntSuffixLen(l: SweetLexer): int =
  ## Length of a C integer suffix at the current position, or 0.
  ## Valid shapes (case-insensitive): `u`, `l`, `ul`, `lu`, `ll`,
  ## `ull`, `llu` — and the suffix must not run into more identifier
  ## characters (`1Length` stays `1` + `Length`, an error downstream
  ## just like a real C frontend). Peek-only; advances nothing.
  var uCount = 0
  var lCount = 0
  while true:
    case l.charAt(l.pos + result)
    of 'u', 'U':
      if uCount > 0: break
      inc uCount
    of 'l', 'L':
      if lCount >= 2: break
      inc lCount
    else: break
    inc result
  if result == 0: return 0
  if l.charAt(l.pos + result).isIdentPart(): return 0

proc consumeIntSuffix(l: var SweetLexer) {.inline.} =
  ## Fold a C integer suffix into the current number token, if the
  ## `int_suffixes` spec flag is on. No-op for other languages.
  if l.intSuffixes:
    for i in 0 ..< l.scanIntSuffixLen():
      discard l.advance()

proc consumeFloatSuffix(l: var SweetLexer) {.inline.} =
  ## Fold a C float suffix (`f`/`F`, plus `l`/`L` long double via the
  ## integer-suffix scan) into the current number token. No-op unless
  ## the `int_suffixes` spec flag is on.
  if l.intSuffixes:
    if l.current in {'f', 'F'} and not l.peek().isIdentPart():
      discard l.advance()
    else:
      l.consumeIntSuffix()

proc scanQuotedString(l: var SweetLexer, startPos, startLine, startCol: int): Token =
  ## Scan a `"` or `'` delimited string literal. Assumes the opening quote is
  ## current. `startPos` may point before the quote so that a literal prefix
  ## (C++ `u8"x"`) is folded into the returned token span.
  let quote = l.current
  discard l.advance()
  # Check for triple-quoted string """"""
  var isTriple = false
  if quote == '"' and l.current == '"' and l.peek() == '"':
    isTriple = true
    discard l.advance() # consume second "
    discard l.advance() # consume third "
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
    if isTriple:
      if l.current == '"' and l.peek() == '"' and l.charAt(l.pos + 2) == '"':
        discard l.advance() # consume first "
        discard l.advance() # consume second "
        discard l.advance() # consume third "
        return l.makeRange(tkString, startPos, startLine, startCol)
    elif l.current == quote:
      discard l.advance()
      return l.makeRange(tkString, startPos, startLine, startCol)
    discard l.advance()
  return l.makeRange(tkString, startPos, startLine, startCol) # unterminated, but safe

proc matchesAt(l: SweetLexer, at: int, s: string): bool {.inline.} =
  ## True when `s` occurs at byte offset `at`. Peek-only; advances nothing.
  if s.len == 0: return true
  for i in 0 ..< s.len:
    if l.charAt(at + i) != s[i]: return false
  true

proc scanDelimitedRawString(l: var SweetLexer, startPos, startLine, startCol, prefixLen: int): Token =
  ## Scan a C++17 delimited raw string body: `R"tag( ... )tag"`. The prefix
  ## (`R`, `u8R`, `LR`, ...) is already consumed and `l.current` is the
  ## opening `"`; this proc consumes that quote, the optional `tag`
  ## delimiter and the `(`. The body then runs to `)tag"`, so quotes and
  ## backslashes inside are literal.
  discard l.advance() # opening '"'
  var delim = ""
  while l.current != '\0' and l.current notin {'(', ')', '"', '\n', '\r'} and
      delim.len < 16:
    delim.add(l.current)
    discard l.advance()
  if l.current != '(':
    # Not a well-formed raw string; fall back to an ordinary quoted scan so
    # the text still highlights as a string. Rewind onto the opening quote.
    l.pos = startPos + prefixLen
    l.current = l.charAt(l.pos)
    return l.scanQuotedString(startPos, startLine, startCol)
  discard l.advance() # consume '('
  while l.current != '\0':
    if l.current == ')' and
        l.matchesAt(l.pos + 1, delim) and l.charAt(l.pos + 1 + delim.len) == '"':
      for _ in 0 ..< delim.len + 2:
        discard l.advance() # consume `)tag"`
      return l.makeRange(tkString, startPos, startLine, startCol)
    discard l.advance()
  return l.makeRange(tkString, startPos, startLine, startCol) # unterminated

proc scanStringPrefix(l: var SweetLexer, startPos, startLine, startCol: int): Token =
  ## Try to lex a string literal carrying an identifier prefix, e.g. C++
  ## `u8"x"`, `L'c'`, `R"tag(...)tag"` or Rust `b"x"`. Returns nil when the
  ## input does not start with one of the spec's `string_prefixes` followed
  ## immediately by a quote, so the caller falls back to a plain identifier.
  var prefixLen = 0
  for pfx in l.stringPrefixes:
    if pfx.len > prefixLen and l.matchesAt(l.pos, pfx) and
        l.charAt(l.pos + pfx.len) in {'"', '\''}:
      prefixLen = pfx.len
  if prefixLen == 0:
    return nil

  # A prefix ending in `R` (`R`, `u8R`, `LR`) may open a delimited raw string.
  let isRaw = l.rawStringDelims and
    l.charAt(l.pos + prefixLen - 1) in {'R', 'r'} and
    l.charAt(l.pos + prefixLen) == '"'
  for i in 0 ..< prefixLen:
    discard l.advance()
  if isRaw:
    return l.scanDelimitedRawString(startPos, startLine, startCol, prefixLen)
  l.scanQuotedString(startPos, startLine, startCol)

proc scanPercentLiteral(l: var SweetLexer, startPos, startLine, startCol: int): Token =
  ## Scan a Ruby percent literal: `%w[..]`, `%W{..}`, `%i[..]`, `%I{..}`,
  ## `%q(..)`, `%Q[..]` or a bare `%(..)`. The `W`, `Q` and `I` variants
  ## interpolate. Returns nil when the text is the `%` operator instead
  ## (e.g. `a % b`), so the caller falls back to operator scanning.
  # Caller guarantees current == '%'. Everything is peeked first so a
  # rejected candidate leaves the lexer untouched.
  let kind = l.charAt(l.pos + 1)
  if kind notin {'w', 'W', 'i', 'I', 'q', 'Q'}:
    return nil # bare %(..) has no kind character
  let open = l.charAt(l.pos + 2)
  # The delimiter must be punctuation, which is what separates it from an
  # identifier: `a % i` is modulo by `i`, not a `%i` literal.
  if open == '\0' or open.isAlphaNumeric or open == '_' or
      open in {' ', '\t', '\r', '\n'}:
    return nil
  let closer =
    case open
    of '(': ')'
    of '[': ']'
    of '{': '}'
    of '<': '>'
    else: open
  discard l.advance() # consume '%'
  discard l.advance() # consume the kind letter
  discard l.advance() # consume the opening delimiter
  # Paired delimiters nest; any other delimiter closes on itself.
  let nesting = closer != open
  var depth = 1
  while l.current != '\0':
    if l.current == '\\':
      discard l.advance()
      if l.current != '\0': discard l.advance()
      continue
    if nesting and l.current == open:
      inc depth
    elif l.current == closer:
      dec depth
      if depth == 0:
        discard l.advance() # consume the closing delimiter
        result = l.makeRange(tkString, startPos, startLine, startCol)
        result.attr.addAttrOnce("percent_literal")
        if kind in {'W', 'Q', 'I'}:
          result.attr.addAttrOnce("interpolating")
        return
    discard l.advance()
  result = l.makeRange(tkString, startPos, startLine, startCol) # unterminated
  result.attr.addAttrOnce("percent_literal")

proc regexAllowed(l: var SweetLexer): bool =
  ## Whether a `/` at the current position may open a regex literal,
  ## inferred from the previous significant token using the spec's
  ## `expect_regex_after` lists. This mirrors what `GenericParser.walk`
  ## decides with the same lists, so lexer-only consumers (e.g.
  ## `highlight`) agree with the parser.
  ## At the very start of input a `/` can only be a regex.
  if l.lastTokValue.len == 0:
    return true
  if l.lastTokValue in l.expectRegexTokens:
    return true
  if l.lastTokKind == tkIdentifier and l.lastTokValue in l.expectRegexKeywords:
    return true
  false

proc scanLongBracketString(l: var SweetLexer, startPos, startLine, startCol: int): Token =
  ## Scan a Lua long bracket string: `[[ ... ]]`, `[=[ ... ]=]`,
  ## `[==[ ... ]==]`. Called with `l.current == '['`; returns nil when the
  ## text is an ordinary bracket (table access or a nested `[`), so the
  ## caller falls back to delimiter scanning. The opening bracket, the run of
  ## `=` and the second `[` are consumed, then the body runs to the matching
  ## `]` + the same number of `=` + `]`, so a `]` or `]=` inside the body is
  ## literal. A newline immediately after the opener is skipped, per Lua.
  ## Only reached when the spec sets `long_brackets: true` (Lua), so a `[`
  ## in other languages keeps its current meaning.
  var eqCount = 0
  while l.charAt(l.pos + 1 + eqCount) == '=': inc eqCount
  if l.charAt(l.pos + 1 + eqCount) != '[':
    return nil # plain index / table access
  for _ in 0 .. eqCount + 1:
    discard l.advance()
  # Lua drops a newline directly after the opening bracket.
  if l.current == '\r':
    discard l.advance()
    if l.current == '\n': discard l.advance()
  elif l.current == '\n':
    discard l.advance()
    if l.current == '\r': discard l.advance()
  while l.current != '\0':
    if l.current == ']':
      var seen = 0
      while seen < eqCount and l.charAt(l.pos + 1 + seen) == '=': inc seen
      if seen == eqCount and l.charAt(l.pos + 1 + eqCount) == ']':
        for _ in 0 .. eqCount + 1:
          discard l.advance()
        return l.makeRange(tkString, startPos, startLine, startCol)
    discard l.advance()
  l.makeRange(tkString, startPos, startLine, startCol) # unterminated, but safe

proc lexToken(l: var SweetLexer): Token =
  ## Scan one token. See `getToken`, which wraps this to remember the last
  ## significant token so the regex heuristic can look at it.
  if l.enableFilters: l.prepareFilters() # Ensure filters are prepared if enabled
  l.skipWhitespace()

  let startPos = l.pos
  let startLine = l.line
  let startCol = l.col


  # Skip open tags (e.g. `<?php`) — transparently consumed
  if l.openTag.isSome and l.current == l.openTag.get[0]:
    let tag = l.openTag.get
    var matches = true
    for i in 0 ..< tag.len:
      if l.charAt(l.pos + i) != tag[i]: matches = false; break
    if matches:
      for i in 0 ..< tag.len: discard l.advance()
      l.skipWhitespace()
      return l.lexToken() # recurse — parser only sees the real tokens

  # Close tags (e.g. `?>`) — skip any raw content until the next open tag
  # (or EOF) and resume lexing, enabling multi-block files such as
  # `<?php ... ?> <html> <?php ... ?>`.
  if l.closeTag.isSome and l.current == l.closeTag.get[0]:
    let tag = l.closeTag.get
    var matches = true
    for i in 0 ..< tag.len:
      if l.charAt(l.pos + i) != tag[i]: matches = false; break
    if matches:
      for i in 0 ..< tag.len: discard l.advance()
      if l.openTag.isSome:
        let open = l.openTag.get
        while l.current != '\0':
          if l.current == open[0]:
            var openMatches = true
            for i in 0 ..< open.len:
              if l.charAt(l.pos + i) != open[i]: openMatches = false; break
            if openMatches:
              for i in 0 ..< open.len: discard l.advance()
              l.skipWhitespace()
              result = l.lexToken() # resume lexing after the open tag
              l.tagTerminated = true
              return
          discard l.advance()
      l.tagTerminated = true
      return Token(kind: tkEOF, line: startLine, col: startCol,
                   pos: startPos, start: startPos, stop: startPos)

  if l.current == '\0':
    return Token(kind: tkEOF, line: startLine, col: startCol, pos: startPos, start: startPos, stop: startPos)

  # Prefixed string literals (C++ `u8"x"`, `L'c'`, `R"tag(...)tag"`, C#
  # `@"verbatim"`) must be tested before the plain identifier scan, because the
  # prefix is glued to the quote and would otherwise be read as an identifier
  # (or, for `@`, as punctuation). A prefix need not start like an identifier:
  # C#'s `@` is punctuation, so a prefix's own first character also arms this
  # check.
  if l.stringPrefixes.len > 0:
    var mayBePrefix = isIdentStart(l.current)
    if not mayBePrefix:
      for pfx in l.stringPrefixes:
        if pfx.len > 0 and pfx[0] == l.current:
          mayBePrefix = true
          break
    if mayBePrefix:
      let prefixed = l.scanStringPrefix(startPos, startLine, startCol)
      if prefixed != nil:
        return prefixed

  if isIdentStart(l.current) or ord(l.current) >= 0x80:
    if ord(l.current) >= 0x80:
      discard l.advanceUtf8Char()
    else:
      discard l.advance()
    while true:
      if isIdentPart(l.current):
        discard l.advance()
      elif l.trailingBangQuestion and l.current in {'?', '!'}:
        discard l.advance()
      elif ord(l.current) >= 0x80:
        discard l.advanceUtf8Char()
      else:
        break
    return l.makeRange(tkIdentifier, startPos, startLine, startCol)

  # numbers
  if l.current.isDigit() or (l.current == '.' and l.peek().isDigit()):
    let startPos = l.pos
    let startLine = l.line
    let startCol = l.col

    if l.current == '0':
      discard l.advance()
      case l.current
      of 'x', 'X':
        discard l.advance()
        var hexIntDigits = 0
        while l.current in {'0'..'9', 'a'..'f', 'A'..'F', '_'}:
          if l.current != '_': inc hexIntDigits
          discard l.advance()
        if l.extendedNumbers:
          # Hex float `0x1p-2`, `0x1.8p3`, `0x.8p1` (Go; the `p`
          # exponent is mandatory — without it `0x1.8` splits into
          # `0x1` + `.8`, an error downstream just like gc).
          var expOff = -1
          var fracDigits = 0
          if l.current == '.' and l.peek() != '.':
            var k = 1
            if l.peek(k) in {'0'..'9', 'a'..'f', 'A'..'F'}:
              while l.peek(k) in {'0'..'9', 'a'..'f', 'A'..'F', '_'}:
                if l.peek(k) != '_': inc fracDigits
                inc k
            if l.peek(k) in {'p', 'P'}:
              expOff = k
          elif l.current in {'p', 'P'}:
            expOff = 0
          if expOff >= 0:
            var k = expOff + 1
            if l.peek(k) in {'+', '-'}: inc k
            var expDigits = 0
            while l.peek(k) in {'0'..'9', '_'}:
              if l.peek(k) != '_': inc expDigits
              inc k
            if expDigits > 0 and (hexIntDigits > 0 or fracDigits > 0):
              if l.current == '.':
                discard l.advance()
                while l.current in {'0'..'9', 'a'..'f', 'A'..'F', '_'}:
                  discard l.advance()
              discard l.advance() # `p`/`P`
              if l.current in {'+', '-'}:
                discard l.advance()
              while l.current.isDigit() or l.current == '_':
                discard l.advance()
              if l.current == 'i' and not l.peek().isIdentPart():
                discard l.advance()
                return l.makeRange(tkImag, startPos, startLine, startCol)
              return l.makeRange(tkFloat, startPos, startLine, startCol)
        let isBigInt = l.current == 'n'
        if isBigInt: discard l.advance()
        # Nim type suffix like 0xFF'u8 (mirrors the decimal branch below)
        if l.current == '\'':
          discard l.advance()
          while l.current.isIdentPart():
            discard l.advance()
        l.consumeIntSuffix()
        if not isBigInt and l.extendedNumbers and l.current == 'i' and
           not l.peek().isIdentPart():
          # Imaginary `0xFFi`
          discard l.advance()
          return l.makeRange(tkImag, startPos, startLine, startCol)
        return l.makeRange(
          if isBigInt: tkBigInt else: tkHex,
          startPos, startLine, startCol)
      of 'o', 'O':
        discard l.advance()
        while l.current in {'0'..'7', '_'}:
          discard l.advance()
        let isBigInt = l.current == 'n'
        if isBigInt: discard l.advance()
        # Nim type suffix like 0o17'u8 (mirrors the decimal branch below)
        if l.current == '\'':
          discard l.advance()
          while l.current.isIdentPart():
            discard l.advance()
        l.consumeIntSuffix()
        if not isBigInt and l.extendedNumbers and l.current == 'i' and
           not l.peek().isIdentPart():
          # Imaginary `0o17i`
          discard l.advance()
          return l.makeRange(tkImag, startPos, startLine, startCol)
        return l.makeRange(
          if isBigInt: tkBigInt else: tkOctal,
          startPos, startLine, startCol)
      of 'b', 'B':
        discard l.advance()
        while l.current in {'0', '1', '_'}:
          discard l.advance()
        let isBigInt = l.current == 'n'
        if isBigInt: discard l.advance()
        # Nim type suffix like 0b1010'u8 (mirrors the decimal branch below)
        if l.current == '\'':
          discard l.advance()
          while l.current.isIdentPart():
            discard l.advance()
        l.consumeIntSuffix()
        if not isBigInt and l.extendedNumbers and l.current == 'i' and
           not l.peek().isIdentPart():
          # Imaginary `0b101i`
          discard l.advance()
          return l.makeRange(tkImag, startPos, startLine, startCol)
        return l.makeRange(
          if isBigInt: tkBigInt else: tkBinary,
          startPos, startLine, startCol)
      else:
        # Legacy octal `0755` (Go; flag-gated): `0` followed by octal
        # digits — including `0_755`. `0.5`/`0e1`/`0i` are not digits
        # and stay on the decimal path; `09` finds no octal digit and
        # also stays decimal (lenient, as before).
        if l.extendedNumbers and l.current in {'0'..'9', '_'}:
          var k = 0
          var octDigits = 0
          while l.peek(k) in {'0'..'7', '_'}:
            if l.peek(k) != '_': inc octDigits
            inc k
          if octDigits > 0:
            while l.current in {'0'..'7', '_'}:
              discard l.advance()
            if l.current == 'i' and not l.peek().isIdentPart():
              discard l.advance()
              return l.makeRange(tkImag, startPos, startLine, startCol)
            return l.makeRange(tkOctal, startPos, startLine, startCol)
        discard # fall through to decimal scanning

    # decimal integer or float
    while l.current.isDigit() or l.current == '_':
      discard l.advance()

    var isFloat = false
    # fractional part
    if l.current == '.' and l.peek().isDigit():
      isFloat = true
      discard l.advance() # consume '.'
      while l.current.isDigit() or l.current == '_':
        discard l.advance()
    elif l.extendedNumbers and l.current == '.' and l.peek() != '.':
      # `1.` / `1.e10` (Go; `1.e` errors downstream as juxtaposition,
      # same as gc — and `1..2` keeps its dots for other uses).
      isFloat = true
      discard l.advance() # consume '.'
      while l.current.isDigit() or l.current == '_':
        discard l.advance()

    # exponent
    if l.current in {'e', 'E'}:
      isFloat = true
      discard l.advance() # consume 'e'/'E'
      if l.current in {'+', '-'}:
        discard l.advance()
      var expDigits = 0
      while l.current.isDigit():
        discard l.advance()
        inc expDigits
      if l.extendedNumbers and expDigits > 0:
        # Underscores between exponent digits (`1e1_0`).
        while l.current == '_' and l.peek().isDigit():
          discard l.advance()
          while l.current.isDigit():
            discard l.advance()

    # Imaginary suffix `1i`, `1.5i`, `1e10i`
    if l.extendedNumbers and l.current == 'i' and
       not l.peek().isIdentPart():
      discard l.advance()
      return l.makeRange(tkImag, startPos, startLine, startCol)

    # BigInt suffix
    if l.current == 'n':
      discard l.advance()

    # Nim type suffix like 0'i32, 1'u64, etc.
    if l.current == '\'':
      discard l.advance()
      while l.current.isIdentPart():
        discard l.advance()

    # C integer suffix (`1U`, `100ULL`) and float suffix (`1.5f`).
    l.consumeIntSuffix()
    if isFloat:
      l.consumeFloatSuffix()

    return l.makeRange(
      if isFloat: tkFloat else: tkInt,
      startPos, startLine, startCol)

  if l.current == '"' or l.current == '\'':
    return l.scanQuotedString(startPos, startLine, startCol)

  # Check for block comments FIRST (before inline comments and operators)
  if l.blockComment[0].len > 0 and l.current == l.blockComment[0][0]:
    let commentStart = l.pos
    let startSyntax = l.blockComment[0]
    let endSyntax = l.blockComment[1]
    var matchesStart = true
    for i in 0 ..< startSyntax.len:
      if l.charAt(l.pos + i) != startSyntax[i]:
        matchesStart = false
        break
    if matchesStart:
      # Check if this is a doc comment (`/**`, `/*!`, `(**`, `(*!`)
      let isDocComment = (startSyntax == "/*" or startSyntax == "(*") and
        (l.peek(2) == '*' or l.peek(2) == '!')
      
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

  # Check for inline comments
  if l.inlineComment.isSome():
    let commentSyntax = l.inlineComment.get()
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

  # Hash comments (e.g. PHP): '#' to end of line, unless followed by '[' which
  # starts a PHP 8 attribute.
  if l.hashComments and l.current == '#' and l.peek() != '[':
    let commentStart = l.pos
    while l.current != '\0' and l.current != '\n':
      discard l.advance()
    return l.makeRange(tkComment, commentStart, startLine, startCol)

  # Backtick-quoted identifiers (Nim), template literals (JS),
  # or raw string literals (Go).
  if l.current == '`':
    if l.rawStrings:
      # Go raw string: any character except backquote, including newlines;
      # backslashes have no special meaning, `\r` is discarded from the
      # value (per spec) but kept in the token slice for positions.
      discard l.advance() # consume opening '`'
      while l.current != '\0' and l.current != '`':
        discard l.advance()
      if l.current == '`':
        discard l.advance() # consume closing '`'
      return l.makeRange(tkString, startPos, startLine, startCol)
    # Check if this is a template literal language
    let isTemplateLit = featTemplateLit in l.features
    if isTemplateLit:
      discard l.advance() # consume opening '`'
      while l.current != '\0':
        if l.current == '\\':
          discard l.advance() # consume '\'
          if l.current != '\0': discard l.advance() # consume escaped char
        elif l.current == '`':
          discard l.advance() # consume closing '`'
          break
        elif l.current == '$' and l.peek() == '{':
          discard l.advance() # '$'
          discard l.advance() # '{'
          var depth = 1
          while l.current != '\0' and depth > 0:
            if l.current == '{': inc depth
            elif l.current == '}': dec depth
            discard l.advance()
        else:
          discard l.advance()
      return l.makeRange(tkString, startPos, startLine, startCol)
    else:
      # Nim backtick-quoted identifier: `+`, `<-`, etc.
      discard l.advance() # consume opening '`'
      while l.current != '\0' and l.current != '`':
        discard l.advance()
      if l.current == '`':
        discard l.advance() # consume closing '`'
      return l.makeRange(tkIdentifier, startPos, startLine, startCol)

  # Lua long bracket strings (`[[ ... ]]`, `[==[ ... ]==]`). Checked after
  # comments so `--[[ ... ]]` is a comment, and before punctuation so the
  # opener is not read as two `[` delimiters.
  if l.longBrackets and l.current == '[':
    let long = l.scanLongBracketString(startPos, startLine, startCol)
    if long != nil:
      return long

  # Check for punctuation
  if isDelimiterPunct(l.current):
    # Some languages define multi-char delimiters in their symbols table
    # (e.g. PHP's "::" scope resolution). Greedily match the longest known op.
    var bestOp = ""
    for op in l.allOps:
      if op.len > 1 and op[0] == l.current and op.len > bestOp.len:
        var matches = true
        for i in 0 ..< op.len:
          if l.charAt(l.pos + i) != op[i]: matches = false; break
        if matches:
          bestOp = op
    if bestOp.len > 0:
      for i in 0 ..< bestOp.len:
        discard l.advance()
      return l.makeRange(tkPunct, startPos, startLine, startCol)
    discard l.advance()
    return l.makeRange(tkPunct, startPos, startLine, startCol)

  if isOperatorPunct(l.current):
    if l.heredocs and l.current == '<' and l.peek() == '<':
      # Ruby/PHP heredoc (`<<EOS`, `<<~EOS`, `<<<EOT`, ...). Falls back
      # to normal operator scanning when it is not a heredoc.
      let hd = l.scanHeredoc(startPos, startLine, startCol)
      if hd != nil:
        return hd
    if l.percentLiterals and l.current == '%':
      # Ruby percent literals (`%w[a b]`, `%i[..]`, `%q(..)`, `%Q{..}`).
      # Falls back to the `%` operator (modulo) when it is not one.
      let pl = l.scanPercentLiteral(startPos, startLine, startCol)
      if pl != nil:
        return pl
    if l.current == '/':
      # Treat as a regex when the parser explicitly signals it, or — with no
      # parser running (`inferRegex`) — when the previous significant token
      # says a regex may appear here. Otherwise this is division.
      if l.expectRegex or (l.inferRegex and l.regexAllowed()):
        l.expectRegex = false  # consume the hint
        discard l.advance() # consume opening '/'
        var inCharClass = false
        while l.current != '\0':
          if l.current == '\\':
            discard l.advance()
            if l.current != '\0': discard l.advance()
          elif l.current == '[' and not inCharClass:
            inCharClass = true
            discard l.advance()
          elif l.current == ']' and inCharClass:
            inCharClass = false
            discard l.advance()
          elif l.current == '/' and not inCharClass:
            discard l.advance()
            # JS flags (g,i,m,s,u,v,y,d) and Ruby flags (i,m,x,o)
            while l.current in {'g', 'i', 'm', 's', 'u', 'v', 'y', 'd', 'x', 'o'}:
              discard l.advance()
            break
          elif l.current in {'\n', '\r'}:
            break
          else:
            discard l.advance()
        return l.makeRange(tkRegex, startPos, startLine, startCol)
      # else: fall through to normal operator scanning below

    # Normal operator scanning (handles /=, /, >=, etc.)
    var opAccum = newStringOfCap(8)
    while isOperatorPunct(l.current):
      let nextCh = l.current
      # First character is always consumed; subsequent chars checked against known operators
      if opAccum.len > 0:
        let candidate = opAccum & nextCh
        var found = false
        for tok in l.allOps:
          if tok.startsWith(candidate):
            found = true
            break
        if not found and candidate != "=>":
          break
      opAccum.add(nextCh)
      discard l.advance()
    return l.makeRange(tkPunct, startPos, startLine, startCol)

proc getToken*(l: var SweetLexer): Token =
  ## Retrieve the next token from the input stream, advancing the lexer's position.
  ## Remembers the last significant token so `regexAllowed` can decide, without a
  ## parser, whether a `/` opens a regex literal or is division.
  result = l.lexToken()
  if result.kind notin {tkEOF, tkComment, tkDocComment}:
    l.lastTokKind = result.kind
    l.lastTokValue = l.getLexeme(result.start, result.stop)

proc buildAllOps(l: var SweetLexer, spec: SweetSpec) =
  ## Collect the operator/delimiter lexemes the scanners may greedily match.
  ## The spec's `symbols` table is always the base: it is the language's
  ## punctuation vocabulary and is what the operator and delimiter scanners
  ## need in order to emit multi-character operators (`==`, `->`, `::`).
  ## `operators:` only *adds* the tokens a Pratt parser uses but which are not
  ## symbols. Highlight-only specs have no `operators:` block, so gating the
  ## symbol vocabulary on it would leave those languages unable to lex any
  ## multi-character operator. Mirrors `buildPrepared`.
  l.allOps = @[]
  for k in spec.symbols.keys: l.allOps.add(k)
  if spec.operators == nil: return
  for g in spec.operators.prefix:
    for tok in g.tokens: l.allOps.add(tok)
  for g in spec.operators.infix:
    for tok in g.tokens: l.allOps.add(tok)
    for kw in g.keywords: l.allOps.add(kw)
  if spec.operators.assignment != nil:
    for tok in spec.operators.assignment.tokens: l.allOps.add(tok)
  if spec.operators.ternary != nil:
    l.allOps.add(spec.operators.ternary.token)

proc buildRegexHints(l: var SweetLexer, spec: SweetSpec) =
  ## Seed the parser-free `/regex/` heuristic from the spec's
  ## `expect_regex_after` list. `GenericParser` decides the same thing from
  ## the same lists while parsing, so lexer-only consumers that set
  ## `inferRegex` (e.g. `highlight`) reach the same verdict.
  if not spec.statements.hasKey("expect_regex_after"):
    return
  let era = spec.statements["expect_regex_after"]
  l.expectRegexTokens = era.tokens.toHashSet()
  l.expectRegexKeywords = era.keywords.toHashSet()

proc buildKeywordScopes(l: var SweetLexer, spec: SweetSpec) =
  ## Invert `spec.keyword_scopes` (scope -> lexemes) into the lexeme -> scope
  ## table the renderers look up. A spec that declares no scopes leaves this
  ## empty, and every identifier then renders as a plain `keyword`.
  l.keywordScopes = initTable[string, string](spec.keywordScopes.len)
  for scope, lexemes in spec.keyword_scopes.pairs:
    for lexeme in lexemes:
      l.keywordScopes[lexeme] = scope

proc initLexerFromFile*(spec: SweetSpec, path: string, enableFilters: bool = false): SweetLexer =
  ## Initialize lexer from a file using memfiles for efficient access.
  ## This overload accepts a SweetSpec and extracts lexer data from it.
  result = SweetLexer(
    input: path,
    mf: memfiles.open(path, fmRead),
    data: nil,
    len: 0,
    line: 1,
    col: 1,
    pos: 0,
    symbols: spec.symbols,
    identifiers: spec.identifiers,
    keywordScopes: initTable[string, string](),
    inlineComment: spec.inline_comment,
    blockComment: spec.block_comment,
    hashComments: spec.hash_comments,
    trailingBangQuestion: spec.trailing_bang_question,
    rawStrings: spec.raw_strings,
    extendedNumbers: spec.extended_numbers,
    intSuffixes: spec.int_suffixes,
    heredocs: spec.heredocs,
    stringPrefixes: spec.string_prefixes,
    rawStringDelims: spec.raw_string_delims,
    percentLiterals: spec.percent_literals,
    filtersSkipLiterals: spec.filters_skip_literals,
    longBrackets: spec.long_brackets,
    heredocOpenerPunctuation: spec.heredoc_opener_punctuation,
    openTag: spec.open_tag,
    closeTag: spec.close_tag,
    filters: spec.filters,
    enableFilters: enableFilters,
    usingMemFile: true,
    filtersReady: false,
    filterHits: @[],
    filterScanIdx: 0
  )
  if spec.features != nil:
    if spec.features.regexLiterals: result.features.incl(featRegex)
    if spec.features.asyncAwait: result.features.incl(featAsync)
    if spec.features.generators: result.features.incl(featGenerators)
    if spec.features.arrowFunctions: result.features.incl(featArrowFn)
    if spec.features.templateLiterals: result.features.incl(featTemplateLit)
    if spec.features.labeledStatements: result.features.incl(featLabeledStmt)
    if spec.features.commandSyntax: result.features.incl(featCommandSyntax)
  result.buildAllOps(spec)
  result.buildRegexHints(spec)
  result.buildKeywordScopes(spec)
  result.data = cast[ptr UncheckedArray[char]](result.mf.mem)
  result.len = result.mf.size
  result.current = result.charAt(0)

proc initLexerFromFile*(pre: SweetLexerInit, path: string, enableFilters: bool = false): SweetLexer =
  ## Initialize lexer from a file using memfiles for efficient access.
  result = SweetLexer(
    input: path,
    mf: memfiles.open(path, fmRead),
    data: nil,
    len: 0,
    line: 1,
    col: 1,
    pos: 0,
    symbols: pre.symbols,
    identifiers: pre.identifiers,
    keywordScopes: pre.keywordScopes,
    inlineComment: pre.inlineComment,
    blockComment: pre.blockComment,
    hashComments: pre.hashComments,
    trailingBangQuestion: pre.trailingBangQuestion,
    rawStrings: pre.rawStrings,
    extendedNumbers: pre.extendedNumbers,
    intSuffixes: pre.intSuffixes,
    heredocs: pre.heredocs,
    stringPrefixes: pre.stringPrefixes,
    rawStringDelims: pre.rawStringDelims,
    percentLiterals: pre.percentLiterals,
    filtersSkipLiterals: pre.filtersSkipLiterals,
    longBrackets: pre.longBrackets,
    heredocOpenerPunctuation: pre.heredocOpenerPunctuation,
    inferRegex: pre.inferRegex,
    openTag: pre.openTag,
    closeTag: pre.closeTag,
    features: pre.features,
    allOps: pre.allOps,
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
  ## Initialize lexer from raw source text (SweetSpec-based, backward compat).
  result = SweetLexer(
    input: input,
    data: nil,
    len: input.len,
    line: 1,
    col: 1,
    pos: 0,
    current: '\0',
    symbols: spec.symbols,
    identifiers: spec.identifiers,
    keywordScopes: initTable[string, string](),
    inlineComment: spec.inline_comment,
    blockComment: spec.block_comment,
    hashComments: spec.hash_comments,
    trailingBangQuestion: spec.trailing_bang_question,
    rawStrings: spec.raw_strings,
    extendedNumbers: spec.extended_numbers,
    intSuffixes: spec.int_suffixes,
    heredocs: spec.heredocs,
    stringPrefixes: spec.string_prefixes,
    rawStringDelims: spec.raw_string_delims,
    percentLiterals: spec.percent_literals,
    filtersSkipLiterals: spec.filters_skip_literals,
    longBrackets: spec.long_brackets,
    heredocOpenerPunctuation: spec.heredoc_opener_punctuation,
    openTag: spec.open_tag,
    closeTag: spec.close_tag,
    filters: spec.filters,
    enableFilters: enableFilters,
    filtersReady: false,
    filterHits: @[],
    filterScanIdx: 0
  )
  if spec.features != nil:
    if spec.features.regexLiterals: result.features.incl(featRegex)
    if spec.features.asyncAwait: result.features.incl(featAsync)
    if spec.features.generators: result.features.incl(featGenerators)
    if spec.features.arrowFunctions: result.features.incl(featArrowFn)
    if spec.features.templateLiterals: result.features.incl(featTemplateLit)
    if spec.features.labeledStatements: result.features.incl(featLabeledStmt)
    if spec.features.commandSyntax: result.features.incl(featCommandSyntax)
  result.buildAllOps(spec)
  result.buildRegexHints(spec)
  result.buildKeywordScopes(spec)
  if result.len > 0:
    result.current = result.charAt(0)

proc initLexer*(pre: SweetLexerInit, input: sink string, enableFilters: bool = false): SweetLexer =
  ## Initialize lexer from raw source text, this is efficient for small inputs
  result = SweetLexer(
    input: input,
    data: nil,
    len: input.len,
    line: 1,
    col: 1,
    pos: 0,
    current: '\0',
    symbols: pre.symbols,
    identifiers: pre.identifiers,
    keywordScopes: pre.keywordScopes,
    inlineComment: pre.inlineComment,
    blockComment: pre.blockComment,
    hashComments: pre.hashComments,
    trailingBangQuestion: pre.trailingBangQuestion,
    rawStrings: pre.rawStrings,
    extendedNumbers: pre.extendedNumbers,
    intSuffixes: pre.intSuffixes,
    heredocs: pre.heredocs,
    stringPrefixes: pre.stringPrefixes,
    rawStringDelims: pre.rawStringDelims,
    percentLiterals: pre.percentLiterals,
    filtersSkipLiterals: pre.filtersSkipLiterals,
    longBrackets: pre.longBrackets,
    heredocOpenerPunctuation: pre.heredocOpenerPunctuation,
    inferRegex: pre.inferRegex,
    openTag: pre.openTag,
    closeTag: pre.closeTag,
    features: pre.features,
    allOps: pre.allOps,
    enableFilters: enableFilters,
    filtersReady: false,
    filterHits: @[],
    filterScanIdx: 0
  )
  if result.len > 0:
    result.current = result.charAt(0)

proc initLexerFromMemFile*(spec: SweetSpec, mf: MemFile, path: string = "", enableFilters: bool = false): SweetLexer =
  ## Initialize lexer from an already-opened MemFile (e.g. from Flysystem's
  ## `readStream`). Zero-copy: the returned lexer borrows `mf.mem`.
  if mf.size == 0 or mf.mem.isNil:
    var empty = ""
    result = initLexer(spec, empty, enableFilters)
    return
  result = SweetLexer(
    input: path,
    mf: mf,
    data: cast[ptr UncheckedArray[char]](mf.mem),
    len: mf.size,
    line: 1, col: 1, pos: 0,
    symbols: spec.symbols,
    identifiers: spec.identifiers,
    keywordScopes: initTable[string, string](),
    inlineComment: spec.inline_comment,
    blockComment: spec.block_comment,
    hashComments: spec.hash_comments,
    trailingBangQuestion: spec.trailing_bang_question,
    rawStrings: spec.raw_strings,
    extendedNumbers: spec.extended_numbers,
    intSuffixes: spec.int_suffixes,
    heredocs: spec.heredocs,
    stringPrefixes: spec.string_prefixes,
    rawStringDelims: spec.raw_string_delims,
    percentLiterals: spec.percent_literals,
    filtersSkipLiterals: spec.filters_skip_literals,
    longBrackets: spec.long_brackets,
    heredocOpenerPunctuation: spec.heredoc_opener_punctuation,
    openTag: spec.open_tag,
    closeTag: spec.close_tag,
    filters: spec.filters,
    enableFilters: enableFilters,
    usingMemFile: true,
    filtersReady: false,
    filterHits: @[],
    filterScanIdx: 0
  )
  if spec.features != nil:
    if spec.features.regexLiterals: result.features.incl(featRegex)
    if spec.features.asyncAwait: result.features.incl(featAsync)
    if spec.features.generators: result.features.incl(featGenerators)
    if spec.features.arrowFunctions: result.features.incl(featArrowFn)
    if spec.features.templateLiterals: result.features.incl(featTemplateLit)
    if spec.features.labeledStatements: result.features.incl(featLabeledStmt)
    if spec.features.commandSyntax: result.features.incl(featCommandSyntax)
  result.buildAllOps(spec)
  result.buildRegexHints(spec)
  result.buildKeywordScopes(spec)
  result.current = result.charAt(0)

proc resetLexer*(l: SweetLexer) =
  ## Rewind the lexer to offset 0 so its token stream can be consumed again.
  ## Used by streaming consumers that need a second pass over the input
  ## (e.g. fold computation that detects its mode only at EOF).
  if l.isNil: return
  l.pos = 0
  l.line = 1
  l.col = 1
  l.filterScanIdx = 0
  l.expectRegex = false
  l.tagTerminated = false
  l.lastTokKind = tkEOF
  l.lastTokValue = ""
  l.current = if l.len > 0: l.charAt(0) else: '\0'

proc closeLexer*(l: var SweetLexer) =
  if l != nil and l.usingMemFile:
    l.mf.close()
  reset(l)
