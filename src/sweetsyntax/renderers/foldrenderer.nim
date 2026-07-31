# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module provides tree-sitter style code folding for the renderer family.
##
## Fold regions are derived from the token stream and emitted as line-delimited
## JSON (NDJSON), as a stream separate from the token highlighting stream, so
## editors can subscribe to and handle folds independently.
##
## Folding is fully optional: `computeFolds` is only invoked when a consumer
## requests it, and each fold source can be toggled via the `mode` and
## `preprocessorFolds` parameters.

import std/[algorithm, strutils]
import pkg/openparser/json
import ../sweetlexer

type
  FoldMode* = enum
    fmAuto        ## Brace mode if the file contains any `{` token, else indent mode
    fmBraces      ## Fold brace pairs ({...}) spanning multiple lines
    fmIndent      ## Fold indentation-based blocks (Python)

  FoldKind* = enum
    fkBlock = "block"
    fkComment = "comment"
    fkDocComment = "doc_comment"
    fkPreprocessor = "preprocessor"
    fkIndent = "indent"

  FoldRegion* = object
    ## A foldable region in the source. Positions are 1-based (consistent with
    ## the token JSON renderer) and byte offsets are `start`..`stop` (exclusive).
    kind*: FoldKind
    startLine*, startCol*: int
    endLine*, endCol*: int
    start*, stop*: int

proc collectTokens(lexer: var SweetLexer): seq[Token] =
  var tok = lexer.getToken()
  while tok.kind != tkEOF:
    result.add(tok)
    tok = lexer.getToken()

proc hasBraces(lexer: SweetLexer, tokens: seq[Token]): bool =
  for t in tokens:
    if t.kind == tkPunct and lexer.getTokenValue(t) in ["{", "}"]:
      return true
  false

proc newlinesCount(s: string): int =
  for c in s:
    if c == '\n':
      inc result

proc computeBraceFolds(lexer: SweetLexer, tokens: seq[Token]): seq[FoldRegion] =
  ## Fold brace pairs ({...}) that span multiple lines.
  var stack: seq[Token]
  for t in tokens:
    if t.kind == tkPunct:
      let value = lexer.getTokenValue(t)
      if value == "{":
        stack.add(t)
      elif value == "}" and stack.len > 0:
        let openTok = stack.pop()
        if t.line > openTok.line:
          result.add(FoldRegion(
            kind: fkBlock,
            startLine: openTok.line, startCol: openTok.col,
            endLine: t.line, endCol: t.col,
            start: openTok.start, stop: t.stop))

proc computeCommentFolds(lexer: SweetLexer, tokens: seq[Token]): seq[FoldRegion] =
  ## Fold multi-line block and doc comments.
  for t in tokens:
    if t.kind notin [tkComment, tkDocComment]:
      continue
    let lexeme = lexer.getTokenValue(t)
    let newlines = newlinesCount(lexeme)
    if newlines == 0:
      continue
    let lastNewline = lexeme.rfind('\n')
    result.add(FoldRegion(
      kind: if t.kind == tkDocComment: fkDocComment else: fkComment,
      startLine: t.line, startCol: t.col,
      endLine: t.line + newlines, endCol: lexeme.len - lastNewline,
      start: t.start, stop: t.stop))

proc computePreprocessorFolds(lexer: SweetLexer, tokens: seq[Token]): seq[FoldRegion] =
  ## Fold preprocessor conditionals: #if/#ifdef/#ifndef ... #endif and
  ## #region ... #endregion.
  const
    openers = ["if", "ifdef", "ifndef", "region"]
    closers = ["endif", "endregion"]
  var stack: seq[Token]
  var i = 0
  while i < tokens.len:
    let t = tokens[i]
    if t.kind == tkPunct and lexer.getTokenValue(t) == "#" and i + 1 < tokens.len:
      let kw = tokens[i + 1]
      if kw.kind == tkIdentifier:
        let value = lexer.getTokenValue(kw)
        if value in openers:
          stack.add(t)
        elif value in closers and stack.len > 0:
          let openTok = stack.pop()
          if kw.line > openTok.line:
            result.add(FoldRegion(
              kind: fkPreprocessor,
              startLine: openTok.line, startCol: openTok.col,
              endLine: kw.line, endCol: kw.col,
              start: openTok.start, stop: kw.stop))
    inc i

proc computeIndentFolds(tokens: seq[Token]): seq[FoldRegion] =
  ## Fold indentation-based blocks (Python). A region opens when a line is
  ## indented deeper than the current level, starting at the previous content
  ## line (the `def`/`if` introducer), and closes on dedent or EOF.
  if tokens.len == 0:
    return

  # Per-line info: indent/col/start of the first non-comment token, stop of the
  # last token, and whether the line has any non-comment content.
  type LineInfo = tuple
    line, indent, col, start, stop, lastCol: int
    content: bool

  var lines: seq[LineInfo]
  for t in tokens:
    if lines.len == 0 or lines[^1].line != t.line:
      var info: LineInfo = (line: t.line, indent: -1, col: t.col,
                            start: t.start, stop: t.stop, lastCol: t.col,
                            content: true)
      if t.kind in [tkComment, tkDocComment]:
        info.content = false
      else:
        info.indent = t.col - 1
      lines.add(info)
    else:
      lines[^1].stop = t.stop
      lines[^1].lastCol = t.col
      if not lines[^1].content and t.kind notin [tkComment, tkDocComment]:
        lines[^1].content = true
        lines[^1].indent = t.col - 1
        lines[^1].col = t.col
        lines[^1].start = t.start

  var stack: seq[tuple[indent, line, col, start: int]]
  var baseline = -1
  var prev: tuple[line, col, start, stop: int]

  for info in lines:
    if not info.content:
      continue
    if baseline < 0:
      baseline = info.indent
      prev = (info.line, info.col, info.start, info.stop)
      continue
    # Close regions that dedent below this line
    while stack.len > 0 and info.indent < stack[^1].indent:
      let r = stack.pop()
      result.add(FoldRegion(
        kind: fkIndent,
        startLine: r.line, startCol: r.col,
        endLine: prev.line, endCol: prev.col,
        start: r.start, stop: prev.stop))
    if stack.len == 0:
      if info.indent > baseline:
        stack.add((info.indent, prev.line, prev.col, prev.start))
    elif info.indent > stack[^1].indent:
      stack.add((info.indent, prev.line, prev.col, prev.start))
    prev = (info.line, info.col, info.start, info.stop)

  # Close any remaining regions at EOF
  while stack.len > 0:
    let r = stack.pop()
    result.add(FoldRegion(
      kind: fkIndent,
      startLine: r.line, startCol: r.col,
      endLine: prev.line, endCol: prev.col,
      start: r.start, stop: prev.stop))

proc sortFolds(folds: var seq[FoldRegion]) =
  folds.sort do (a, b: FoldRegion) -> int:
    result = cmp(a.startLine, b.startLine)
    if result == 0:
      result = cmp(a.startCol, b.startCol)
    if result == 0:
      result = cmp(a.start, b.start)

proc computeFolds*(lexer: var SweetLexer,
                   mode: FoldMode = fmAuto,
                   preprocessorFolds = false): seq[FoldRegion] =
  ## Compute fold regions for the given source.
  ##
  ## Folding is optional: callers opt in by calling this proc, and individual
  ## fold sources are controlled by `mode` and `preprocessorFolds`.
  let tokens = collectTokens(lexer)
  if tokens.len == 0:
    return

  let effectiveMode =
    if mode == fmAuto:
      if hasBraces(lexer, tokens): fmBraces else: fmIndent
    else:
      mode

  if effectiveMode == fmBraces:
    result.add computeBraceFolds(lexer, tokens)
  else:
    result.add computeIndentFolds(tokens)

  result.add computeCommentFolds(lexer, tokens)

  if preprocessorFolds:
    result.add computePreprocessorFolds(lexer, tokens)

  result.sortFolds()

proc foldRegionToJson*(region: FoldRegion): JsonNode =
  ## Build a JSON object for a single fold region.
  result = newJObject()
  result["kind"] = newJString($region.kind)
  var start = newJObject()
  start["line"] = %region.startLine
  start["col"] = %region.startCol
  start["offset"] = %region.start
  result["start"] = start
  var stop = newJObject()
  stop["line"] = %region.endLine
  stop["col"] = %region.endCol
  stop["offset"] = %region.stop
  result["end"] = stop

proc foldsToJsonLd*(folds: seq[FoldRegion]): string =
  ## Render fold regions as one line of NDJSON each.
  for region in folds:
    result.add($foldRegionToJson(region) & "\n")
