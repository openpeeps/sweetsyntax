# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module provides functionality to render the tokens for terminal output
## using ANSI escape codes for coloring based on token types and attributes.

import ../sweetlexer
import std/strutils

const
  ansiReset = "\e[0m"

proc hasAttr(tok: SweetTokenRange, name: string): bool {.inline.} =
  let want = toLowerAscii(name)
  for a in tok.attr:
    if toLowerAscii(a) == want:
      return true
  false

proc hasAnyAttr(tok: SweetTokenRange, names: openArray[string]): bool {.inline.} =
  for n in names:
    if tok.hasAttr(n):
      return true
  false

proc colorForToken(tok: SweetTokenRange): string =
  ## Prefer semantic attrs, then strong kind fallback.
  if tok.hasAnyAttr(["comment", "doc", "documentation"]): return "\e[90m" # bright black
  if tok.hasAnyAttr(["string", "str", "char"]): return "\e[32m"           # green
  if tok.hasAnyAttr(["keyword", "kw", "control"]): return "\e[35;1m"      # bold magenta
  if tok.hasAnyAttr(["number", "numeric", "int", "float"]): return "\e[36m" # cyan
  if tok.hasAnyAttr(["type", "class", "struct", "interface"]): return "\e[34;1m" # bold blue
  if tok.hasAnyAttr(["function", "func", "method"]): return "\e[33m"      # yellow
  if tok.hasAnyAttr(["operator", "op"]): return "\e[37m"                  # white
  if tok.hasAnyAttr(["punct", "punctuation", "delimiter"]): return "\e[90m"

  let k = toLowerAscii($tok.kind)
  if "comment" in k: return "\e[90m"
  if "string" in k or "char" in k: return "\e[32m"
  if "number" in k or "int" in k or "float" in k: return "\e[36m"
  if "keyword" in k: return "\e[35;1m"
  if "type" in k: return "\e[34;1m"
  if "func" in k or "method" in k: return "\e[33m"
  if "operator" in k: return "\e[37m"
  if "punct" in k or "delim" in k: return "\e[90m"
  if "ident" in k: return "\e[96m"  # bright cyan fallback for identifiers

  return "\e[97m" # default bright white so tokens are visibly styled

proc tokenToAscii*(lexer: SweetLexer, tok: SweetTokenRange, useColor = true): string =
  let lexeme = lexer.getLexeme(tok.start, tok.stop)
  if not useColor:
    return lexeme

  let c = colorForToken(tok)
  if c.len == 0: lexeme else: c & lexeme & ansiReset

proc highlightAscii*(lexer: var SweetLexer, useColor = true): string =
  ## Render full source with ANSI highlighting.
  ## Preserves skipped whitespace/newlines between tokens.
  var prevStop = 0
  var tok = lexer.getToken()
  while tok.kind != tkEOF:
    if tok.start > prevStop:
      result.add lexer.getLexeme(prevStop, tok.start) # whitespace/gaps
    result.add tokenToAscii(lexer, tok, useColor)
    prevStop = tok.stop
    tok = lexer.getToken()
