# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module provides functionality to render the tokens for terminal output
## using ANSI escape codes for coloring based on token types and attributes.

import ../sweetlexer
import ./jsonrenderer
import std/strutils

const
  ansiReset = "\e[0m"

proc colorForToken(lexer: SweetLexer, tok: Token): string =
  ## Derive an ANSI color from the TextMate-style scope. `tok.attr` only
  ## holds keyword lexemes and symbol names, so classification is done via
  ## `scopeForToken`, which knows the language's keyword table.
  let scope = scopeForToken(lexer, tok)
  if scope.startsWith("comment"): return "\e[90m"                          # gray
  if scope.startsWith("keyword.control"): return "\e[35;1m"                # bold magenta
  if scope.startsWith("keyword.operator"): return "\e[37m"                 # white
  if scope.startsWith("storage.type"): return "\e[34;1m"                   # bold blue
  if scope.startsWith("constant.numeric"): return "\e[36m"                 # cyan
  if scope.startsWith("constant.language"): return "\e[36m"                # cyan
  if scope.startsWith("string"): return "\e[32m"                           # green
  if scope.startsWith("keyword"): return "\e[35;1m"                        # bold magenta
  if scope.startsWith("variable.other.property"): return "\e[33m"          # yellow (object fields)
  if scope.startsWith("variable"): return "\e[96m"                         # bright cyan
  if scope.startsWith("punctuation"): return "\e[90m"

  return "\e[97m" # default bright white so tokens are visibly styled

proc tokenToAscii*(lexer: SweetLexer, tok: Token, useColor = true): string =
  let lexeme = lexer.getLexeme(tok.start, tok.stop)
  if not useColor:
    return lexeme

  let c = colorForToken(lexer, tok)
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
