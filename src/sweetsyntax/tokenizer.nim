# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/tables
import ./config, ./sweetlexer

type
  TokenTuple* = tuple
    ## A tuple representing a token, including its kind, any associated identifier,
    ## the raw value, and its position in the input (line, column, and character index).
    kind: SweetTokenKind
    ident: string
    value: string
    line: int
    col: int
    pos: int

proc getToken*[T](p: var T): TokenTuple {.inline.} =
  ## Retrieve the next token from the input stream, advancing
  ## the lexer's position accordingly.
  let token = p.lexer.getToken()
  let val = p.lexer.getTokenValue(token)

  # Single lookup: symbols for punctuation, identifiers for keywords
  if token.kind == tkPunct:
    let ident = p.lexer.symbols.getOrDefault(val)
    if ident.len > 0:
      return (token.kind, ident, val, token.line, token.col, token.pos)
  else:
    let ident = p.lexer.identifiers.getOrDefault(val)
    if ident.len > 0:
      return (token.kind, ident, val, token.line, token.col, token.pos)

  return (token.kind, "", val, token.line, token.col, token.pos)
