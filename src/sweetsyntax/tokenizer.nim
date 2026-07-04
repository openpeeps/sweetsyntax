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

proc getToken*[T](p: var T): TokenTuple =
  ## Retrieve the next token from the input stream, advancing
  ## the lexer's position accordingly.
  let token = p.lexer.getToken()
  let val = p.lexer.getTokenValue(token)
  # Check if it's a known symbol
  if token.kind == tkPunct and p.lexer.spec.symbols.hasKey(val):
    return (token.kind, p.lexer.spec.symbols[val], val, token.line, token.col, token.pos)
  
  # Check if it's an identifier
  if p.lexer.spec.identifiers.hasKey(val):
    return (token.kind, p.lexer.spec.identifiers[val], val, token.line, token.col, token.pos)

  # Otherwise, return the raw token information without a known identifier
  return (token.kind, "", val, token.line, token.col, token.pos)
